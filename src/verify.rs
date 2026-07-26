//! The off-chain verifier.
//!
//! A relying party receives several proofs, not one. Each is sound on its own
//! but says nothing about the others, so what makes them describe a single
//! document is a set of equalities between their public values. Those
//! equalities live here, once, rather than in every integration.
//!
//! Two failures this closes are easy to miss when integrating by hand. A
//! bundle whose proofs carry different domains is several documents wearing
//! one identity, and a proof produced by a weaker circuit variant is a
//! downgrade unless the verifier states which verification keys it accepts.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use crate::field::FieldElement;
use crate::layout::{Circuit, PublicInputs};

pub struct Proof {
    pub circuit: Circuit,
    /// The key this proof is checked against. A policy accepts keys by their
    /// bytes rather than by a digest supplied alongside them: a digest and
    /// the key it claims to describe are two independent values, and a
    /// sender who chose both could present an accepted digest next to a key
    /// of their own.
    pub verification_key: Vec<u8>,
    pub bytes: Vec<u8>,
    pub public_inputs: PublicInputs,
}

/// What a bundle actually proved. A verifier that only learns the checks
/// passed does not know which question was answered: the prover chooses the
/// field, the range and the set, and nothing in a circuit ties those to what
/// was asked.
#[derive(Debug, PartialEq, Eq)]
pub enum Statement {
    DataGroup {
        number: u64,
    },
    Compare {
        field_id: u64,
        minimum: u64,
        maximum: u64,
    },
    Member {
        field_id: u64,
        set_root: FieldElement,
    },
    Reveal {
        field_id: u64,
        length: u64,
        value: [FieldElement; 4],
    },
}

/// What a relying party decides in advance: which circuit variants it trusts,
/// which application it is, and the freshness value it issued for this
/// exchange.
pub struct Policy {
    pub accepted_keys: HashMap<Circuit, Vec<Vec<u8>>>,
    pub domain: FieldElement,
    pub context: FieldElement,
    /// Whether the bundle must show the Document Signer belongs to a trusted
    /// set. Left off, a bundle proves only that some key signed the document.
    pub require_trust_anchor: bool,
    /// The registry an anchor proof has to be against, when one is required.
    pub registry_root: Option<FieldElement>,
    /// The window the date a proof resolved against has to fall in.
    ///
    /// That date decides the century of a two digit year, so a prover who
    /// picks it moves a birth date by a hundred years: a holder born in 2010
    /// reads as 1910 and passes an adult check. It also gates certificate
    /// validity in the chain anchor. Left unset, nothing constrains it.
    pub date_window: Option<(u64, u64)>,
}

impl Policy {
    pub fn new(domain: FieldElement, context: FieldElement) -> Self {
        Self {
            accepted_keys: HashMap::new(),
            domain,
            context,
            require_trust_anchor: false,
            registry_root: None,
            date_window: None,
        }
    }

    /// Requires every proof that resolves dates to have used one inside this
    /// inclusive window, as YYYYMMDD. A window rather than a single day so a
    /// bundle proved yesterday, or in another timezone, is still accepted.
    pub fn require_date_within(mut self, earliest: u64, latest: u64) -> Self {
        assert!(earliest <= latest, "an empty date window accepts nothing");

        self.date_window = Some((earliest, latest));

        self
    }

    pub fn require_anchor(mut self, registry_root: FieldElement) -> Self {
        self.require_trust_anchor = true;

        self.registry_root = Some(registry_root);

        self
    }

    pub fn accept(mut self, circuit: Circuit, verification_key: Vec<u8>) -> Self {
        self.accepted_keys
            .entry(circuit)
            .or_default()
            .push(verification_key);

        self
    }
}

#[derive(Debug)]
pub struct Verified {
    pub nullifier: Option<FieldElement>,
    /// The salted signer commitment, when the bundle's document proof exposes
    /// one. A Passive Authentication proof does; a registration proof
    /// deliberately does not, because signer trust is proved inside it, so a
    /// registration bundle returns `None` here.
    pub dsc_commitment: Option<FieldElement>,
    /// Everything the bundle established, in the order the proofs appeared.
    /// A relying party has to read this to know whether the question it asked
    /// is the question that was answered.
    pub statements: Vec<Statement>,
    /// The date the proofs resolved two digit years and certificate validity
    /// against, when any proof carried one.
    pub asserted_date: Option<u64>,
    /// The registry the signer was shown to belong to, when the bundle
    /// carried a trust anchor proof. Without one the bundle establishes that
    /// some key signed the document and nothing about whose key it is, which
    /// is why `require_trust_anchor` exists.
    pub signer_registry_root: Option<FieldElement>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Failure {
    NoSecurityObjectProof,
    MoreThanOneSecurityObjectProof,
    UntrustedVerificationKey { circuit: &'static str },
    ProofRejected { circuit: &'static str },
    WrongDomain { circuit: &'static str },
    WrongContext { circuit: &'static str },
    ContextNotSet,
    DomainNotSet,
    UnlinkedDataGroup { circuit: &'static str },
    UnlinkedCommitment { circuit: &'static str },
    NullifierFromAnotherDocument,
    MoreThanOneNullifierProof,
    NotLinkableToRegistration { circuit: &'static str },
    NotASessionProof { circuit: &'static str },
    NoTrustAnchorProof,
    RegistryRootNotSet,
    DateOutsideWindow { circuit: &'static str },
    InconsistentDates,
    AnchorForAnotherSigner,
    AnchorAgainstAnotherRegistry,
    Malformed(String),
}

impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoSecurityObjectProof => {
                write!(f, "the bundle has neither a Passive Authentication proof nor a registration proof, so nothing establishes the document was signed")
            }
            Self::MoreThanOneSecurityObjectProof => {
                write!(
                    f,
                    "the bundle has more than one proof establishing a document, so it describes more than one"
                )
            }
            Self::UntrustedVerificationKey { circuit } => {
                write!(
                    f,
                    "{circuit} was proved with a verification key this verifier does not accept"
                )
            }
            Self::ProofRejected { circuit } => write!(f, "{circuit} did not verify"),
            Self::WrongDomain { circuit } => {
                write!(f, "{circuit} carries a different application domain")
            }
            Self::WrongContext { circuit } => {
                write!(f, "{circuit} carries a different session context")
            }
            Self::ContextNotSet => write!(f, "the session context is zero"),
            Self::DomainNotSet => write!(
                f,
                "the application domain is zero, which would put every application in one scope"
            ),
            Self::UnlinkedDataGroup { circuit } => {
                write!(
                    f,
                    "{circuit} reads a data group no authenticated Security Object commits to"
                )
            }
            Self::UnlinkedCommitment { circuit } => {
                write!(
                    f,
                    "{circuit} refers to a commitment no attribute proof published"
                )
            }
            Self::NullifierFromAnotherDocument => {
                write!(f, "the nullifier was derived from a different document")
            }
            Self::MoreThanOneNullifierProof => {
                write!(
                    f,
                    "the bundle has more than one nullifier proof, so which value the application stores would be ambiguous"
                )
            }
            Self::NotLinkableToRegistration { circuit } => {
                write!(
                    f,
                    "{circuit} cannot appear beside a registration proof, which does not expose the value it would have to match"
                )
            }
            Self::NotASessionProof { circuit } => {
                write!(
                    f,
                    "a session answers questions about a registered document; {circuit} establishes a document and belongs in registration"
                )
            }
            Self::RegistryRootNotSet => {
                write!(
                    f,
                    "the policy requires a trust anchor without fixing a registry, which would accept an anchor against any registry"
                )
            }
            Self::InconsistentDates => {
                write!(f, "the proofs in this bundle resolved dates against different dates")
            }
            Self::DateOutsideWindow { circuit } => write!(
                f,
                "{circuit} resolved dates against a date this verifier does not accept"
            ),
            Self::NoTrustAnchorProof => write!(
                f,
                "this verifier requires the Document Signer to be shown trusted and the bundle carries no anchor proof"
            ),
            Self::AnchorForAnotherSigner => write!(
                f,
                "the anchor proof is about a different key than the one that signed the document"
            ),
            Self::AnchorAgainstAnotherRegistry => {
                write!(f, "the anchor proof is against a registry this verifier does not use")
            }
            Self::Malformed(reason) => write!(f, "malformed proof bundle: {reason}"),
        }
    }
}

impl std::error::Error for Failure {}

/// Runs the whole checklist. Cryptographic verification comes first, then the
/// equalities, so a bundle that fails here has been rejected for a stated
/// reason rather than passing on the strength of one proof.
pub fn verify_bundle(proofs: &[Proof], policy: &Policy) -> Result<Verified, Failure> {
    if policy.context.is_zero() {
        return Err(Failure::ContextNotSet);
    }

    // A zero domain collapses every application into one scope, so the same
    // holder would carry the same nullifier everywhere. The circuits reject
    // it too; a verifier that never reaches them should not be able to ask.
    if policy.domain.is_zero() {
        return Err(Failure::DomainNotSet);
    }

    // A required anchor without a fixed registry would accept an anchor proof
    // against any registry, including one the prover built and published.
    if policy.require_trust_anchor && policy.registry_root.is_none() {
        return Err(Failure::RegistryRootNotSet);
    }

    let mut document_proofs = Vec::new();

    for proof in proofs {
        admit(proof, policy)?;

        if proof.circuit == Circuit::Sod || proof.circuit == Circuit::Registration {
            document_proofs.push(proof);
        }
    }

    let document = match document_proofs.len() {
        0 => return Err(Failure::NoSecurityObjectProof),
        1 => document_proofs[0],
        _ => return Err(Failure::MoreThanOneSecurityObjectProof),
    };

    let mut statements = Vec::new();

    let mut asserted_date = None;

    let mut commitments = Vec::new();

    let mut signer_registry_root = None;

    let document_secret_binding;

    let dsc_commitment;

    if document.circuit == Circuit::Sod {
        let econtent_binding = document
            .public_inputs
            .sod_econtent_binding()
            .map_err(malformed)?;

        let mut data_group_bindings = Vec::new();

        for proof in proofs.iter().filter(|p| p.circuit == Circuit::DgExtract) {
            let seen = proof
                .public_inputs
                .dg_extract_econtent_binding()
                .map_err(malformed)?;

            if seen != econtent_binding {
                return Err(Failure::UnlinkedDataGroup {
                    circuit: proof.circuit.name(),
                });
            }

            data_group_bindings.push(
                proof
                    .public_inputs
                    .dg_extract_dg_binding()
                    .map_err(malformed)?,
            );
        }

        for proof in proofs.iter().filter(|p| p.circuit == Circuit::DgExtract) {
            let number = proof
                .public_inputs
                .dg_number()
                .map_err(malformed)?
                .to_u64()
                .map_err(malformed)?;

            statements.push(Statement::DataGroup { number });
        }

        for proof in proofs.iter().filter(|p| p.circuit == Circuit::Attributes) {
            let binding = proof
                .public_inputs
                .attributes_dg_binding()
                .map_err(malformed)?;

            if !data_group_bindings.contains(&binding) {
                return Err(Failure::UnlinkedDataGroup {
                    circuit: proof.circuit.name(),
                });
            }

            let date = proof
                .public_inputs
                .attributes_current_date()
                .map_err(malformed)?
                .to_u64()
                .map_err(malformed)?;

            check_date(policy, date, proof.circuit.name())?;

            record_date(&mut asserted_date, date)?;

            commitments.push(
                proof
                    .public_inputs
                    .attributes_commitment()
                    .map_err(malformed)?,
            );
        }

        let sod_dsc_commitment = document
            .public_inputs
            .sod_dsc_commitment()
            .map_err(malformed)?;

        for proof in proofs
            .iter()
            .filter(|p| p.circuit == Circuit::AnchorInclusion || p.circuit == Circuit::AnchorChain)
        {
            if proof
                .public_inputs
                .anchor_dsc_commitment()
                .map_err(malformed)?
                != sod_dsc_commitment
            {
                return Err(Failure::AnchorForAnotherSigner);
            }

            if proof.circuit == Circuit::AnchorChain {
                let date = proof
                    .public_inputs
                    .anchor_current_date()
                    .map_err(malformed)?
                    .to_u64()
                    .map_err(malformed)?;

                check_date(policy, date, proof.circuit.name())?;

                record_date(&mut asserted_date, date)?;
            }

            let root = proof
                .public_inputs
                .anchor_registry_root()
                .map_err(malformed)?;

            if let Some(expected) = policy.registry_root {
                if root != expected {
                    return Err(Failure::AnchorAgainstAnotherRegistry);
                }
            }

            signer_registry_root = Some(root);
        }

        if policy.require_trust_anchor && signer_registry_root.is_none() {
            return Err(Failure::NoTrustAnchorProof);
        }

        document_secret_binding = document
            .public_inputs
            .sod_secret_binding()
            .map_err(malformed)?;

        dsc_commitment = Some(sod_dsc_commitment);
    } else {
        // The registration proof aggregated the extraction, the attributes
        // and the anchor, and it exposes only what downstream proofs link
        // against. A leaf proof of those kinds beside it has nothing to be
        // checked against, so it cannot be accepted silently.
        for proof in proofs {
            match proof.circuit {
                Circuit::DgExtract
                | Circuit::Attributes
                | Circuit::AnchorInclusion
                | Circuit::AnchorChain => {
                    return Err(Failure::NotLinkableToRegistration {
                        circuit: proof.circuit.name(),
                    });
                }
                _ => {}
            }
        }

        let date = document
            .public_inputs
            .registration_current_date()
            .map_err(malformed)?
            .to_u64()
            .map_err(malformed)?;

        check_date(policy, date, document.circuit.name())?;

        record_date(&mut asserted_date, date)?;

        // The registration circuit pins the extraction to data group 1.
        statements.push(Statement::DataGroup { number: 1 });

        commitments.push(
            document
                .public_inputs
                .registration_commitment()
                .map_err(malformed)?,
        );

        let root = document
            .public_inputs
            .registration_registry_root()
            .map_err(malformed)?;

        if let Some(expected) = policy.registry_root {
            if root != expected {
                return Err(Failure::AnchorAgainstAnotherRegistry);
            }
        }

        // Signer trust is proved inside a registration proof, so a policy
        // that requires an anchor is satisfied by construction here.
        signer_registry_root = Some(root);

        document_secret_binding = document
            .public_inputs
            .registration_secret_binding()
            .map_err(malformed)?;

        dsc_commitment = None;
    }

    let nullifier = answer_questions(
        proofs,
        &commitments,
        document_secret_binding,
        &mut statements,
    )?;

    Ok(Verified {
        nullifier,
        dsc_commitment,
        statements,
        asserted_date,
        signer_registry_root,
    })
}

/// The checks every proof passes before the bundle's shape is considered: an
/// accepted verification key, a proof the backend verifies, and the policy's
/// domain and context.
fn admit(proof: &Proof, policy: &Policy) -> Result<(), Failure> {
    let name = proof.circuit.name();

    let accepted = policy
        .accepted_keys
        .get(&proof.circuit)
        .map(|keys| keys.iter().any(|key| key == &proof.verification_key))
        .unwrap_or(false);

    if !accepted {
        return Err(Failure::UntrustedVerificationKey { circuit: name });
    }

    if !verify_one(proof)? {
        return Err(Failure::ProofRejected { circuit: name });
    }

    let domain = proof.public_inputs.domain().map_err(malformed)?;

    if domain != policy.domain {
        return Err(Failure::WrongDomain { circuit: name });
    }

    let context = proof.public_inputs.context().map_err(malformed)?;

    if context != policy.context {
        return Err(Failure::WrongContext { circuit: name });
    }

    Ok(())
}

/// The per session questions. Predicates contribute statements, the nullifier
/// has to hold the secret behind the document's binding, and a second
/// nullifier proof is refused.
fn answer_questions(
    proofs: &[Proof],
    commitments: &[FieldElement],
    document_secret_binding: FieldElement,
    statements: &mut Vec<Statement>,
) -> Result<Option<FieldElement>, Failure> {
    let mut nullifier = None;

    for proof in proofs {
        match proof.circuit {
            Circuit::Compare | Circuit::Member | Circuit::Reveal => {
                let referenced = proof
                    .public_inputs
                    .referenced_commitment()
                    .map_err(malformed)?;

                if !commitments.contains(&referenced) {
                    return Err(Failure::UnlinkedCommitment {
                        circuit: proof.circuit.name(),
                    });
                }

                let field_id = proof
                    .public_inputs
                    .field_id()
                    .map_err(malformed)?
                    .to_u64()
                    .map_err(malformed)?;

                statements.push(match proof.circuit {
                    Circuit::Compare => Statement::Compare {
                        field_id,
                        minimum: proof
                            .public_inputs
                            .at(2)
                            .map_err(malformed)?
                            .to_u64()
                            .map_err(malformed)?,
                        maximum: proof
                            .public_inputs
                            .at(3)
                            .map_err(malformed)?
                            .to_u64()
                            .map_err(malformed)?,
                    },
                    Circuit::Member => Statement::Member {
                        field_id,
                        set_root: proof.public_inputs.at(2).map_err(malformed)?,
                    },
                    _ => {
                        let mut value = [FieldElement([0u8; 32]); 4];

                        for (offset, slot) in value.iter_mut().enumerate() {
                            *slot = proof.public_inputs.at(2 + offset).map_err(malformed)?;
                        }

                        Statement::Reveal {
                            field_id,
                            length: proof
                                .public_inputs
                                .at(6)
                                .map_err(malformed)?
                                .to_u64()
                                .map_err(malformed)?,
                            value,
                        }
                    }
                });
            }
            Circuit::Nullifier => {
                let referenced = proof
                    .public_inputs
                    .referenced_commitment()
                    .map_err(malformed)?;

                if !commitments.contains(&referenced) {
                    return Err(Failure::UnlinkedCommitment {
                        circuit: proof.circuit.name(),
                    });
                }

                let binding = proof
                    .public_inputs
                    .nullifier_secret_binding()
                    .map_err(malformed)?;

                if binding != document_secret_binding {
                    return Err(Failure::NullifierFromAnotherDocument);
                }

                // One domain fixes one policy, and one policy over one
                // document gives one value. A second proof would make which
                // value the application stores an accident of ordering.
                if nullifier.is_some() {
                    return Err(Failure::MoreThanOneNullifierProof);
                }

                nullifier = Some(proof.public_inputs.nullifier_value().map_err(malformed)?);
            }
            _ => {}
        }
    }

    Ok(nullifier)
}

/// What a relying party stores when a registration verifies, and holds every
/// later session against: the commitment the document's fields sit under and
/// the secret binding a nullifier proof has to match. Both are public values
/// of the registration proof, or of the attribute and Passive Authentication
/// proofs in the leaf form.
///
/// The holder keeps its own half: the session salt behind the commitment.
/// Every later opening needs it, so for a registered identity it is not a
/// per session value but a secret the holder retains. A holder who loses it
/// cannot answer questions against this registration and has to register
/// again, which the stored nullifier makes visible to the application.
pub struct Registered {
    pub commitment: FieldElement,
    pub secret_binding: FieldElement,
}

/// Verifies a session bundle against a registration the relying party stored.
///
/// Registration establishes the document once. Afterwards a holder answers
/// questions per session: predicate proofs, and optionally the nullifier,
/// against the commitment that registration exposed. This entry point is
/// that second half. It accepts only question proofs, requires each to link
/// to the stored values, and enforces the accepted keys, the domain and the
/// context exactly as `verify_bundle` does; freshness comes from the
/// context, so a proof replayed from an earlier session is refused.
///
/// Document trust is not re-examined here. It was established when the
/// registration bundle verified, and it is the caller's stored decision, so
/// the anchor and date parts of the policy play no part in a session.
pub fn verify_session(
    proofs: &[Proof],
    policy: &Policy,
    registered: &Registered,
) -> Result<Verified, Failure> {
    if policy.context.is_zero() {
        return Err(Failure::ContextNotSet);
    }

    if policy.domain.is_zero() {
        return Err(Failure::DomainNotSet);
    }

    for proof in proofs {
        match proof.circuit {
            Circuit::Compare | Circuit::Member | Circuit::Reveal | Circuit::Nullifier => {}
            _ => {
                return Err(Failure::NotASessionProof {
                    circuit: proof.circuit.name(),
                });
            }
        }

        admit(proof, policy)?;
    }

    let mut statements = Vec::new();

    let nullifier = answer_questions(
        proofs,
        std::slice::from_ref(&registered.commitment),
        registered.secret_binding,
        &mut statements,
    )?;

    Ok(Verified {
        nullifier,
        dsc_commitment: None,
        statements,
        asserted_date: None,
        signer_registry_root: None,
    })
}

/// Every proof in a bundle has to have resolved dates against the same date.
/// Otherwise a prover could resolve two digit years against one date and
/// certificate validity against another, and `asserted_date` would report
/// whichever the checklist read last.
fn record_date(asserted: &mut Option<u64>, date: u64) -> Result<(), Failure> {
    match *asserted {
        None => {
            *asserted = Some(date);

            Ok(())
        }
        Some(previous) if previous == date => Ok(()),
        Some(_) => Err(Failure::InconsistentDates),
    }
}

/// A date a proof resolved against has to sit inside the window the verifier
/// set, when it set one.
fn check_date(policy: &Policy, date: u64, circuit: &'static str) -> Result<(), Failure> {
    let Some((earliest, latest)) = policy.date_window else {
        return Ok(());
    };

    if date < earliest || date > latest {
        return Err(Failure::DateOutsideWindow { circuit });
    }

    Ok(())
}

fn malformed<E: std::fmt::Display>(error: E) -> Failure {
    Failure::Malformed(error.to_string())
}

/// A scratch directory that removes itself, so a failure part way through
/// verification does not leave a proof and its verification key behind.
struct Scratch {
    path: PathBuf,
}

impl Drop for Scratch {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.path).ok();
    }
}

/// Creates a directory no other caller can be using and no other user can
/// have prepared.
///
/// The name is unpredictable and the directory is created exclusively, so a
/// local attacker cannot win a race by placing a symlink at the path first,
/// which would otherwise redirect the verification key and proof this writes.
/// A name derived from the process id alone would also collide between
/// threads: two concurrent verifications would share the three file names,
/// and one could run `bb` against files the other had just written, which
/// returns a verdict about a proof the caller never submitted.
fn scratch(name: &str) -> Result<Scratch, Failure> {
    let mut random = [0u8; 16];

    let mut urandom = std::fs::File::open("/dev/urandom")
        .map_err(|e| Failure::Malformed(format!("cannot open /dev/urandom: {e}")))?;

    urandom
        .read_exact(&mut random)
        .map_err(|e| Failure::Malformed(format!("cannot read /dev/urandom: {e}")))?;

    let suffix: String = random.iter().map(|byte| format!("{byte:02x}")).collect();

    let path = std::env::temp_dir().join(format!("zkicao-{name}-{suffix}"));

    // The mode is applied as the directory is created. Creating it first and
    // restricting it afterwards leaves a window in which it exists under the
    // process umask, which is usually world readable.
    let mut builder = std::fs::DirBuilder::new();

    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;

        builder.mode(0o700);
    }

    // Not recursive: this has to fail rather than adopt anything that already
    // exists at the path.
    builder
        .create(&path)
        .map_err(|e| Failure::Malformed(format!("cannot create a scratch directory: {e}")))?;

    Ok(Scratch { path })
}

/// Delegates the cryptographic check to Barretenberg, the same prover that
/// produced the proof, rather than reimplementing verification here.
fn verify_one(proof: &Proof) -> Result<bool, Failure> {
    let scratch = scratch("verify")?;

    let vk_path = scratch.path.join("vk");

    let proof_path = scratch.path.join("proof");

    let inputs_path = scratch.path.join("public_inputs");

    write(&vk_path, &proof.verification_key)?;

    write(&proof_path, &proof.bytes)?;

    let mut serialized = Vec::new();

    for index in 0..proof.circuit.public_input_count() {
        let value = proof.public_inputs.at(index).map_err(malformed)?;

        serialized.extend_from_slice(&value.0);
    }

    write(&inputs_path, &serialized)?;

    let status = Command::new("bb")
        .args([
            "verify",
            "-k",
            path_argument(&vk_path)?,
            "-p",
            path_argument(&proof_path)?,
            "-i",
            path_argument(&inputs_path)?,
        ])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map_err(|e| Failure::Malformed(format!("cannot run bb: {e}")))?;

    // A rejected proof and a backend that never reached a verdict are
    // different outcomes. Reporting a crash or a signal as a rejection would
    // be safe but would send an integrator looking at the wrong thing.
    match status.code() {
        Some(0) => Ok(true),
        Some(1) => Ok(false),
        Some(other) => Err(Failure::Malformed(format!("bb exited with status {other}"))),
        None => Err(Failure::Malformed(
            "bb was terminated by a signal".to_string(),
        )),
    }
}

fn path_argument(path: &Path) -> Result<&str, Failure> {
    path.to_str()
        .ok_or_else(|| Failure::Malformed("a scratch path is not valid unicode".to_string()))
}

fn write(path: &Path, bytes: &[u8]) -> Result<(), Failure> {
    let mut file = std::fs::File::create(path).map_err(|e| Failure::Malformed(e.to_string()))?;

    file.write_all(bytes)
        .map_err(|e| Failure::Malformed(e.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scratch_directories_are_unique_and_private() {
        let a = scratch("test").unwrap();

        let b = scratch("test").unwrap();

        assert_ne!(a.path, b.path, "two scratch directories must not collide");

        assert!(a.path.is_dir());

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;

            let mode = std::fs::metadata(&a.path).unwrap().permissions().mode();

            assert_eq!(
                mode & 0o777,
                0o700,
                "a scratch directory must not be readable by others"
            );
        }
    }

    #[test]
    fn a_scratch_directory_removes_itself() {
        let path = {
            let scratch = scratch("test").unwrap();

            std::fs::write(scratch.path.join("proof"), b"secret").unwrap();

            scratch.path.clone()
        };

        assert!(!path.exists(), "a proof must not outlive the verification");
    }

    // Two verifications running at once used to share three file names, so one
    // could run the backend over files the other had just written.
    #[test]
    fn concurrent_scratch_directories_do_not_share_paths() {
        let handles: Vec<_> = (0..8)
            .map(|_| std::thread::spawn(|| scratch("test").unwrap().path.clone()))
            .collect();

        let mut paths: Vec<PathBuf> = handles.into_iter().map(|h| h.join().unwrap()).collect();

        paths.sort();

        let count = paths.len();

        paths.dedup();

        assert_eq!(
            paths.len(),
            count,
            "concurrent scratch directories collided"
        );
    }

    #[test]
    fn a_bundle_without_a_security_object_is_rejected() {
        let policy = Policy::new(FieldElement::from_u64(42), FieldElement::from_u64(7));

        assert_eq!(
            verify_bundle(&[], &policy).unwrap_err(),
            Failure::NoSecurityObjectProof
        );
    }

    #[test]
    fn a_zero_scope_is_rejected_before_anything_else() {
        let no_context = Policy::new(FieldElement::from_u64(42), FieldElement::from_u64(0));

        assert_eq!(
            verify_bundle(&[], &no_context).unwrap_err(),
            Failure::ContextNotSet
        );

        let no_domain = Policy::new(FieldElement::from_u64(0), FieldElement::from_u64(7));

        assert_eq!(
            verify_bundle(&[], &no_domain).unwrap_err(),
            Failure::DomainNotSet
        );
    }

    // The fields of a policy are public, so this state is reachable without
    // going through `require_anchor`. It has to fail rather than accept an
    // anchor against whatever registry the prover chose.
    #[test]
    fn a_required_anchor_without_a_registry_is_a_misconfiguration() {
        let mut policy = Policy::new(FieldElement::from_u64(42), FieldElement::from_u64(7));

        policy.require_trust_anchor = true;

        assert_eq!(
            verify_bundle(&[], &policy).unwrap_err(),
            Failure::RegistryRootNotSet
        );
    }

    #[test]
    fn a_session_rejects_zero_scopes_first() {
        let registered = Registered {
            commitment: FieldElement::from_u64(1),
            secret_binding: FieldElement::from_u64(2),
        };

        let no_context = Policy::new(FieldElement::from_u64(42), FieldElement::from_u64(0));

        assert_eq!(
            verify_session(&[], &no_context, &registered).unwrap_err(),
            Failure::ContextNotSet
        );

        let no_domain = Policy::new(FieldElement::from_u64(0), FieldElement::from_u64(7));

        assert_eq!(
            verify_session(&[], &no_domain, &registered).unwrap_err(),
            Failure::DomainNotSet
        );
    }

    // The shape check comes before any cryptography, so this needs no real
    // proof: a document proof has no business in a session at all.
    #[test]
    fn a_document_proof_is_not_a_session_proof() {
        let registered = Registered {
            commitment: FieldElement::from_u64(1),
            secret_binding: FieldElement::from_u64(2),
        };

        let policy = Policy::new(FieldElement::from_u64(42), FieldElement::from_u64(7));

        let proof = Proof {
            circuit: Circuit::Sod,
            verification_key: Vec::new(),
            bytes: Vec::new(),
            public_inputs: PublicInputs::new(Circuit::Sod, vec![FieldElement::from_u64(0); 5])
                .unwrap(),
        };

        assert_eq!(
            verify_session(&[proof], &policy, &registered).unwrap_err(),
            Failure::NotASessionProof { circuit: "sod" }
        );
    }

    #[test]
    fn dates_must_agree_across_a_bundle() {
        let mut date = None;

        assert!(record_date(&mut date, 20260726).is_ok());

        assert!(record_date(&mut date, 20260726).is_ok());

        assert_eq!(
            record_date(&mut date, 20260725).unwrap_err(),
            Failure::InconsistentDates
        );

        assert_eq!(date, Some(20260726), "a rejected date must not be recorded");
    }
}
