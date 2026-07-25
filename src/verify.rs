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
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use crate::field::FieldElement;
use crate::layout::{Circuit, PublicInputs};

pub struct Proof {
    pub circuit: Circuit,
    pub verification_key: Vec<u8>,
    pub verification_key_hash: [u8; 32],
    pub bytes: Vec<u8>,
    pub public_inputs: PublicInputs,
}

/// What a relying party decides in advance: which circuit variants it trusts,
/// which application it is, and the freshness value it issued for this
/// exchange.
pub struct Policy {
    pub accepted_keys: HashMap<Circuit, Vec<[u8; 32]>>,
    pub domain: FieldElement,
    pub context: FieldElement,
    /// Whether the bundle must show the Document Signer belongs to a trusted
    /// set. Left off, a bundle proves only that some key signed the document.
    pub require_trust_anchor: bool,
    /// The registry an anchor proof has to be against, when one is required.
    pub registry_root: Option<FieldElement>,
}

impl Policy {
    pub fn new(domain: FieldElement, context: FieldElement) -> Self {
        Self {
            accepted_keys: HashMap::new(),
            domain,
            context,
            require_trust_anchor: false,
            registry_root: None,
        }
    }

    pub fn require_anchor(mut self, registry_root: FieldElement) -> Self {
        self.require_trust_anchor = true;

        self.registry_root = Some(registry_root);

        self
    }

    pub fn accept(mut self, circuit: Circuit, key_hash: [u8; 32]) -> Self {
        self.accepted_keys
            .entry(circuit)
            .or_default()
            .push(key_hash);

        self
    }
}

#[derive(Debug)]
pub struct Verified {
    pub nullifier: Option<FieldElement>,
    pub dsc_commitment: FieldElement,
    pub disclosed_fields: Vec<(u64, [FieldElement; 4])>,
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
    UnlinkedDataGroup { circuit: &'static str },
    UnlinkedCommitment { circuit: &'static str },
    NullifierFromAnotherDocument,
    NoTrustAnchorProof,
    AnchorForAnotherSigner,
    AnchorAgainstAnotherRegistry,
    Malformed(String),
}

impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoSecurityObjectProof => {
                write!(f, "the bundle has no Passive Authentication proof, so nothing establishes the document was signed")
            }
            Self::MoreThanOneSecurityObjectProof => {
                write!(
                    f,
                    "the bundle has more than one Passive Authentication proof"
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

    let mut security_objects = Vec::new();

    for proof in proofs {
        let name = proof.circuit.name();

        let accepted = policy
            .accepted_keys
            .get(&proof.circuit)
            .map(|keys| keys.contains(&proof.verification_key_hash))
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

        if proof.circuit == Circuit::Sod {
            security_objects.push(proof);
        }
    }

    let security_object = match security_objects.len() {
        0 => return Err(Failure::NoSecurityObjectProof),
        1 => security_objects[0],
        _ => return Err(Failure::MoreThanOneSecurityObjectProof),
    };

    let econtent_binding = security_object
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

    let mut commitments = Vec::new();

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

        commitments.push(
            proof
                .public_inputs
                .attributes_commitment()
                .map_err(malformed)?,
        );
    }

    let mut disclosed_fields = Vec::new();

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

                if proof.circuit == Circuit::Reveal {
                    let field_id = proof
                        .public_inputs
                        .field_id()
                        .map_err(malformed)?
                        .to_u64()
                        .map_err(malformed)?;

                    let mut revealed = [FieldElement([0u8; 32]); 4];

                    for (offset, slot) in revealed.iter_mut().enumerate() {
                        *slot = proof.public_inputs.at(2 + offset).map_err(malformed)?;
                    }

                    disclosed_fields.push((field_id, revealed));
                }
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

                if binding
                    != security_object
                        .public_inputs
                        .sod_secret_binding()
                        .map_err(malformed)?
                {
                    return Err(Failure::NullifierFromAnotherDocument);
                }

                nullifier = Some(proof.public_inputs.nullifier_value().map_err(malformed)?);
            }
            _ => {}
        }
    }

    let dsc_commitment = security_object
        .public_inputs
        .sod_dsc_commitment()
        .map_err(malformed)?;

    let mut signer_registry_root = None;

    for proof in proofs.iter().filter(|p| p.circuit == Circuit::Anchor) {
        if proof
            .public_inputs
            .anchor_dsc_commitment()
            .map_err(malformed)?
            != dsc_commitment
        {
            return Err(Failure::AnchorForAnotherSigner);
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

    Ok(Verified {
        nullifier,
        dsc_commitment,
        disclosed_fields,
        signer_registry_root,
    })
}

fn malformed<E: std::fmt::Display>(error: E) -> Failure {
    Failure::Malformed(error.to_string())
}

/// Delegates the cryptographic check to Barretenberg, the same prover that
/// produced the proof, rather than reimplementing verification here.
fn verify_one(proof: &Proof) -> Result<bool, Failure> {
    let dir = std::env::temp_dir().join(format!("zkicao-verify-{}", std::process::id()));

    std::fs::create_dir_all(&dir).map_err(|e| Failure::Malformed(e.to_string()))?;

    let vk_path = dir.join("vk");

    let proof_path = dir.join("proof");

    let inputs_path = dir.join("public_inputs");

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
            vk_path.to_str().unwrap(),
            "-p",
            proof_path.to_str().unwrap(),
            "-i",
            inputs_path.to_str().unwrap(),
        ])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map_err(|e| Failure::Malformed(format!("cannot run bb: {e}")))?;

    std::fs::remove_dir_all(&dir).ok();

    Ok(status.success())
}

fn write(path: &Path, bytes: &[u8]) -> Result<(), Failure> {
    let mut file = std::fs::File::create(path).map_err(|e| Failure::Malformed(e.to_string()))?;

    file.write_all(bytes)
        .map_err(|e| Failure::Malformed(e.to_string()))
}
