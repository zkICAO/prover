//! Runs the checklist over a real bundle.
//!
//! The unit tests reach the checklist with values built by hand. This reaches
//! it the way a relying party does: with proofs produced by the circuits,
//! verification keys produced by the backend, and public inputs read off
//! disk. It is the only test that would catch the checklist reading a value
//! from the wrong index, because every other test builds the inputs using the
//! same indices it then checks.
//!
//! The bundle is produced in the circuits repository:
//!
//!   cd ../circuits/fixtures/generator && cargo run -- bundle
//!
//! Point ZKICAO_BUNDLE at the result. Without it these tests skip rather than
//! fail, since the bundle needs the circuits, nargo and bb, none of which
//! this crate depends on.

use std::path::{Path, PathBuf};

use zkicao_prover::{
    parse_public_inputs, verify_bundle, verify_session, Circuit, Failure, FieldElement, Policy,
    Proof, Registered, Statement,
};

/// The scope a bundle was proved under, read from the bundle rather than
/// written here. The generator takes both from the environment, so a bundle
/// proved for a chain carries that chain's sender as its context, and a test
/// that hardcoded either would only pass for one of them.
fn scope(proofs: &[Proof]) -> (FieldElement, FieldElement) {
    let any = proofs.first().expect("a bundle has proofs");

    (
        any.public_inputs
            .domain()
            .expect("every proof carries a domain"),
        any.public_inputs
            .context()
            .expect("every proof carries a context"),
    )
}

fn bundle_directory() -> Option<PathBuf> {
    let path = PathBuf::from(std::env::var("ZKICAO_BUNDLE").ok()?);

    path.is_dir().then_some(path)
}

fn load(directory: &Path, name: &str, circuit: Circuit) -> Proof {
    let entry = directory.join(name);

    let verification_key = std::fs::read(entry.join("vk")).expect("bundle entry has no vk");

    let bytes = std::fs::read(entry.join("proof")).expect("bundle entry has no proof");

    let raw =
        std::fs::read(entry.join("public_inputs")).expect("bundle entry has no public inputs");

    let values = parse_public_inputs(&raw).expect("public inputs are malformed");

    Proof {
        circuit,
        verification_key,
        bytes,
        public_inputs: zkicao_prover::PublicInputs::new(circuit, values)
            .expect("public inputs do not match the circuit"),
    }
}

fn bundle(directory: &Path) -> Vec<Proof> {
    vec![
        load(directory, "sod", Circuit::Sod),
        load(directory, "dg_extract", Circuit::DgExtract),
        load(directory, "attributes", Circuit::Attributes),
        load(directory, "predicate_compare", Circuit::Compare),
        load(directory, "anchor", Circuit::AnchorInclusion),
        load(directory, "nullifier", Circuit::Nullifier),
    ]
}

/// A bundle that also proves the chip answered, which is the one statement
/// a copy of a document's data cannot make.
fn bundle_with_chip(directory: &Path) -> Vec<Proof> {
    let mut proofs = bundle(directory);

    // The chip's key is its own data group, so it needs its own extraction:
    // that is what puts the key inside the Security Object rather than
    // beside it.
    proofs.push(load(directory, "dg_extract_chip", Circuit::DgExtract));

    proofs.push(load(directory, "chip", Circuit::ChipActive));

    proofs
}

/// The registry the anchor proof in the bundle was built against.
fn registry_root(proofs: &[Proof]) -> FieldElement {
    proofs
        .iter()
        .find(|p| p.circuit == Circuit::AnchorInclusion)
        .expect("the bundle carries an anchor proof")
        .public_inputs
        .anchor_registry_root()
        .expect("the anchor proof carries a registry root")
}

fn policy_accepting(proofs: &[Proof]) -> Policy {
    let (domain, context) = scope(proofs);

    let mut policy = Policy::new(domain, context);

    for proof in proofs {
        policy = policy.accept(proof.circuit, proof.verification_key.clone());
    }

    policy
}

#[test]
fn a_real_bundle_verifies() {
    let Some(directory) = bundle_directory() else {
        eprintln!("skipping: set ZKICAO_BUNDLE to a directory built by the circuits repository");

        return;
    };

    let proofs = bundle(&directory);

    let verified = verify_bundle(&proofs, &policy_accepting(&proofs))
        .expect("a bundle straight from the circuits must verify");

    // The bundle carries the whole chain, so all of it should come back: a
    // holder identifier scoped to this application, and the registry the
    // signer was shown to belong to.
    let nullifier = verified.nullifier.expect("the bundle carries a nullifier");

    assert!(!nullifier.is_zero());

    assert_eq!(verified.signer_registry_root, Some(registry_root(&proofs)));

    assert!(!verified
        .dsc_commitment
        .expect("a leaf bundle exposes the signer commitment")
        .is_zero());

    // The point of returning statements: the verifier can see that what was
    // proved is the question it asked, rather than some other range over some
    // other field.
    assert_eq!(
        verified.statements,
        vec![
            Statement::DataGroup { number: 1 },
            Statement::Compare {
                field_id: 5,
                minimum: 0,
                maximum: 20080725,
            },
        ]
    );

    assert_eq!(verified.asserted_date, Some(20260725));
}

#[test]
fn a_chip_proof_says_the_chip_answered() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = bundle_with_chip(&directory);

    let verified = verify_bundle(&proofs, &policy_accepting(&proofs))
        .expect("a bundle with a chip proof must verify");

    assert!(
        verified.statements.contains(&Statement::ChipPresent),
        "the bundle proved chip presence and the result does not say so"
    );
}

// The chip proof attaches through its own data group binding, so a chip that
// answered for another document has nothing in this bundle to attach to.
#[test]
fn a_chip_proof_for_another_document_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    // The chip proof without the extraction that vouches for its data
    // group, so nothing in the bundle ties that key to this document.
    let mut proofs = bundle(&directory);

    proofs.push(load(&directory, "chip", Circuit::ChipActive));

    assert_eq!(
        verify_bundle(&proofs, &policy_accepting(&proofs)).unwrap_err(),
        Failure::ChipFromAnotherDocument
    );
}

#[test]
fn a_proof_from_an_unaccepted_circuit_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = bundle(&directory);

    // Every key accepted except the one the Security Object proof used, which
    // is the shape of a downgrade: a valid proof from a variant this verifier
    // did not agree to.
    let (domain, context) = scope(&proofs);

    let mut policy = Policy::new(domain, context);

    for proof in proofs.iter().filter(|p| p.circuit != Circuit::Sod) {
        policy = policy.accept(proof.circuit, proof.verification_key.clone());
    }

    assert_eq!(
        verify_bundle(&proofs, &policy).unwrap_err(),
        Failure::UntrustedVerificationKey { circuit: "sod" }
    );
}

#[test]
fn a_bundle_for_another_application_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = bundle(&directory);

    let mut policy = policy_accepting(&proofs);

    policy.domain = FieldElement::from_u64(1);

    assert_eq!(
        verify_bundle(&proofs, &policy).unwrap_err(),
        Failure::WrongDomain { circuit: "sod" }
    );
}

#[test]
fn a_bundle_from_another_session_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = bundle(&directory);

    let mut policy = policy_accepting(&proofs);

    policy.context = FieldElement::from_u64(1);

    assert_eq!(
        verify_bundle(&proofs, &policy).unwrap_err(),
        Failure::WrongContext { circuit: "sod" }
    );
}

#[test]
fn a_predicate_alone_establishes_nothing() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = vec![load(&directory, "predicate_compare", Circuit::Compare)];

    // The statement is true of some committed document. Without the chain
    // behind it nothing says that document was ever signed by a state.
    assert_eq!(
        verify_bundle(&proofs, &policy_accepting(&proofs)).unwrap_err(),
        Failure::NoSecurityObjectProof
    );
}

#[test]
fn a_predicate_detached_from_the_document_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    // Everything except the attribute proof, so the predicate refers to a
    // commitment nothing in the bundle published.
    let proofs = vec![
        load(&directory, "sod", Circuit::Sod),
        load(&directory, "dg_extract", Circuit::DgExtract),
        load(&directory, "predicate_compare", Circuit::Compare),
    ];

    assert_eq!(
        verify_bundle(&proofs, &policy_accepting(&proofs)).unwrap_err(),
        Failure::UnlinkedCommitment {
            circuit: "predicate_compare"
        }
    );
}

#[test]
fn an_anchor_is_refused_when_the_policy_requires_one_and_none_is_present() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs: Vec<Proof> = bundle(&directory)
        .into_iter()
        .filter(|p| p.circuit != Circuit::AnchorInclusion)
        .collect();

    let policy = policy_accepting(&proofs).require_anchor(FieldElement::from_u64(1));

    assert_eq!(
        verify_bundle(&proofs, &policy).unwrap_err(),
        Failure::NoTrustAnchorProof
    );
}

#[test]
fn an_anchor_against_another_registry_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = bundle(&directory);

    let policy = policy_accepting(&proofs).require_anchor(FieldElement::from_u64(1));

    assert_eq!(
        verify_bundle(&proofs, &policy).unwrap_err(),
        Failure::AnchorAgainstAnotherRegistry
    );
}

#[test]
fn the_required_anchor_is_satisfied_by_the_matching_registry() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = bundle(&directory);

    let policy = policy_accepting(&proofs).require_anchor(registry_root(&proofs));

    assert!(verify_bundle(&proofs, &policy).is_ok());
}

// The nullifier proves it holds the secret behind the binding the Security
// Object proof published. Take that proof away and the binding it has to
// match is not in the bundle at all.
#[test]
fn a_nullifier_without_the_document_behind_it_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs: Vec<Proof> = bundle(&directory)
        .into_iter()
        .filter(|p| p.circuit != Circuit::Sod)
        .collect();

    assert_eq!(
        verify_bundle(&proofs, &policy_accepting(&proofs)).unwrap_err(),
        Failure::NoSecurityObjectProof
    );
}

// The date a proof resolves two digit years against decides the century of a
// birth year, so a prover who picks it moves a holder born in 2010 to 1910
// and past an adult check. A verifier that pins the window closes that.
#[test]
fn a_date_outside_the_window_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = bundle(&directory);

    let policy = policy_accepting(&proofs).require_date_within(20250101, 20250131);

    assert_eq!(
        verify_bundle(&proofs, &policy).unwrap_err(),
        Failure::DateOutsideWindow {
            circuit: "attributes"
        }
    );
}

#[test]
fn a_date_inside_the_window_is_accepted() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = bundle(&directory);

    let policy = policy_accepting(&proofs).require_date_within(20260701, 20260731);

    assert!(verify_bundle(&proofs, &policy).is_ok());
}

/// What the relying party stored when the registration verified.
fn registered(directory: &Path) -> Registered {
    let proof = load(directory, "registration", Circuit::Registration);

    Registered {
        commitment: proof.public_inputs.registration_commitment().unwrap(),
        secret_binding: proof.public_inputs.registration_secret_binding().unwrap(),
    }
}

/// A session: questions only, against a registration from an earlier
/// exchange.
fn session(directory: &Path) -> Vec<Proof> {
    vec![
        load(directory, "predicate_compare", Circuit::Compare),
        load(directory, "nullifier", Circuit::Nullifier),
    ]
}

#[test]
fn a_later_session_verifies_against_the_stored_registration() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = session(&directory);

    let verified = verify_session(&proofs, &policy_accepting(&proofs), &registered(&directory))
        .expect("a session against the stored registration must verify");

    assert!(!verified
        .nullifier
        .expect("the session carries a nullifier")
        .is_zero());

    // No document proof ran here, so nothing re-establishes trust or dates;
    // those are the stored registration's.
    assert!(verified.dsc_commitment.is_none());

    assert!(verified.asserted_date.is_none());

    assert!(verified.signer_registry_root.is_none());

    assert_eq!(
        verified.statements,
        vec![Statement::Compare {
            field_id: 5,
            minimum: 0,
            maximum: 20080725,
        }]
    );
}

#[test]
fn a_session_against_another_registration_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = session(&directory);

    let mut other = registered(&directory);

    other.commitment = FieldElement::from_u64(123);

    assert_eq!(
        verify_session(&proofs, &policy_accepting(&proofs), &other).unwrap_err(),
        Failure::UnlinkedCommitment {
            circuit: "predicate_compare"
        }
    );
}

#[test]
fn a_session_nullifier_from_another_document_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = session(&directory);

    let mut other = registered(&directory);

    other.secret_binding = FieldElement::from_u64(123);

    assert_eq!(
        verify_session(&proofs, &policy_accepting(&proofs), &other).unwrap_err(),
        Failure::NullifierFromAnotherDocument
    );
}

#[test]
fn an_aggregated_session_verifies_against_the_stored_registration() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    // More than one question in a session aggregates into one proof; the
    // nullifier still travels beside it.
    let proofs = vec![
        load(&directory, "session", Circuit::SessionCompareMember),
        load(&directory, "nullifier", Circuit::Nullifier),
    ];

    let verified = verify_session(&proofs, &policy_accepting(&proofs), &registered(&directory))
        .expect("an aggregated session against the stored registration must verify");

    let set_root = proofs[0].public_inputs.at(4).unwrap();

    assert_eq!(
        verified.statements,
        vec![
            Statement::Compare {
                field_id: 5,
                minimum: 0,
                maximum: 20080725,
            },
            Statement::Member {
                field_id: 4,
                set_root,
            },
        ]
    );

    assert!(!verified
        .nullifier
        .expect("the session carries a nullifier")
        .is_zero());
}

#[test]
fn an_aggregated_session_against_another_registration_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = vec![load(&directory, "session", Circuit::SessionCompareMember)];

    let mut other = registered(&directory);

    other.commitment = FieldElement::from_u64(123);

    assert_eq!(
        verify_session(&proofs, &policy_accepting(&proofs), &other).unwrap_err(),
        Failure::UnlinkedCommitment {
            circuit: "session_compare_member"
        }
    );
}

#[test]
fn a_document_proof_in_a_session_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let mut proofs = session(&directory);

    proofs.push(load(&directory, "sod", Circuit::Sod));

    assert_eq!(
        verify_session(&proofs, &policy_accepting(&proofs), &registered(&directory)).unwrap_err(),
        Failure::NotASessionProof { circuit: "sod" }
    );
}

/// A bundle in the aggregate form: one registration proof standing for the
/// four leaf proofs, plus the per session questions.
fn registration_bundle(directory: &Path) -> Vec<Proof> {
    vec![
        load(directory, "registration", Circuit::Registration),
        load(directory, "predicate_compare", Circuit::Compare),
        load(directory, "nullifier", Circuit::Nullifier),
    ]
}

#[test]
fn a_registration_bundle_verifies() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = registration_bundle(&directory);

    let verified = verify_bundle(&proofs, &policy_accepting(&proofs))
        .expect("a registration bundle straight from the circuits must verify");

    // The nullifier chains against the registration proof's secret binding
    // and commitment exactly as it does against the leaf proofs'.
    assert!(!verified
        .nullifier
        .expect("the bundle carries a nullifier")
        .is_zero());

    // Signer trust was proved inside, against the registry the anchor used.
    let registration = load(&directory, "registration", Circuit::Registration);

    assert_eq!(
        verified.signer_registry_root,
        Some(
            registration
                .public_inputs
                .registration_registry_root()
                .unwrap()
        )
    );

    // The registration proof deliberately does not expose the signer
    // commitment.
    assert!(verified.dsc_commitment.is_none());

    assert_eq!(
        verified.statements,
        vec![
            Statement::DataGroup { number: 1 },
            Statement::Compare {
                field_id: 5,
                minimum: 0,
                maximum: 20080725,
            },
        ]
    );

    assert_eq!(verified.asserted_date, Some(20260725));
}

#[test]
fn a_leaf_proof_beside_a_registration_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let mut proofs = registration_bundle(&directory);

    proofs.push(load(&directory, "dg_extract", Circuit::DgExtract));

    assert_eq!(
        verify_bundle(&proofs, &policy_accepting(&proofs)).unwrap_err(),
        Failure::NotLinkableToRegistration {
            circuit: "dg_extract"
        }
    );
}

#[test]
fn a_chained_registration_bundle_verifies() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    // The variant that walked the whole chain to the country signing key.
    // Same layout, different verification key; the master list root comes
    // back where the registry root does.
    let proofs = vec![
        load(&directory, "registration_chain", Circuit::Registration),
        load(&directory, "predicate_compare", Circuit::Compare),
        load(&directory, "nullifier", Circuit::Nullifier),
    ];

    let verified = verify_bundle(&proofs, &policy_accepting(&proofs))
        .expect("a chained registration bundle straight from the circuits must verify");

    assert_eq!(
        verified.signer_registry_root,
        Some(
            proofs[0]
                .public_inputs
                .registration_registry_root()
                .unwrap()
        )
    );

    assert_eq!(verified.asserted_date, Some(20260725));

    assert!(verified.dsc_commitment.is_none());
}

#[test]
fn a_registration_beside_a_security_object_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let mut proofs = bundle(&directory);

    proofs.push(load(&directory, "registration", Circuit::Registration));

    assert_eq!(
        verify_bundle(&proofs, &policy_accepting(&proofs)).unwrap_err(),
        Failure::MoreThanOneSecurityObjectProof
    );
}

#[test]
fn a_registration_against_another_registry_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = registration_bundle(&directory);

    let policy = policy_accepting(&proofs).require_anchor(FieldElement::from_u64(1));

    assert_eq!(
        verify_bundle(&proofs, &policy).unwrap_err(),
        Failure::AnchorAgainstAnotherRegistry
    );
}

// One domain fixes one policy and one policy over one document gives one
// value, so a second nullifier proof never adds information. Refusing it is
// what keeps which value the application stores from being an accident of
// proof ordering.
#[test]
fn a_second_nullifier_proof_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let mut proofs = bundle(&directory);

    proofs.push(load(&directory, "nullifier", Circuit::Nullifier));

    assert_eq!(
        verify_bundle(&proofs, &policy_accepting(&proofs)).unwrap_err(),
        Failure::MoreThanOneNullifierProof
    );
}

// A key and a digest of a key are two values, and a sender who chose both
// could present an accepted digest beside a key of their own. Acceptance is
// by the key itself, so substituting one is simply a key that is not accepted.
#[test]
fn a_substituted_verification_key_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let mut proofs = bundle(&directory);

    let policy = policy_accepting(&proofs);

    proofs[0].verification_key[0] ^= 1;

    assert_eq!(
        verify_bundle(&proofs, &policy).unwrap_err(),
        Failure::UntrustedVerificationKey { circuit: "sod" }
    );
}
