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
    parse_public_inputs, verify_bundle, Circuit, Failure, FieldElement, Policy, Proof, Statement,
};

const DOMAIN: u64 = 42;

const CONTEXT: u64 = 99;

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
    let mut policy = Policy::new(
        FieldElement::from_u64(DOMAIN),
        FieldElement::from_u64(CONTEXT),
    );

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

    assert!(!verified.dsc_commitment.is_zero());

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
fn a_proof_from_an_unaccepted_circuit_is_refused() {
    let Some(directory) = bundle_directory() else {
        return;
    };

    let proofs = bundle(&directory);

    // Every key accepted except the one the Security Object proof used, which
    // is the shape of a downgrade: a valid proof from a variant this verifier
    // did not agree to.
    let mut policy = Policy::new(
        FieldElement::from_u64(DOMAIN),
        FieldElement::from_u64(CONTEXT),
    );

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

    policy.domain = FieldElement::from_u64(DOMAIN + 1);

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

    policy.context = FieldElement::from_u64(CONTEXT + 1);

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
