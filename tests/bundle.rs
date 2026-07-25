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
    parse_public_inputs, verify_bundle, Circuit, Failure, FieldElement, Policy, Proof,
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

    let key_hash_bytes = std::fs::read(entry.join("vk_hash")).expect("bundle entry has no vk_hash");

    let mut verification_key_hash = [0u8; 32];

    verification_key_hash.copy_from_slice(&key_hash_bytes);

    let bytes = std::fs::read(entry.join("proof")).expect("bundle entry has no proof");

    let raw =
        std::fs::read(entry.join("public_inputs")).expect("bundle entry has no public inputs");

    let values = parse_public_inputs(&raw).expect("public inputs are malformed");

    Proof {
        circuit,
        verification_key,
        verification_key_hash,
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
    ]
}

fn policy_accepting(proofs: &[Proof]) -> Policy {
    let mut policy = Policy::new(
        FieldElement::from_u64(DOMAIN),
        FieldElement::from_u64(CONTEXT),
    );

    for proof in proofs {
        policy = policy.accept(proof.circuit, proof.verification_key_hash);
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

    // This bundle carries no nullifier and no anchor, so what it establishes
    // is that a signed document exists and a statement about one of its
    // fields holds, and nothing about which signer or which holder.
    assert!(verified.nullifier.is_none());

    assert!(verified.signer_registry_root.is_none());

    assert!(!verified.dsc_commitment.is_zero());
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
        policy = policy.accept(proof.circuit, proof.verification_key_hash);
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

    let proofs = bundle(&directory);

    let policy = policy_accepting(&proofs).require_anchor(FieldElement::from_u64(1));

    assert_eq!(
        verify_bundle(&proofs, &policy).unwrap_err(),
        Failure::NoTrustAnchorProof
    );
}
