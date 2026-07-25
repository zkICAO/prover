//! Off-chain verification for zkICAO proofs.
//!
//! A relying party receives a bundle of proofs rather than one. Each proof is
//! sound on its own and says nothing about the others, so what makes them
//! describe a single document is a set of equalities between their public
//! values. This crate is that check, written once so an integration does not
//! carry its own copy of the rules.
//!
//! It has no dependencies. Cryptographic verification is delegated to
//! Barretenberg through its command line tool, the same prover that produced
//! the proof, rather than reimplemented here.
//!
//! ```no_run
//! use zkicao_prover::{Circuit, FieldElement, Policy, verify_bundle};
//!
//! let policy = Policy::new(FieldElement::from_u64(42), FieldElement::from_u64(7))
//!     .accept(Circuit::Sod, [0u8; 32]);
//!
//! let verified = verify_bundle(&[], &policy);
//! ```

mod field;
mod layout;
mod verify;

pub use field::{parse_public_inputs, Error, FieldElement};
pub use layout::{Circuit, PublicInputs};
pub use verify::{verify_bundle, Failure, Policy, Proof, Verified};
