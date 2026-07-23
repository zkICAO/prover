//! zkICAO prover: proving and off-chain verification for zkICAO circuits.
//!
//! Grows in phase P1e with two responsibilities:
//!
//! 1. Prove and verify UltraHonk proofs for the zkICAO circuit variants
//!    (via `noir_rs` v1.0.0-beta.19-4 with native Barretenberg FFI).
//! 2. The off-chain verifier: enforce the cross-circuit binding rules
//!    (invariants I1..I7 of the specification) so relying parties do not
//!    re-implement them. This includes the accepted-variant vkHash
//!    whitelist that prevents algorithm downgrade.
//!
//! Until P1e this crate intentionally contains no code: circuits land
//! first in the `circuits` repository.
