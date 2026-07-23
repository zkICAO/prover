# zkICAO prover

Rust proving and off-chain verification library for zkICAO circuits.

Two responsibilities (landing in phase P1e):

1. Prove and verify UltraHonk proofs for the zkICAO circuit variants, via noir_rs with native Barretenberg FFI (macOS and Linux; mobile through Swoir on iOS and noir_android on Android).
2. The off-chain verifier: a single implementation of the cross-circuit binding checklist (domain and context equality, eContent and data group bindings, DSC commitment, commitment equalities, nullifier bookkeeping) plus the accepted-variant vkHash whitelist that prevents algorithm downgrade. Relying parties call one function instead of re-implementing the rules.

Status: bootstrap. Circuits land first in the `circuits` repository.

Planned pins: noir_rs v1.0.0-beta.19-4, Barretenberg 4.2.0-aztecnr-rc.2 (see circuits/TOOLCHAIN.md).

## License

MIT
