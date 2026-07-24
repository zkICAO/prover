# zkICAO prover

Rust proving and off-chain verification library for zkICAO circuits.

Status: skeleton. The crate contains no code yet; it has no dependencies and builds empty. Everything below describes intended contents.

Two responsibilities:

1. Prove and verify UltraHonk proofs for the zkICAO circuit variants, via noir_rs with native Barretenberg FFI (macOS and Linux; mobile through Swoir on iOS and noir_android on Android).
2. The off-chain verifier: a single implementation of the cross-circuit binding checklist (domain and context equality, Security Object and data group bindings, DSC commitment, commitment equalities, nullifier bookkeeping) plus the accepted-variant verification key whitelist that prevents algorithm downgrade. Relying parties call one function instead of re-implementing the rules.

Witness preparation belongs here too, including normalizing ECDSA `s` to `n - s` when it exceeds `n/2`, which the circuits require and certificate signatures do not guarantee.

Planned pins: noir_rs v1.0.0-beta.19-4, Barretenberg 4.2.0-aztecnr-rc.2. These must stay aligned with the compiler pin published in [zkICAO/circuits](https://github.com/zkICAO/circuits), since proofs are produced against circuits compiled there.

## Trademarks and affiliation

zkICAO is an independent open source project, not affiliated with, endorsed by, or approved by the International Civil Aviation Organization (ICAO) or the United Nations. See [TRADEMARKS.md](https://github.com/zkICAO/circuits/blob/main/TRADEMARKS.md).

## License

MIT
