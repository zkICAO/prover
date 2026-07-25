# zkICAO prover

Off-chain verification for zkICAO proofs.

A relying party receives a bundle of proofs rather than one. Each is sound on its own and says nothing about the others, so what makes them describe a single document is a set of equalities between their public values. This crate is that check, written once so an integration does not carry its own copy of the rules.

## What it does

`verify_bundle` runs the checklist in order. Every proof must carry a verification key the verifier accepts, then verify cryptographically, then agree on the application domain and the session context. Only then are the links checked: data group proofs must reference the authenticated Security Object, attribute proofs must reference an extracted data group, predicates and the nullifier must reference a published commitment, and the nullifier must carry the secret binding from that same Security Object.

Two failures it closes are easy to miss when integrating by hand. Proofs carrying different domains are several documents wearing one identity. A proof from a weaker circuit variant is a downgrade unless the verifier states which verification keys it accepts, which the policy makes mandatory rather than optional.

A relying party can also require the Document Signer to be shown trusted. Without that, a bundle establishes that some key signed the document and nothing about whose key it is.

## What it does not do

It does not prove. Proving needs the Barretenberg FFI and the toolchain around it, and a relying party that only checks proofs should not have to build any of that. Keeping the two apart is what lets this crate have no dependencies at all, which is also what makes it small enough to read end to end before trusting it. Witness preparation, including normalizing ECDSA `s` to `n - s` when it exceeds `n/2`, belongs with proving for the same reason and is not here.

Cryptographic verification is delegated to Barretenberg through its command line tool, the same prover that produced the proof, rather than reimplemented. `bb` must be on the path.

It also does not keep state. Recognising a nullifier it has seen before is the application's job; this returns the value.

## Layout compatibility

The public input indices this crate reads are fixed by circuit signatures in [zkICAO/circuits](https://github.com/zkICAO/circuits), a separate repository, so the table here can drift from them silently. `layout.manifest` is the guard: it is generated from the compiled ABIs, committed here, and checked by tests. A signature change not reflected in a regenerated manifest fails them. It has already caught one drift.

## Platform

Unix. The scratch directory each verification uses is named from `/dev/urandom` and created with mode 0700, so a local user cannot predict the path, place a symlink at it, or read a proof out of it.

## Trademarks and affiliation

zkICAO is an independent open source project, not affiliated with, endorsed by, or approved by the International Civil Aviation Organization (ICAO) or the United Nations. See [TRADEMARKS.md](https://github.com/zkICAO/circuits/blob/main/TRADEMARKS.md).

## License

MIT
