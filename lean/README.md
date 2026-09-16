# Lean certificate foundation

From this directory:

```sh
lake update                 # only needed for initial dependency installation
lake build
lake env lean Audit.lean
```

Lean is pinned to 4.27.0 and mathlib to
`a3a10db0e9d66acbebf76c5e6a135066525ac900` (v4.27.0).
`lake-manifest.json` pins the transitive dependencies. The upstream project
currently uses Lean/mathlib 4.33.1; this small adaptation uses the already
available 4.27.0 toolchain.

`ScholzBrauer/AdditionChain.lean` adapts the Apache-2.0 implementation from
Google DeepMind's formal-conjectures commit
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`.
The definitions and theorem statements are unchanged. Compatibility edits remove
`module`, `public`, and `@[expose] public section`, and replace the renamed
`Mathlib.Order.Lattice.Nat` import with `Mathlib.Data.Nat.Lattice`.
Original files, licence, exact URLs and SHA-256 hashes are in
`vendor/formal-conjectures/`.

The upstream `ScholzConjecture.lean` is retained **only as an uncompiled source
reference**. Its open statement contains `sorry`; it is not imported by this
library and supplies no hypothesis or theorem to our proofs. Our compiled files
contain no `sorry`, custom axiom, or `native_decide`. Concrete proofs use `decide`,
which Lean's kernel checks.

`Certificate.lean` provides:

- `replay`: generate a strictly increasing chain from explicit summand pairs,
  starting at `[1]`, or return `none` when a step is invalid;
- `append_sum`, `replay_sound`: prove every successful replay is an addition
  chain under the upstream definition;
- `replay_length`: prove exactly one addition per supplied pair;
- `replay_upper_bound`: turn successful replay and an endpoint check into an
  upper bound on the minimum addition-chain length.

`Example12509.lean` replays a published 17-step witness and also checks the list
directly against the upstream predicate. The proved numerical result is
`14 ≤ additionChainLength 12509 ≤ 17`. Neither optimality nor the Scholz bound for
`2^12509 - 1` is proved. `Audit.lean` reports the dependencies of the key theorems.
The independent Python check is `python3 ../scripts/check_12509.py`.
