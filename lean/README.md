# Lean certificate foundation

From this directory:

```sh
lake update                 # only needed for initial dependency installation
lake build
lake env lean Audit.lean
```

Lean is pinned to 4.27.0 and mathlib to
`a3a10db0e9d66acbebf76c5e6a135066525ac900` (v4.27.0).
`lake-manifest.json` pins the transitive dependencies. The inspected upstream revision
uses Lean/mathlib 4.33.1; this small adaptation uses the already
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
`2^12509 - 1` is proved in Lean. The 23 September C++/Python exhaustive searches
and Hansen certificate establish both computationally; they are not imported
into these Lean proofs. `Audit.lean` reports the dependencies of the key theorems.
The independent Python check is `python3 ../scripts/check_12509.py`.

`BrauerBlock.lean` provides the next constructive layer:

- `doublingSteps`: an executable summand-value certificate; replay is proved
  to succeed from any valid endpoint, retain all old values, and end at `2^k*a`;
- `replayFrom_append`: composition of arbitrary certificate replays;
- `brauerBlock_replay`: given a valid chain ending at `2^a-1` and containing
  `2^b-1`, replay a block to `2^(a+b)-1` with exactly `b+1` new entries;
- `brauerBlock_upper_bound`: if the starting chain has `r` additions, the
  extended endpoint has minimum addition-chain length at most `r+b+1`.

Membership of the stored value is a hypothesis checked by replay, not an
assumed version of the conjecture. The Lean
certificate names summand values; no equivalence with the Python index-format
certificate generator has been proved. Five kernel-evaluated examples cover
zero doublings, two successful blocks, and absent/zero stored values.

`StarLift.lean` now proves the complete construction:

- `IsStarFrom source a bs` checks that each increment is already stored in
  the source prefix; `starSourceFrom` constructs the resulting source list.
  Source validity, endpoint `a+sum(bs)` and exact source length are proved.
- `starCertificateFrom` concatenates explicit Brauer blocks. Its length is
  `sum(bs)+length(bs)` for any inputs; correctness requires checked increments.
- `starCertificateFrom_replay` proves successful replay, chain validity,
  endpoint, exact length, retention of the initial target chain, and membership
  of every source Mersenne value throughout the completed lift.
- `starLift_certificate` and `starLift_upper_bound` specialise to `[1]`, giving
  exactly `n-1+r` additions and the resulting numerical bound. The empty
  increment list covers `n=1` without a separate exception.
- `scholz_of_optimal_star` proves the conjectured inequality under an explicit
  minimum-source-length hypothesis. No optimality theorem is assumed globally.

`Example12509.lean` also checks the published 18-step star source and applies
the general theorem to prove `additionChainLength (2^12509-1) ≤ 12526` and
successful replay of its explicit certificate. It does not expand the entire
large certificate for closed kernel evaluation. The independently checked
Python Hansen bound of 12525 is stronger and is not yet formalised.
Seven small kernel-checked examples cover the singleton source, a complete
two-block replay, and zero, unavailable and future increments. `Audit.lean`
now covers 69 named theorems; standard axiom dependencies are checked by the
integration runner.

`Hansen.lean` checks a marking certificate given as `(value, Bool)` entries,
with initial value 1 marked implicitly. `IsHansenFrom` requires strict growth
and a decomposition using the latest marked value and any stored value.
Acceptance enforces a marked endpoint. It is decidable and does not assume
optimality. Its proved API includes:

- successful source replay via `hansenPairsFrom`, source validity under the
  upstream predicate, and exactly one addition per source entry;
- `hansenAnchorFrom_latest` and `hansen_latest_anchor_step`: at every cut the
  carried anchor is the latest actual mark, is stored, and is a summand of
  the next step;
- stored marked values bounded by the final anchor, splitting an accepted
  certificate, and an explicit theorem forcing the final flag to be true.

Nine kernel-evaluated boundary/regression examples accompany the general
proofs. Five new named 12509 theorems check its marking, source list, replay,
marked-value list and 17-step count. The marking matches the saved Python
Hansen certificate. No detector completeness theorem or Python/Lean format
isomorphism is claimed. The large Hansen Mersenne lift and source optimality
remain outside Lean. See `../results/2026-09-24-hansen-underlining-lean.md`.

`HansenShift.lean` proves the shift accounting independently of the future
Mersenne replay. `hansenShiftDemands` lists consumers of the current anchor
through the next mark, and `hansenShiftMax` computes their maximum. For any
valid source prefix and accepted continuation, that maximum is exactly the
next-mark gap. `hansenShiftCaps` gives one cap per marked value, ending in zero;
its head is the actual maximum and its sum plus the initial anchor equals the
final anchor. Starting at 1 gives sum `n-1`.

Eight general theorems, eight kernel-evaluated examples and three 12509
specialisations cover the count. The concrete cap list matches the saved
Python certificate at its marked indices, with zero at every unmarked index.
The sum 12508 and budget 12525 are proved. Shifted-node distinctness is now
proved in `HansenNodes.lean`; allocation and sorted replay remain implementation
work. The numerical Lean bound
remains 12526 and the source optimum remains unformalised.

`HansenReplayFixtures.lean` is generated by the bounded Python exporter
`../scripts/export_lean_certificate.py`. It contains eight audited theorems:
replay, exact count, chain validity and a numerical upper bound for each of the
singleton and interleaving-29 lifts. The latter proves
`additionChainLength (2^29-1) ≤ 35` using closed kernel `decide` replay and the
existing soundness theorem. Neither source optimum nor Mersenne optimum is
asserted. This finite interface check does not prove correctness of the Hansen
generator or equivalence of arbitrary index and value certificates.

Regenerate a comparison file and check the whole bounded family from the repo root:

```sh
python3 scripts/verify_lean_export.py --output results/export-local.json --emit-fixtures results/export-local.lean
```

Both output paths must be fresh; saved fixture source must match exactly.
The script's Python checks do not run Lean. `lake build` here compiles both
saved fixtures, and `lake env lean Audit.lean` audits their proof dependencies.
The generic exporter accepts a checked index JSON and explicit `--name`,
`--exponent`, `--additions`; it refuses exponents above 64 or more than 128
additions before replay. Compiling its output is always a separate requirement.

`HansenNodes.lean` defines `shiftedMersenne a k = 2^k*(2^a-1)` and proves
seven general theorems: odd Mersenne remainder, unique power-of-two/odd-part
factorisation, injectivity for positive exponents, positivity, doubling,
base-node addition and preservation of duplicate-free labels under value
conversion. It reuses `Nat.pow_right_injective`, `List.Nodup.map_on` and the
existing `mersenne_block_identity`; no new dependency or toolchain change.

Six checked examples cover the essential zero-exponent failure, exponent 1,
zero and positive shifts, the two interleaving windows in the saved 29 fixture,
and separation of the 12 and 13 families for arbitrary shifts in the 12509
source. The general injectivity proof is unbounded. The list theorem assumes
duplicate-free labels and positive exponents; allocation must establish these
conditions before applying it. No successful general Hansen replay, exact
allocated-family cardinality or improved numerical bound follows yet.
