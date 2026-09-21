# 2026-09-22 — Tuesday — complete star lift in Lean

## Result

`lean/ScholzBrauer/StarLift.lean` proves a complete constructive Brauer lift.
A star source is represented by increments `bs`, starting at 1. At each step
with current endpoint `a`, `IsStarFrom` checks that the next increment `b`
already occurs in the source prefix, then appends `a+b` to that prefix.
This is a decidable condition on small source values, independent of the
Mersenne target or any optimality hypothesis.

For a checked source with `r = bs.length` additions and endpoint
`n = 1 + bs.sum`, the theorem `starLift_certificate` supplies an explicit
summand-value certificate and proves:

- successful replay from `[1]` to an addition chain ending at `2^n-1`;
- exactly `n-1+r` certificate pairs and `n+r` chain entries;
- membership of `2^x-1` for every source value `x` in the completed chain.

The proof inducts over the increments, uses `brauerBlock_replay` and
`replayFrom_append`, and maintains stored Mersenne membership after every block.
Old stored values survive by list inclusion; the new source value's Mersenne
value is the block endpoint. The block counts `b+1` sum to `sum(bs)+r`, hence
`n-1+r`. The empty increment list gives source `[1]`, target `[1]` and zero
additions. Separate lemmas establish the generated source's addition-chain
validity, endpoint and exact length under the reused upstream definition.

`starLift_upper_bound` consequently proves `ell(2^n-1) <= n-1+r`.
`scholz_of_optimal_star` additionally assumes `r = ell(n)` and proves Scholz
for that source. It neither assumes the target inequality nor asserts that
every exponent has an optimal star source.

## The 12509 instance and limits

Reopened [OEIS A349044](https://oeis.org/A349044) on **2026-09-22,
Australia/Sydney** and matched the entire published 18-step star witness:

```text
1,2,3,4,7,11,18,25,43,86,172,344,688,1376,1401,2777,5554,6955,12509
```

The checked increments are:

```text
1,1,1,3,4,7,7,18,43,86,172,344,688,25,1376,2777,1401,5554
```

Lean checks their star condition and equality of the generated source to the
published list using `decide`. A separate Python comparison matched the Lean
list and increments against `data/12509-star.json`. No source minimum-length
assertion was imported. `starLift12509_certificate` applies the general proof
to establish successful replay and exactly 12,527 entries without expanding
the large replay in the kernel. `mersenne12509_length_le_12526` proves
**`ell(2^12509-1) <= 12526`** in Lean.

This formal bound is one addition weaker than Monday's independently checked
Python Hansen witness of 12,525. Hansen formalisation, equivalence between the
Lean summand-value and Python summand-index formats, and local optimality at
12509 remain unproved. The local interval `14 <= ell(12509) <= 17` is unchanged.
Neither the 12526 formal result nor the 12525 numerical witness by itself
proves Scholz at 12509. No new best numerical bound, novelty, current frontier,
counterexample, or failed mathematical hypothesis is claimed.

## Source reuse and pinned dependencies

Read the vendored addition-chain implementation, Scholz statement, provenance
and Apache-2.0 licence; reopened the pinned primary source URLs on 2026-09-22:

- [AdditionChain.lean](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/NumberTheory/AdditionChain.lean).
- [ScholzConjecture.lean](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/Wikipedia/ScholzConjecture.lean).

Revision `40e7c98697de6f66b8cbdbf641749ab39ed9c152`. Reused the adapted
`IsAdditionChain`, `additionChainLength`, positivity and upper-bound API.
All five vendored hashes match. The upstream open theorem remains uncompiled
and unimported; it supplies no axiom or hypothesis.

Pins unchanged: Lean **4.27.0**, mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`, existing transitive manifest.
Python **3.9.6**, standard library only. Exact arithmetic and kernel-checked
proofs; no heuristic, random seed, optimum search or timeout inference.

## Verification

From `lean/`, `lake build` compiled the new module and instance successfully
(750 jobs). Seven small kernel-checked examples cover the singleton, its zero
bound, two consecutive blocks using an older stored value, and invalid zero,
unavailable and future increments. During development, source-length
normalisation required explicit empty-list length simplification and arithmetic
rearrangement. No theorem was weakened or left with a placeholder.

Final full integration from the repository root:

```sh
python3 scripts/verify_integration.py --output results/2026-09-22-integration-checks.json
```

Use a fresh report filename on reruns. Started
**2026-09-22T08:06:38.858993+10:00**; passed in **12.915720 s**, including:

- cached Lean build: **2.416202 s**, 750 jobs;
- all **28** named theorem axiom audits: **7.024810 s**; only `propext`,
  `Quot.sound` and, for minimum-length bounds, `Classical.choice`;
- previous exact 17-step source check and seven negative fixtures;
- exact replay of the stored 12526-step certificate;
- all 842 star prefixes with <=6 additions and endpoint <=32, binary sources
  1..256, and 23 negative checks;
- all 1,051 small addition-chain sources, 30,582 marking masks and 5,248
  accepted Hansen lifts, both published 12509 sources, and 21 negatives.

These finite enumerations check the implementations, not optimal lengths.
All subprocesses finished within the existing 180-second limit. Full outputs,
input hashes, theorem names and timings are in the integration JSON.
Compiled local Lean sources contain no `sorry`, custom axiom or `native_decide`.

The integration report now distinguishes the formal star bound from the Python
Hansen bound. Review caught a stale `lean_lift_formalised: false` field in the
Python-only star verifier; it now reports that this command does not check Lean
and that no format-equivalence theorem is proved. Integration was rerun after
that metadata correction. Historical reports and certificates are unchanged.

## Next

Wednesday: obtain auditable primary optimality evidence for 12509; checkpoint
and bound any local exclusion search. Thursday: define and check Hansen
underlining in Lean, then prove the latest-underlined-anchor invariant for the
17-step source. Whole-star replay is complete and need not be repeated.
