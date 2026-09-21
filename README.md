# Scholz–Brauer research

The programme studies

\[
  \ell(2^n-1) \le n-1+\ell(n) \qquad (n>0),
\]

where `ℓ(n)` is the minimum number of additions in an addition chain for `n`.
Computational claims must have independently checkable certificates; a short
witness, its optimality, and the Scholz upper bound are separate claims.

## Verified status — 22 September 2026

The first daily run found only the initial README. Its advertised Python
library, experiments, results and Lean infrastructure did not exist. The original
Brauer-lift claim was withdrawn then; the construction has now been implemented
and independently checked.

The repository now has a Lean certificate generator that starts at 1 and
replays explicit summand pairs, rejecting unavailable summands or non-increasing
steps. Kernel-checked theorems establish that successful replay gives an addition
chain, with exactly one addition per pair, and therefore an upper bound on `ℓ`.

The published chain

```text
1, 2, 4, 6, 12, 13, 24, 48, 96, 192, 384, 768, 781,
1562, 3124, 6248, 12496, 12509
```

has been checked by Lean replay, by direct evaluation of the upstream
addition-chain predicate, and independently using Python integers. It proves
`ℓ(12509) ≤ 17`. The reused doubling lemma also proves `14 ≤ ℓ(12509)`.
The step `24 = 12 + 12` after `13` makes this particular chain non-star.

The published **18-step star witness** now has an explicit Brauer lift, checked
by independent integer replay and a value-only star check. It establishes
`ℓ(2^12509-1) ≤ 12526`. The Python generator also passes all 842 star prefixes
with at most six steps and endpoint at most 32, binary lifts for exponents
1–256, and 23 negative checks. See the dated report in `results/`.

The published **17-step non-star witness** now has a checked Hansen underlining
and an explicit **12,525-step Mersenne certificate**. Independent exact replay
establishes `ℓ(2^12509-1) ≤ 12525`, improving the stored star lift by one step.
Both the OEIS and Clift source witnesses give this length. Exhaustive regression
checks cover 1,051 source chains with at most six steps and endpoint at most 32:
30,582 marking masks and all 5,248 accepted underlinings. These are tests of
classification and construction, not searches for minimum chain lengths.

**Not established here:** `ℓ(12509)=17`, the shortest star length 18, or the
Scholz bound for 12509. A Hansen *chain* of length 17 does not establish that
12509 is a Hansen *number* without optimality evidence. The complete star lift
is now formalised in Lean; the Hansen lift is not.

Lean now proves one constructive Brauer block: from a valid chain ending at
`2^a-1` and containing `2^b-1`, an explicit replay certificate reaches
`2^(a+b)-1`, adds exactly `b+1` entries, and retains all prior values.
The whole-star theorem now composes these blocks, retains every source
Mersenne value, and proves exactly `n-1+r` additions for a checked `r`-step
source ending at `n`, including `[1]`. A conditional corollary proves Scholz
when that star source is optimal; it does not assert universal optimality.
Instantiating the rechecked 18-step source gives the kernel-checked bound
`ℓ(2^12509-1) ≤ 12526`. The stronger 12525 bound above is independently
checked in Python and has not yet been proved in Lean.

Integration includes both Python lifts, the Lean build and 28-theorem axiom
audit. The local bounds put `12508 + ℓ(12509)` in `[12522, 12525]`. The new
12525-step witness still needs the matching lower bound `ℓ(12509) ≥ 17`, or
another sufficient argument, before it proves the conjectured inequality.
See `results/2026-09-21-hansen-lift.md` for the construction, checks and limits.
See `results/2026-09-22-star-lift-lean.md` for the whole-star formal proof.

Clift's page was retrieved on 21 September. Its claim that 5,784,689 is the
first non-Hansen number remains a literature claim; the larger data and
optimality search have not been independently checked here.

## Reproduce

```sh
python3 scripts/verify_integration.py --output results/integration-local.json
```

Choose a fresh output path: the integration runner refuses to overwrite an
existing report. It runs the four Python checks, `lake build` and
`lake env lean Audit.lean` (from `lean/`), verifies the toolchain version and
vendored source hashes, and records input hashes, commands and exact outputs.
The small-check report now uses the actual Australia/Sydney run date.

Lean 4.27.0, mathlib and transitive dependencies are pinned. See `lean/README.md`
for setup, licence attribution and the adaptation from Google DeepMind's
formal-conjectures implementation. Its open Scholz theorem is an uncompiled
reference and is not imported into the proofs.

## Files and next work

- `lean/ScholzBrauer/AdditionChain.lean`: adapted upstream definitions and lemmas.
- `lean/ScholzBrauer/Certificate.lean`: replay generator, soundness and length proofs.
- `lean/ScholzBrauer/Example12509.lean`: concrete witness and numerical bounds.
- `lean/ScholzBrauer/BrauerBlock.lean`: doubling and single-block replay proofs.
- `lean/ScholzBrauer/StarLift.lean`: checked source increments, complete replay,
  stored-value invariant, exact count and conditional Scholz corollary.
- `scripts/check_12509.py`: independent exact check, including invalid fixtures.
- `scripts/star_lift.py`: star/Brauer lift to explicit summand-index pairs.
- `scripts/check_certificate.py`: independent replay and value-only star checker.
- `scripts/verify_star_lift.py`: bounded exhaustive and regression checks.
- `scripts/hansen_lift.py`: complete underlining detector and stored-shift lift.
- `scripts/verify_hansen_lift.py`: independent mask oracle and exact lift checks.
- `scripts/verify_integration.py`: combined reproducible evidence and axiom audit.
- `data/12509-star.json`: published source chain and attribution.
- `data/12509-hansen.json`: two rechecked 17-step sources and retrieval hashes.
- `results/`: dated verification evidence and source notes.
- `RESEARCH_LOG.md`: dated increments; `TODO.md`: ordered roadmap.

Next: obtain auditable optimality evidence for 12509 and formalise the Hansen
lift, starting with its underlining invariant. Larger
non-Hansen searches remain deferred. See `TODO.md` for the next increment.

## Sources

- [OEIS A349044](https://oeis.org/A349044): the explicit witness checked here;
  optimality statements remain separately sourced claims.
- [Flammenkamp, Shortest Addition Chains](https://wwwhomes.uni-bielefeld.de/achim/addition_chain.html).
- [Clift, Scholz–Brauer notes](https://www.additionchains.com/ScholzBrauer.html):
  underlining criterion and edge-labelling construction, retrieved 21 September.
- [formal-conjectures, inspected revision](https://github.com/google-deepmind/formal-conjectures/tree/40e7c98697de6f66b8cbdbf641749ab39ed9c152).
