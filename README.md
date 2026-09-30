# Scholz–Brauer research

The programme studies

\[
  \ell(2^n-1) \le n-1+\ell(n) \qquad (n>0),
\]

where `ℓ(n)` is the minimum number of additions in an addition chain for `n`.
Computational claims must have independently checkable certificates; a short
witness, its optimality, and the Scholz upper bound are separate claims.

## Verified status — 1 October 2026

**Milestone 1 is complete.** Lean proves the general Hansen lift: for an
accepted marked source with `r` additions ending at `n`, every required node
and summand is allocated, sorting produces an addition chain, and a successful
summand-value replay has exactly `n-1+r` additions. Applying it to the checked
17-step source proves **`ℓ(2^12509-1) ≤ 12525` in Lean**. See
`results/2026-10-01-hansen-lift-lean.md` and `lean/ScholzBrauer/HansenLift.lean`.

**Milestone 2 is next.** Lean still proves only `14 ≤ ℓ(12509) ≤ 17`.
The optimum 17 and the full numerical Scholz instance remain computational
results until exclusion-certificate soundness and the lower bound are kernel
checked. No minimum Mersenne-chain length or general conjecture is claimed.

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

Two independent exhaustive searches now exclude **every chain of at most 16
additions for 12509**. Each completes after 1,345,873 visited prefixes, using
only the at-most-doubling bound and all earlier summand pairs. Combined with
the checked 17-step witness, this establishes **`ℓ(12509)=17` computationally**.
The saved Hansen lift therefore establishes the Scholz inequality at 12509:
`ℓ(2^12509-1) ≤ 12525 = 12508 + ℓ(12509)`. The checked optimal source also
establishes that 12509 is a Hansen number.

The exclusion now also has a portable JSON certificate and an independent
checker. Its 29,437 shared proof nodes cover all 1,345,873 prefix occurrences;
each occurrence is rechecked in its own chain context. The certificate excludes
all chains with at most 16 additions for 12509 using doubling bounds, missing
final summands and complete next-value splits. Regression checks compare all
576 target/limit decisions for targets 1–64 and limits 0–8 with unpruned
enumeration, and reject corrupted certificates. This makes the exclusion
independently replayable; checker soundness has not yet been formalised in Lean.
See `results/2026-09-25-exclusion-certificate.md` for the format and proof argument.

**Not established here:** a Lean optimality proof, an end-to-end Lean Scholz
instance at 12509, the minimum Mersenne-chain length, or the shortest star
length 18. The general
conjecture remains outside these results. See
`results/2026-09-23-optimality.md` for the search completeness argument,
independent checks, resource limits and distinction from a kernel-checked proof.

Lean now proves one constructive Brauer block: from a valid chain ending at
`2^a-1` and containing `2^b-1`, an explicit replay certificate reaches
`2^(a+b)-1`, adds exactly `b+1` entries, and retains all prior values.
The whole-star theorem now composes these blocks, retains every source
Mersenne value, and proves exactly `n-1+r` additions for a checked `r`-step
source ending at `n`, including `[1]`. A conditional corollary proves Scholz
when that star source is optimal; it does not assert universal optimality.
Instantiating the rechecked 18-step source gives the kernel-checked bound
`ℓ(2^12509-1) ≤ 12526`. The stronger 12525 bound is now proved in Lean
by the general Hansen lift.

Lean now also checks Hansen underlining over source values. It proves source
replay correctness, exact source length, the marked endpoint, and that every
step uses the latest marked value already stored in its prefix. The 17-step
12509 source and its marking are kernel checked, including retention of 12
as anchor through the unmarked value 13. This marking proof now supplies the
source hypothesis of the general Hansen lift. It does not prove source optimality.

Lean now also proves that the maximum requested shift between successive
marks `a < h` is `h-a`, and that these maxima sum to `n-1`. For 12509
the proved shift sum is 12508, giving an allocation budget of 12525 after
adding the 17 source steps. This count identity is now realised by the
allocation and sorted replay proofs in `HansenAllocation.lean` and `HansenLift.lean`.
See `results/2026-09-26-hansen-shift-lean.md`.

A bounded exporter now converts independently checked Python summand indices
into Lean summand-value fixtures. Kernel replay checks the singleton lift and
Clift's interleaving source `[1,2,4,8,9,12,17,29]`, giving the concrete bound
`ℓ(2^29-1) ≤ 35`. Python export/readback checks cover all 5,248 accepted small
underlinings. These are finite replay witnesses, not a general Hansen lift or
an index/value equivalence theorem; no source or Mersenne optimum is claimed.
The exporter caps exponents at 64 and additions at 128 before integer replay.
See `results/2026-09-28-hansen-export.md`.

Lean now proves that `2^k*(2^a-1)` uniquely determines both `a` and `k` when
`a > 0`, and that duplicate-free positive node labels map to duplicate-free
values. The new API also proves positivity, doubling and the base-node sum
identity. This removes the collision issue and is reused by the completed
general lift.
See `results/2026-09-29-hansen-nodes-lean.md`.

The Hansen allocation now has a separate labelled certificate: each node
`(a,k)` represents `2^k*(2^a-1)` and records its two summand labels. An
independent checker reconstructs caps from marked gaps, checks the complete
family and dependency closure, then sorts by exact value and replays the
ordinary certificate. Saved allocations for 29 and 12509 reproduce the existing
35- and 12525-step witnesses. All 5248 accepted small underlinings also agree
with the existing generator. This checked interface guided the completed
Lean allocation proof.
The Python checker does not itself establish the general theorem.
See `results/2026-09-30-hansen-allocation.md`.

Integration includes both Python lifts, both exhaustive exclusions, the portable
exclusion checker, the Lean build and 94-theorem axiom audit. The **Lean-only**
source bounds remain
`14 ≤ ℓ(12509) ≤ 17`; the **computational** optimum is now 17. The old
right-side interval `[12522,12525]` describes the Lean evidence alone.
See `results/2026-09-21-hansen-lift.md` for the construction and its then-current
limits, and `results/2026-09-22-star-lift-lean.md` for the whole-star formal proof.

Clift's criterion and the OEIS 17-step source were rechecked on 1 October.
Both published 17-step sources were last rechecked together on 30 September.
Clift's claim that 5,784,689 is the first non-Hansen number remains a literature
claim; the larger data and optimality search have not been independently
checked here.

## Reproduce

```sh
python3 scripts/verify_integration.py --output results/integration-local.json
```

Choose a fresh output path: the integration runner refuses to overwrite an
existing report. It runs the existing Python checks, compiles the C++17 search
and compares it with a separate Python traversal, then runs `lake build` and
`lake env lean Audit.lean` (from `lean/`), verifies the toolchain version and
vendored source hashes, and records input hashes, commands and exact outputs.
The small-check report uses the actual Australia/Sydney run date. Integration
also independently replays the Hansen certificate and checks that source witness,
both exhausted searches, portable exclusion and Mersenne replay agree on the
12509 statement. It rejects incomplete searches, mismatched targets and a lift
longer than 12525 before reporting the numerical Scholz instance. These report
consistency checks do not replace certificate checking or prove checker soundness.
See `results/2026-09-27-weekly-integration.md` for the week's evidence map.

The search needs a C++17 compiler; the recorded run uses Apple clang 21.0.0.
The saved exclusion can also be checked without a compiler or search generator:

```sh
python3 scripts/check_exclusion.py results/2026-09-25-12509-exclusion-certificate.json --target 12509 --max-steps 16
```

Lean 4.27.0, mathlib and transitive dependencies are pinned. See `lean/README.md`
for setup, licence attribution and the adaptation from Google DeepMind's
formal-conjectures implementation. Its open Scholz theorem is an uncompiled
reference and is not imported into the proofs.

## Files and next work

- `lean/ScholzBrauer/AdditionChain.lean`: adapted upstream definitions and lemmas.
- `lean/ScholzBrauer/Certificate.lean`: replay generator, soundness and length proofs.
- `lean/ScholzBrauer/Example12509.lean`: concrete witness and numerical bounds.
- `lean/ScholzBrauer/BrauerBlock.lean`: doubling and single-block replay proofs.
- `lean/ScholzBrauer/Hansen.lean`: decidable marking checker, source replay,
  latest-marked-anchor invariant and final-mark proof.
- `lean/ScholzBrauer/HansenShift.lean`: exact demand maxima, per-mark shift caps,
  telescoping shift sum and allocation budget.
- `lean/ScholzBrauer/HansenAllocation.lean`: finite labels, distinctness, exact
  count, endpoint envelope and summand closure.
- `lean/ScholzBrauer/HansenLift.lean`: sorted chain, successful replay, exact
  Hansen count, upper bound and conditional Scholz theorem.
- `lean/ScholzBrauer/HansenNodes.lean`: positive shifted-node injectivity,
  duplicate-free value conversion and local sum identities.
- `lean/ScholzBrauer/StarLift.lean`: checked source increments, complete replay,
  stored-value invariant, exact count and conditional Scholz corollary.
- `scripts/check_12509.py`: independent exact check, including invalid fixtures.
- `scripts/star_lift.py`: star/Brauer lift to explicit summand-index pairs.
- `scripts/check_certificate.py`: independent replay and value-only star checker.
- `scripts/verify_star_lift.py`: bounded exhaustive and regression checks.
- `scripts/hansen_lift.py`: complete underlining detector and stored-shift lift.
- `scripts/verify_hansen_lift.py`: independent mask oracle and exact lift checks.
- `scripts/search_chain.cpp`: bounded exact search with restartable pending prefixes.
- `scripts/verify_search.py`: independent Python search, unpruned small oracle,
  checkpoint checks and the optional `--research` 12509 exclusion.
- `scripts/exclusion_certificate.py`: bounded exclusion-DAG generator.
- `scripts/check_exclusion.py`: independent, context-sensitive proof-object checker.
- `scripts/verify_exclusion.py`: small exhaustive comparisons, corruption and
  budget checks, saved proof replay and optional deterministic regeneration.
- `scripts/verify_integration.py`: combined reproducible evidence, checked
  composition of the numerical conclusion, and axiom audit.
- `scripts/export_lean_certificate.py`: bounded checked index-to-value Lean export.
- `scripts/verify_lean_export.py`: exhaustive small export/readback and saved-fixture checks.
- `scripts/hansen_allocation.py`: bounded labelled-node/dependency generator.
- `scripts/check_hansen_allocation.py`: independent family/closure/count/endpoint
  checker and exact compilation to ordinary index replay.
- `scripts/verify_hansen_allocation.py`: exhaustive small oracle comparisons,
  saved allocation readback and adversarial/budget/CLI checks.
- `lean/ScholzBrauer/HansenReplayFixtures.lean`: generated kernel replay witnesses
  for exponents 1 and 29, including interleaved shifted values.
- `scripts/verify_evidence_composition.py`: mismatched/incomplete report regressions,
  including rejection of the star-only 12526 bound as evidence for 12525.
- `data/12509-star.json`: published source chain and attribution.
- `data/12509-hansen.json`: two rechecked 17-step sources and retrieval hashes.
- `results/`: dated verification evidence and source notes.
- `RESEARCH_LOG.md`: dated increments; `TODO.md`: ordered roadmap.

Next: formalise the portable exclusion rules and their soundness against the
upstream addition-chain definition. Kernel-check target 7 with limit 3 before
attempting the 12509 DAG. Combine the resulting optimum with the now-proved
12525 bound. Larger non-Hansen searches remain deferred. See `TODO.md`.

## Sources

- [OEIS A349044](https://oeis.org/A349044): the explicit witness checked here;
  optimality statements remain separately sourced claims.
- [Flammenkamp, Shortest Addition Chains](https://wwwhomes.uni-bielefeld.de/achim/addition_chain.html).
- [Clift, Scholz–Brauer notes](https://www.additionchains.com/ScholzBrauer.html):
  underlining criterion and edge-labelling construction, retrieved 21 September.
- [formal-conjectures, inspected revision](https://github.com/google-deepmind/formal-conjectures/tree/40e7c98697de6f66b8cbdbf641749ab39ed9c152).
