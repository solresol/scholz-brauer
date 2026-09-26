# 2026-09-27 — Sunday evidence integration

Australia/Sydney. This run integrates 21–26 September and strengthens how the
integration report composes the numerical conclusion at 12509. No new numerical
bound, theorem of Lean, mathematical counterexample or novelty is claimed.

## Evidence map

| Claim | Verified evidence | Boundary |
| --- | --- | --- |
| ell(12509) <= 17 | Published source, independent integer checking, Lean replay and direct predicate evaluation | A witness alone does not prove optimality |
| ell(12509) >= 17 | Two exhaustive traversals of all chains with <=16 steps; independently checked exclusion DAG | Computational proof argument; checker soundness is not yet formalised |
| ell(2^12509-1) <= 12525 | Exact replay of saved Hansen summand-index certificate | No Mersenne optimality assertion |
| Scholz at 12509 | Combine source optimum 17 with the 12525-step witness: 12525 = 12509-1+17 | Computational instance, not a universal or Lean proof |
| Whole star/Brauer lift | Lean source invariant, replay, exact n-1+r count and conditional optimal-source corollary | The available 18-step star source gives only the Lean Mersenne bound 12526 |
| Hansen marking and shift budget | Lean anchor invariant, next-mark maximum, telescope and budget 12525 | Distinct shifted nodes and sorted replay remain to be proved |

The Lean-only source interval remains [14,17]. The formal Hansen budget is a
count identity, not yet an upper bound for an actual Mersenne chain. Current
README claims match the code and recorded proofs; none needed withdrawing.
Historical dated reports retain the limitations that applied when written.

## Concrete increment

Previously, the integration runner ran the component checks and then inserted
literal success flags. It now checks the composition explicitly: the 17-step
source endpoint, both exhausted searches at limit 16, the full C++ root [1]
and empty pending frontier, the matching portable exclusion, and an exactly
replayed Mersenne witness of length at most 12525. The derived source interval,
right-hand side and witness length supply the computational claim fields.

The saved Hansen certificate also gets a standalone replay, independent of its
generator. Its hash must match both the integration input and the Hansen
regression's certificate hash. All evidence comes from newly executed checkers;
the composition function is a report-contract check, not a certificate verifier,
and does not make arbitrary supplied summaries trustworthy.

Three unittest methods cover a matching case, 26 altered cases and eight
missing-field cases. They reject budget/witness search statuses, partial roots,
nonempty frontiers, target/limit disagreement, malformed counts, an unverified
endpoint and a 12526-step lift offered for the 12525 conclusion. Tests pass both
normally and under Python -O. No actual component failure was found today.

## Reproduction and verification

```sh
python3 scripts/verify_integration.py --output results/2026-09-27-integration-checks.json
```

Use a fresh filename on reruns; existing evidence is never overwritten.
Started **08:04:58 AEST**, completed in **55.145647 seconds**. The JSON records
commands, outputs, 39 input hashes, Python 3.9.6, Apple clang 21.0.0, Lean 4.27.0
and the unchanged pinned dependency inputs. Exact integers throughout; no seed.

- 842 star prefixes (<=6 additions, endpoint <=32), binary sources 1–256;
- 1051 general source chains, 30582 masks and all 5248 accepted Hansen markings
  in the same small range; both published 12509 sources and Lean fixture match;
- 576 target/limit decisions (targets 1–64, limits 0–8), against 78758 unpruned
  prefixes, including checkpoint coverage and malformed-input cases;
- both <=16-step exclusions for 12509: 1345873 visits each, exhausted within
  budgets of 10000000 (C++) and 2000000 (Python); no heuristic search;
- portable exclusion: 29437 shared nodes, rechecked at 1345873 contextual
  occurrences, within its 2000000 visit budget; no regeneration needed;
- standalone Hansen replay: 12525 additions, **0.054021 s**;
- `lake build`: **752 jobs**, **6.494372 s**;
- `lake env lean Audit.lean`: **54 named theorems**, **8.182695 s**, only
  standard axioms; all five vendored source hashes match.

The compiled local Lean source scan found no sorry, admit, custom axiom,
unsafe or native_decide. The open upstream Scholz statement remains an
uncompiled reference. The pinned upstream definitions and statement were
reinspected; no Lean source or dependency changes were needed today.

## Sources and retired assumptions

Reopened [Clift's exposition](https://www.additionchains.com/ScholzBrauer.html)
and [OEIS A349044](https://oeis.org/A349044) on **27 September 2026**. Both
17-step chain lists and the 18-step star list match the local fixtures.
`data/2026-09-27-integration-sources.json` records URLs, access time and the
live-page version limitation. No original Hansen article or new minimum-length
table was imported; larger non-Hansen and first-example claims remain literature
claims, not independently verified results of this project.

Two implementation assumptions remain explicitly retired: chosen non-star
parent indices do not imply non-star values (6=3+3=5+1 in [1,2,3,5,6]); shared
exclusion-node syntax does not justify caching truth without its prefix context.
Neither is a failed mathematical hypothesis. No mathematical hypothesis was
newly rejected this week, and no absence-of-witness or timeout is used as proof.

## Next informative work

Monday: export small Hansen index certificates to Lean summand-value replay
fixtures with a bounded size, including [1] and the interleaving example at 29.
Kernel replay checks will test the interface without implying general format
equivalence. Tuesday: prove distinctness of positive-exponent shifted Mersenne
nodes by uniqueness of odd parts, then work toward summand availability and
sorted replay. Separately, prove exclusion-checker soundness and kernel-check
7/3 before attempting the large 12509 DAG. Larger cases remain deferred.
