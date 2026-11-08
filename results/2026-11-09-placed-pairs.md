# Actual exception positions — 9 November 2026, Sydney

Scheduled trigger: 8 November 2026, 21:00 UTC / 9 November, 08:00 Sydney.
Active obligation: Lean exclusion of every 108-doubling labelling of Clift's
selected 109 parent graph. Its exact computational minimum remains 109.

## Result and boundary

**Exact full-interval placement and a shared singleton reduce the necessary
344 ordered step pairs to 278 computationally.** The new necessary placement
theorems are kernel checked; the finite evaluation and 278 count are not.
No full selected-109 Lean exclusion, feasible cap assignment, new Scholz
instance, minimum Mersenne-chain length or novelty claim is made.

The seven source-side exceptions are the three pairs starting at
`A3, A3+d2, A3+q`, each with step d1, plus singleton `A3+p`. The sink-side
exceptions start at `A1+p, A1+p+v, A2+p`, each with step u, plus the **same
actual singleton** `A3+p`. The preceding sparse predicates kept residues and
allowed unrelated singleton witnesses. The new predicate retains their
positions in the whole interval.

For positive steps m,d, let S(m,d) be all positions s for which [0,108]
is the disjoint union of 51 m-pairs, three d-pairs and {s}. Then every original
budget-108 graph labelling must satisfy

```
(u,d1) in sparseStepPairs,    (A3+p) in S(u,d1) intersect S(d1,u).
```

Evaluating every S on the 344-pair input domain gives 34 empty directional
domains, which remove 52 ordered pairs after reversing. An additional 14
ordered pairs have nonempty but disjoint singleton domains. This leaves
**278 pairs**, 66 fewer than 344. For example S(7,6) is empty; (4,27) has
two nonempty domains whose intersection is empty. (2,3) remains: both
domains contain every odd singleton 1,3,...,107. Thus neither
`min(u,d1)=1` nor complete interval/cap classification follows.

This test permits unrelated triples and halves in its two directions.
The actual box, v,d2, other coordinates, both remainder odd-run restrictions,
twelve critical families and 64 orientations impose further constraints.
The 278 survivors are not whole-graph feasible configurations.

## Kernel-checked reduction

`lean/ScholzBrauer/Clift109PlacedPairs.lean` imports the existing sparse
domain and reuses `threePairWeights`, `zbranch`, both full-interval
factorizations and the normalized graph theorem. Its predicate is the exact
multiset equation

```
range109 = zbranch half m + threePairWeights d x y z s.
```

`interval_three_pair_bounds` proves that the seven exceptional positions
are distinct, each pair start r obeys 0<=r and r+d<109, the singleton obeys
0<=s<109, and the complementary half has cardinality 51. Signed original
coordinates are allowed. Distinctness is derived from the interval equation,
not assumed as a convenient extra hypothesis.

`interval_three_pair_placements` proves both equations with the same A3+p.
`placed_pairs_of_budget` transports them and the existing 344-pair membership
to all natural bases/shifts/caps with seed B1=1, every selected production
equation, outgoing shift bounds, terminal B109=M109 and cap sum <=108.
There is no enumeration premise or assumed exclusion. The finite S-domain
implementation is deliberately outside this Lean theorem's claim.

## Bounded exact computation and independent checks

```
python3 scripts/experiment_clift109_placed_pairs.py \
  --output results/2026-11-09-placed-pairs.json
```

The report refuses replacement and records its base commit, input hashes,
compiler command/version, bounds, every singleton domain, every witness,
trial counts and runtimes. Python 3.12.14, the installed g++ and standard
libraries only; no random seed or external solver. Overall hard bound:
180 seconds; each C++ call has a 60-second bound, compilation 30 seconds.
The complete run finishes in **25.788 seconds**: C++ 2.029, independent
Python 23.487, controls 0.099. These are computational results, not proofs
accepted by a compiler or theorem kernel.

Both algorithms enumerate every sorted triple
`0<=x<y<z<109-d` whose six endpoints are distinct. Sorting is complete
because the three d-pairs are interchangeable; repeated starts would violate
the proved distinctness. Each algorithm examines **42,758,315 disjoint
triples** across all 344 directional inputs.

1. `scripts/clift109_placed_pairs.cpp` removes the six endpoints from the
   interval. Pair-peeling finds the odd arithmetic m-runs. One singleton can
   repair the support precisely when there is exactly one odd run; all its
   even-indexed positions are retained. The union over all triples gives S.
   Unsigned 128-bit masks contain at most 109 interval positions, and shifts
   are strictly between 0 and 109. Discarded high bits cannot re-enter a run.
2. The independent Python method uses no run logic or parity prefilter.
   After removing a triple, let R encode the remaining positions. For every
   possible s it tests `R-2^s` for divisibility by `1+2^m`, using a complete
   residue lookup. Quotient H is accepted only if H and H shifted by m are
   disjoint and sum exactly to `R-2^s`. This checks positivity, absence of
   binary carries and the full interval endpoints. Already witnessed s
   values can be skipped; every unwitnessed s remains eligible.

All 344 masks and all triple counts agree. Direct set deletion and
least-element matching, using no bit arithmetic, replay **6,678 witnesses**.
A third recursive matching oracle branches on the partner of the least free
point and agrees with both methods on **344 complete small cases**: all
positive m,d below n for n=7,9,11,13, including equal steps. Four corrupted
placements (duplicate pair, singleton collision, negative start, out-of-range
endpoint) are rejected. All **216 saved interval configurations** retain
their **432 actual source/sink placements**, a positive control without
rerunning their enumeration.

The prior sparse JSON has SHA-256
`4c9ce9bafd676be265d58ee3c22d3489ee30197670246f2cafd77e383f30504a`.
The existing sparse exporter reproduces all proof-source bytes and compares
all 606 preceding decisions in 0.447 seconds. The saved selected-109 checker
also passes all 3,456 negative cycles, the exact computational minimum 109,
120-addition witness replay and seven corruptions:

```
python3 scripts/export_lean_sparse_checks.py --check
python3 scripts/check_clift109_box.py \
  results/2026-10-18-clift109-box-exclusion.json
```

These checks do not supply a Lean proof of enumeration completeness or cap
infeasibility. No completed graph enumeration, full 12509 proof rebuild
without changed inputs, or unrestricted solver is repeated.

## Startup, source versions and validation

The selected theorem-provers environment reaches readiness, then its full
mandatory Start gate passes: exact toolchains, recorded configuration hashes,
clean dependency revisions, readiness receipts and representative imports for
all three targets, including Scholz. Read the published
`/workspace/shared/theorem-provers/START.md`; no applicable AGENTS.md or saved
Start skill is present in this checkout/catalog. No installation, preparation,
receipt fabrication, shared artifact repair or publication occurs.

The clean `work` branch at
`e82b987ed509618e4a94ca25eaff93adc6a3f6f6` equals live and freshly fetched
origin/main. Both ancestry directions are verified before creating tracking
main; the work branch is preserved. Origin is exactly
`https://github.com/solresol/scholz-brauer.git`. The launch's verified catalogue
and GitHub mapping identify repository ID 1368051643. No competing research
process or repository research marker is found; this run holds its own marker.
Only this repository changes; sibling checkouts, shared state, pins and
schedules are preserved.

The latest [weekly handoff](2026-11-06-literature-review.md) is two UTC days
old and is read before selecting this increment, including its HAL/journal
access limits. No new outside theorem or broad literature search is needed.
The primary [Clift account](https://www.additionchains.com/ScholzBrauer.html)
and [selected diagram](https://www.additionchains.com/LargeNonHansen.png) are
accessed **8 November 2026 UTC**. Both hashes match the preceding access.
The account is undated; content hashes identify its version. Exact URLs,
timestamps, byte lengths and hashes are recorded in
`data/2026-11-09-placed-pairs-source-recheck.json`. Only the selected graph and
outgoing cap interpretation are used; the published exclusion is not assumed.

Lean **4.27.0** and mathlib
**a3a10db0e9d66acbebf76c5e6a135066525ac900** are unchanged. Commands use
`prepare.env_for('scholz')`, its archive cache, LEAN_NUM_THREADS=2 and absolute
Lean/Lake binaries returned by `prepare.m.installed_tools`. Costly builds use
the published guarded runner with unchanged 2 GiB disk reserve, 12 GiB
process-group RSS limit and 1,800-second command bound.

The final standalone proof passes in **3.003 guarded seconds**. The full
pinned `lake build` passes **1,153 jobs in 5.060 seconds**.
`lake env lean Audit.lean` passes **365 entries in 19.054 seconds**;
`verify_integration.check_axioms` verifies exact audit-entry order and permits
only propext, Quot.sound and Classical.choice. This includes all three new
public theorems and their transitive dependencies. No placeholder,
project-defined axiom, native decision shortcut or assumed target occurs.
An initial shadowed hypothesis name caused a local elaboration error and
was corrected before the successful checks; no mathematical premise changed.
Reviewed pin hashes, exact clean dependency HEADs, published deployment
integrity and all five vendored source hashes pass.

Build/audit transcripts and input hashes are in
`2026-11-09-placed-pairs-build.txt`, `2026-11-09-placed-pairs-audit.txt` and
`2026-11-09-placed-pairs-verification.json`. Full integration is not repeated:
the unchanged chain-9 checker previously timed out at 180 seconds and this
increment does not address it. That result remains inconclusive. No remote
CI success is claimed.

## Next obligation

Kernel-check the finite placement rejection, or use its proved necessary
predicates directly with the box and actual source/sink coordinates. Then
combine both odd-run restrictions, twelve critical families and 64 orientations
to finish interval/cap classification. The top-pinned branch through 8 and
the branch missing 8 (which visits 5,7,15) remain separate. Matching the
singleton alone does not supply compatible halves or feasible cap constraints.
