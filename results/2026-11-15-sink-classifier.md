# Fixed-box sink interval classifier — 15 November 2026 UTC

Active obligation: Lean exclusion of every 108-doubling labelling of Clift's
selected 109 graph. Its exact minimum 109 remains computational.

**A complete finite classifier now settles the interval equation for fixed
box roles and actual sink exception positions.** Seventeen new public Lean
theorems include its soundness, completeness, at-most-two anchor bound,
transport from original budget-108 labellings, and three concrete checks.
The full exclusion remains open. Necessary pair domains stay at 278
kernel-checked and 246 computational; no pair is removed by this run.

## Exact local classification

Fix the seven coordinates `u,v,w,d1,d2,d3,t`, retaining their roles, and the
actual sink exception positions `r=A1+p`, `s=A2+p`, `z=A3+p`. The exceptional
multiset is the four-point u/v rectangle based at r, the u-pair based at s,
and the singleton z. The existing `halve` recovers the unique candidate
nineteen-weight half H from the interval minus box and exceptions.

`sinkIntervalAnchors` first checks that the box, translated double of H,
and exceptions partition the full interval with multiplicities. This
explicit check prevents truncated multiset subtraction from hiding excess
weights. For each anchor in H, the existing `reconstructSink` recovers p,
q,A1,A2,A3; acceptance requires the full multiset `sinkHalf c = H`.
Moment equality alone is insufficient for acceptance.

For `d1>0`, `mem_sinkIntervalAnchors_iff` proves the exact equivalence:

```
a is accepted iff there exists a coordinate tuple c with
  the fixed seven box coordinates,
  A1+p=r, A2+p=s, A3+p=z, A3=a,
  and coordinateWeights c = {0,...,108}, with multiplicities.
```

Soundness needs no positivity or dissociation hypothesis. Completeness
requires only positive d1 in addition to the stated interval equation and
matching box roles. The earlier two-moment theorem proves that the exact
shape filter, hence this interval classifier, retains at most two anchors.
Every accepted anchor satisfies `0<=a` and `a+d1<109`.
`sink_classifier_of_budget` transports coverage and the cardinality bound
to every original natural labelling under the existing graph, seed,
terminal M109, outgoing-cap and budget-108 hypotheses.

Two concrete classifier evaluations use `decide +kernel`. The saved tuple
`(1,2,4,51,23,8,0,86,28,18,16,22)` at positions `(104,102,108)` returns
exactly `{22}`. It is an interval fixture, without cap feasibility.
For the earlier relaxed common-box example at `(66,69,1)`, the classifier
returns the empty set. `common_box_gap_no_interval_completion` excludes
EVERY tuple sharing those box roles and actual positions, including a
different anchor; this strengthens the prior mismatch of one prescribed
tuple. It is a local exclusion, without excluding all inputs for `(2,3)`.

## Bounded computational checks

The new fixture driver recovers all 216 saved interval configurations,
one anchor each, without repeating outer box/exception enumeration.
All 648 partition corruptions are rejected: out-of-interval singleton,
excessive box translation, and repeated exception pair.

For three fixed inputs (the positive fixture, the relaxed example, and an
invalid singleton), a separate direct algorithm scans anchors `0..108`
and q `-108..108`, constructing every full 109-weight coordinate multiset.
It uses neither halving nor moment recovery. Each input checks 23,653
coordinate pairs, with exact agreement on the entire accepted tuple list.
For an interval tuple, A3 and A3+q lie in the prescribed half, explaining
these comparison bounds. This comparison does not prove outer coverage.

Reproduce from the repository root at an unused output path:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 scripts/experiment_clift109_sink_classifier.py --output /tmp/sink-classifier.json
```

Python 3.12.14, standard library and existing project modules only, no seed,
60-second bound; runtime **1.147 seconds**. The fixture JSON records input
bounds, command, versions, source hashes, anchors and direct comparisons.
The unchanged saved graph regression also checks all 3,456 negative cycles,
the 120-addition witness, and seven corruptions. Saved-case checking does
not promote its computational enumeration completeness or optimum to Lean.

## Environment, source review and verification

Work stays inside the selected published theorem-provers machine and
`/workspace/scholz-brauer`, whose origin is
`https://github.com/solresol/scholz-brauer.git`. Read published START.md;
no applicable AGENTS.md is present. Clean `work`, fetched origin/main and
live main initially equal `2e9f5b5693abb125e2c5ace067106b6bcf469690`.
Ancestry is verified; the fast-forward-only update is already current.
No competing local research process or marker is found; an exclusive
checkout-local research marker protects this run's edits.

The full published startup gate passes for all three projects before Lean.
Installed absolute Lean/Lake 4.27.0 binaries and `prepare.env_for('scholz')`
preserve the exact toolchain/mathlib/Lake/manifest pins, isolated Scholz
archive cache, two Lean threads, 2 GiB reserve, and 12 GiB process-group RSS
guard. Final build and audit each have a 300-second bound. The full
incremental build passes **1,179 jobs in 3.003 guarded seconds**; the new
modules were compiled successfully before this final recorded build.
The fail-closed audit passes **459 entries in 34.048 seconds**, including
all seventeen new public theorems and their transitive dependencies, using
only propext, Quot.sound and Classical.choice. No placeholders,
project-defined axiom, native acceptance or assumed target is introduced.
Only the pre-existing generated unused-simp warning remains.

Read the 13 November weekly literature checkpoint, two UTC days old,
retaining its HAL/publisher access limitations. No external theorem is
used and no broad literature search is repeated. Clift's undated
[primary account](https://www.additionchains.com/ScholzBrauer.html) and
[selected diagram](https://www.additionchains.com/LargeNonHansen.png) are
accessed 15 November UTC; both content hashes match the previous source
record. Reuse the existing diagram reconstruction without claiming a new
visual inspection. All eleven selected parent sums check, and all sixteen
published 5,784,689 chains match the archived ordered lists and pass fresh
strictly increasing 27-addition witness checks. Published optimality or
exclusion is not assumed. The dated source JSON records URLs, versions,
hashes, access timestamp and scope.

No sibling, published runtime, environment configuration, credential or
schedule is changed. Build/audit logs and verification hashes accompany
this result. No whole-integration or remote-CI success is claimed.

## Next obligation

Prove complete coverage of the OUTER box-role/actual-sink-position inputs,
then kernel-check their surviving local classifier outputs and apply the
existing signed gauge/cap constraints, twelve critical families and 64
orientations. The full coordinate interval equation retains both prescribed
halves through its proved factorizations; no unrelated source half can
replace it. Preserve both odd-run restrictions and the 278-pair necessary
domain. The 32 common-box removals need kernel certification if used.
Keep the top-pinned branch through 8 separate from the branch missing 8,
which visits 5,7,15. The fixed-input iff supplies no outer enumeration
completeness, cap feasibility, `min(u,d1)=1`, or new Scholz instance.
