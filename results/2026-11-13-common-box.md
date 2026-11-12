# Common boxes and a compatibility gap — 13 November 2026, Sydney

Authorized invocation: 12 November UTC / Friday 13 November Sydney.
Active obligation: Lean exclusion of every 108-doubling labelling of Clift's
selected 109 graph. Its exact minimum 109 remains computational.

**Two independent complete box counts reduce the necessary ordered-pair
domain from 278 to 246 computationally. Six new Lean theorems exhibit why
common boxes and actual exception placements still do not suffice.**
The kernel-checked necessary domain remains 278; the 32 new removals have
not been formalised. The full selected-109 exclusion remains open.

## Exact bounded computation

The existing Lean results imply a six-dimensional dissociated positive box
`t + SS(u,v,w,d1,d2,d3)` inside `[0,108]`, and at most seven odd arithmetic
runs in its complement at each of steps u and d1. We enumerate just this
necessary common-box condition, without repeating the completed interval
configuration search or cap optimisation.

The C++ driver reuses `Enumerator` and `odd_runs` from the existing box
search. The independent Python pass reuses the other subset-sum generator,
reconstructs subset sums by combinations, and counts maximal arithmetic runs
by set membership, rather than pair peeling. They agree on all per-pair
counts over **31,048 distinct six-difference sets and 263,256 set/offset
choices**. All 278 input pairs fit some box before the odd-run tests; exactly
246 pass both. All 246 also have a top-pinned box. This latter count concerns
only the box relaxation, not feasibility of the critical branch through 8.
The branch missing 8, which must visit 5,7,15, remains separate.

For `(2,3)`, packing alone gives 23,065 boxes; both odd-run tests leave
5,982, including 505 pinned at 108. Every one of the saved 216 complete
interval configurations passes the refinement. The removed pairs and every
per-pair count are in `2026-11-13-common-box.json`.

Reproduce from the repository root with an unused output path:

```bash
python3 scripts/experiment_clift109_common_box.py --output /tmp/common-box.json
```

Python 3.12.14, g++ C++17, standard library only, no random seed. The total
bound is 180 seconds; compilation has 30 seconds and C++ enumeration 60.
The final successful run takes **8.920 seconds**, including both algorithms,
saved-configuration checks, direct witness replay and three corruption controls.
Exact compiler flags, timings, input hashes and bounds are in the JSON.
An initial successful run predates the extra half-mismatch theorem and is
preserved separately; the final report hashes the final proof source.

## Kernel-checked obstruction to the relaxed strategy

In coordinate order `(u,v,w,d1,d2,d3,t,p,q,A1,A2,A3)`, take

```
(2,16,8,3,4,32,0,-63,2,129,132,64).
```

The box is the 64 distinct subset sums of `{2,3,4,8,16,32}`, with span 65.
The SAME tuple supplies both actual exception multisets and singleton 1:

- Source exceptions: three 3-pairs starting at 64,68,66, plus 1.
- Sink exceptions: three 2-pairs starting at 66,82,69, plus 1.

Both fit the SAME 45-point box complement. Each complement after deleting its
seven exceptions has the required unique nineteen-weight half at its regular
step, 2 or 3. `Clift109CommonBoxExample.lean` kernel-checks these two exact
109-point multiset partitions, box dissociation, the consequent two odd-run
bounds, mismatch with BOTH prescribed halves, and failure of the full coordinate
interval equation. The arbitrary halves are explicit private fixtures, not
new definitions of `sourceHalf` or `sinkHalf`.

This is a counterexample to sufficiency of that intermediate relaxation,
not a graph labelling, a counterexample to Scholz, or a feasible cap assignment.
For example its A1=129 already leaves the interval. The decisive remaining
condition is compatibility with the prescribed nineteen-weight shapes.

A bounded single-algorithm exploratory probe also scans all 5,982 boxes for
`(2,3)`. It finds 4,633 passing both independent placements at a common
singleton, and 4,235 after requiring distinct v and d2 roles among the other
four box dimensions. This count has no independent count or Lean enumeration
theorem; the explicit Lean witness, rather than the count, certifies the gap.
Reproduce by compiling `scripts/probe_clift109_common_placements.cpp` with
`g++ -O3 -std=c++17 -Wall -Wextra -Werror` and running the resulting binary.
The 120-second bound, compiler command, source hashes and measured runtime
are in `2026-11-13-common-placements-probe.json`. Preliminary temporary
drivers had two compiler warning failures; corrected drivers pass with
warnings treated as errors. No timeout or failed compilation is an exclusion.

## Validation and sources

The mandatory full published Start gate passes for all three projects before
research. Read `/workspace/shared/theorem-provers/START.md`; no applicable
AGENTS.md or executor Start skill is available. Personal Context reports
unavailable. Only this checkout changes. The shared runtime, siblings and
dependency sources are read-only; no installation or preparation is performed.

Clean work, fetched origin/main and live main initially equal
`c5fa59e8faaf519785003049824527dcded639ff`. Equal ancestry is verified before
creating tracking main, preserving work; an exclusive local research marker
is acquired after checking for competing research processes and markers.
Origin is `https://github.com/solresol/scholz-brauer.git`.

The latest committed weekly handoff is 6 November, six UTC days old; it is
read before choosing work, with its HAL/publisher full-text access limitations.
No new outside theorem or broad literature search is used.
[Clift's primary account](https://www.additionchains.com/ScholzBrauer.html)
and [selected diagram](https://www.additionchains.com/LargeNonHansen.png) are
accessed 12 November UTC: both SHA-256 hashes match prior access. All sixteen
published 5,784,689 chains match the saved ordered lists and are freshly checked
as increasing 27-addition witnesses. The eleven selected-109 parent sums also
check; the diagram's prior visual reconstruction is reused because the image
viewer fails with `exec-server transport closed`. No fresh visual inspection,
source optimum or published exclusion is assumed. Versions, URLs, timestamps,
hashes and boundaries are in `data/2026-11-13-common-box-source-recheck.json`.

The absolute pinned Lean/Lake 4.27.0 tools and `prepare.env_for('scholz')`
are used with the isolated archive cache and LEAN_NUM_THREADS=2. Guarded builds
retain the 2 GiB reserve and 12 GiB process-group RSS limit; this small build
and audit each have a stricter 300-second timeout. The full build passes
**1,176 jobs in 7.010 guarded seconds**. The audit passes **429 entries in
22.017 seconds**, including all six new theorems and transitive dependencies,
with only propext, Quot.sound and Classical.choice. One pre-existing generated
unused-simp warning remains. No placeholder, project axiom, native decision
shortcut or assumed target is introduced. Lean/mathlib and manifest pins stay
unchanged. Build/audit logs and exact commands are saved beside this result.

The prior alternating exporter reproduces all generated bytes and the
278-pair input domain. The saved selected-109 regression passes all 3,456
negative cycles, the 120-addition witness replay and seven corruptions.
It checks saved cases; enumeration completeness and the exact optimum remain
computational. No whole-integration or remote-CI success is claimed.

## Next obligation

Kernel-certify the 32 common-box removals if useful, and join actual
exceptions to the prescribed source/sink halves, twelve critical families,
64 orientations and signed gauge/cap constraints. Matching singleton, box
and actual exceptions alone is insufficient. No claim of `min(u,d1)=1`,
feasibility, full exclusion or a new Scholz instance follows.
