# Complete fixed-box positions and cap exclusion — 16 November 2026 UTC

Active obligation: kernel exclusion of every 108-doubling labelling of Clift's
selected 109 graph. Its global exact minimum 109 remains computational.

**Actual sink-position coverage is now proved for every fixed box, and one
complete box-role subclass is excluded including all orientations and gauges.**
The fixed roles are `(u,v,w,d1,d2,d3,t)=(1,2,4,51,23,8,0)`; their order matters.
This is a local exclusion, without a pair removal or complete outer box
classification. Necessary pair domains remain 278 kernel-checked / 246
computational. No new Scholz instance or universal lift follows.

## Coverage and the additional residue argument

`Clift109SinkPositions.lean` proves that every interval tuple at fixed seven
box roles reaches `sinkPositionChoices` at its ACTUAL positions
`r=A1+p`, `s=A2+p`, `z=A3+p`. The prototype's other five coordinates may be
arbitrary. Positive d1 is required by the full-shape classifier; the position
bounds come from the interval equation rather than a fixture assumption.

The staged list enumerates rectangle starts, then u-pair starts, then the
singleton. Each subtraction follows a multiset inclusion check, retaining
multiplicities. Both the box and the prescribed sink half are paired at d1,
so the existing alternating signed fingerprint constrains the singleton.
The full nineteen-weight classifier remains the acceptance test.

A further proved restriction makes the concrete kernel evaluation practical:
if the seven exceptional weights must supply seven odd residues, EVERY
exception lies in one of those residues. More generally, an arbitrary integer
multiset whose odd-label count equals its cardinality has no label outside
its odd-label set. This proof permits multiplicities and signed weights.
It imposes no additional filter when the interval has fewer than seven odd
residues. The original budget-108 labelling is transported through both filters.

Exact halving also proves that two interval tuples with the same box roles,
actual positions and anchor must be equal. This turns a finite record
classification into a classification of the entire coordinate tuple.

## Exact classification and cap exclusion at one box

For the fixed roles above, the interval has odd residues 0..6 modulo 51.
The residue restriction leaves four rectangle starts, 102..105, from the 33
structurally valid starts. All actual positions reduce to six inputs:

| r | s | z | accepted A3 |
|---|---|---|---|
| 102 | 106 | 108 | none |
| 102 | 107 | 106 | 20 |
| 103 | 107 | 102 | 16 |
| 104 | 102 | 108 | 22 |
| 105 | 102 | 104 | 18 |
| 105 | 103 | 102 | none |

`mem_sinkPositionCompletions_iff` proves that an arbitrary tuple with these
seven roles solves the interval equation iff it is one of four explicit
coordinate tuples. All four listed tuples are independently kernel checked
as interval witnesses. This covers every actual position and anchor, rather
than just the previously saved fixture.

Four `Clift109SinkPositionCapChecks*.lean` proofs then exclude every one of
the 64 signed orientations of each tuple, every integer gauge with endpoints
pinned at zero, and every natural cap allocation with total at most 108.
The proofs instantiate all eleven selected parent pairs (22 edges), retaining
both nonnegativity and upper-cap inequalities, and use kernel-checked linear
arithmetic. They use the existing oriented gauge/cap transport. No assumption
about a critical-family enumeration, saved negative cycle or external solver
result is needed for this stronger fixed-input linear system.

`sink_position_box_no_budget` transports the result back to the original
natural labelling. Thus all budget-108 labellings with these minimum box
roles are excluded. The box top is 89; this local proof does not identify the
top-pinned branch with the branch missing 8. Other boxes with pair (1,51),
the swapped w/d3 roles, and all other necessary pairs remain separate inputs.

## Bounded exact experiment

The new driver scans every structurally valid rectangle/pair/singleton
placement at the 48 saved box-role inputs and the relaxed (2,3) example's box:
**1,157,247 placements** in total. Comparing the pruned scan with the scan
without either residue/fingerprint filter recovers exactly the 216 saved
interval configurations at their 48 role choices, with no additional tuple
at those choices. The relaxed example has no interval completion at ANY
actual positions for its fixed roles; this last all-position assertion is
computational, not kernel checked. It has 1,089 surviving fingerprint inputs.

The two scans share the existing full-shape classifier. They are not two
independent acceptance algorithms. General position coverage and the
fixed-input classifier's exact iff are separately proved in Lean. The list
of 48 boxes is a bounded input, not an assumption of global box completeness.

Reproduce from the repository root using an unused output path:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 scripts/experiment_clift109_sink_positions.py --output /tmp/sink-positions.json
```

Bounds: target interval 0..108, every disjoint seven-point exception shape in
the 45-point complement, 49 fixed role inputs. Python 3.12.14, standard library
and existing project modules only; no seed; 120-second bound; **26.078 seconds**.
The JSON records exact command, source hashes, position counts/digests and all accepted
tuples. The saved graph checker separately revalidates 3,456 negative cycles,
the 120-addition witness, and rejection of all seven corruptions. Neither
regression promotes global enumeration or optimality to a kernel theorem.

## Resource obstacles and verification

The first monolithic position evaluation hit the unchanged 12 GiB process-group
RSS guard after approximately 104 seconds (from log timestamps). Splitting
rectangle branches, then reifying the common 45-point remainder, each still
hit a 300-second bound. These non-retained intermediate attempts are
inconclusive; their exact commands/errors are retained in the stopped logs.
The saturated-residue lemma reduces the actual search before evaluation;
the complete revised position module compiles in 16 seconds.

The combined 256-case cap command also hit its 300-second bound. Four separate
64-orientation proof modules keep each check under that same bound, without
changing the resource limits. No timeout or guard rejection is an exclusion.
Final build, individual cap builds, fail-closed axiom audit and verification
manifest are recorded alongside this report. There are twenty new public
theorems, including their kernel-checked private dependencies; no placeholder,
project axiom, native acceptance or assumed target is used.

The final incremental build passes **1,186 jobs in 4.003 guarded seconds**;
all new proof modules were compiled successfully beforehand. The four cap
batches take **108.074, 105.062, 106.074 and 104.085 seconds**, and their composed
transport module takes **4.005 seconds**. The fail-closed audit passes all
**479 entries in 28.349 seconds**, using only propext, Quot.sound and
Classical.choice, including all new public theorems' transitive dependencies.
Only the pre-existing generated unused-simp warning remains.

Reproduce Lean checks using the existing published guarded runner:

```python
import sys
from pathlib import Path
sys.path.insert(0, '/workspace/shared/theorem-provers')
import prepare
root = Path('/workspace/scholz-brauer/lean')
env = prepare.env_for('scholz')
lean, lake = prepare.m.installed_tools(
    prepare.B / 'runtime', 'leanprover/lean4:v4.27.0', env)
for i in range(4):
    prepare.m.run([str(lake), 'build',
        f'ScholzBrauer.Clift109SinkPositionCapChecks0{i}'],
        root, env, (root, prepare.B), timeout=300)
prepare.m.run([str(lake), 'build'], root, env, (root, prepare.B), timeout=300)
prepare.m.run([str(lake), 'env', str(lean), 'Audit.lean'],
    root, env, (root, prepare.B), timeout=300)
```

Work stays in `/workspace/scholz-brauer`, origin
`https://github.com/solresol/scholz-brauer.git`. Read published START.md; no
applicable AGENTS.md exists. Clean `work`, fetched origin/main and live main
start at `2ee054076c137817a15bb22f5a0cffac95321179`; ancestry and the ff-only
update are checked. No competing local research process/marker is found;
an exclusive checkout-local marker protects the run. The complete published
startup gate passes for all three projects before Lean. Absolute installed
4.27.0 Lean/Lake binaries, `prepare.env_for('scholz')`, two Lean threads,
isolated Scholz cache, 2 GiB disk reserve and 12 GiB RSS guard are reused.
Exact toolchain, mathlib, manifest and Lake pins remain unchanged.

Read the 13 November weekly human literature checkpoint, three UTC dates old,
retaining its HAL/publisher full-text limitations. No external theorem is used
and no broad search is repeated. Clift's undated
[primary page](https://www.additionchains.com/ScholzBrauer.html) and
[selected PNG](https://www.additionchains.com/LargeNonHansen.png), accessed
16 November, match the previous hashes. Reuse the existing graph reconstruction
without claiming fresh visual inspection. All eleven selected sums check;
all sixteen published 5,784,689 chains match the archived ordered lists and
pass strict 27-addition witness checks. Published optimality is not assumed.
The dated source record retains URLs, version hashes and access time.

No sibling checkout, shared runtime, environment, credentials, security setting,
schedule or user machine is changed. No whole-integration or remote-CI claim.

## Next obligation

Prove complete OUTER box-role coverage, then kernel-check the remaining
position/classifier inputs and their cap systems. The new general position
coverage removes the actual-position part of that coverage obligation, not
the box-role part. The 32 computational common-box removals still need kernel
certification if used. Keep both prescribed halves, box dissociation, both
odd-run bounds, 278-pair domain, twelve critical families and 64 orientations;
keep the branch through 8/top 108 separate from the branch missing 8 through
5,7,15. Saturated-residue pruning is inactive for steps with fewer than seven
odd residues, so the small-step compatibility problem, including (2,3), remains.
