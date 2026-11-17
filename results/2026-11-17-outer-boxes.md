# Complete outer box-role coverage — 17 November 2026 UTC

Active obligation: Lean exclusion of every 108-doubling labelling of Clift's
selected 109 graph. Its exact minimum 109 remains computational.

**Complete outer INPUT coverage is now proved.** Every original budget-108
labelling reaches a finite generated box-role branch and the existing actual
sink-position/full-shape classifier. The outer branches' interval outputs and
cap systems are not yet completely kernel classified. Necessary pair domains
remain 278 kernel-checked / 246 computational; no pair is removed, no additional
box is cap-excluded, and no new Scholz instance follows.

## What is proved

`Clift109OuterBoxes.lean` reuses the existing natural `subsetSums`, box
constraints, minimum coordinates and sink classifier. Its generic recursive
`dissociatedDimensions n lower budget` enumerates sorted dimension lists.
The next dimension d ranges from lower to floor(budget/n); the suffix has
the remaining budget and lower bound d. Repeated subset sums are rejected
at every stage, with multiplicities preserved. `mem_dissociatedDimensions`
proves an exact iff with length n, sorted order, lower bounds, total span and
subset-sum dissociation. The division pruning has a proved lower-span bound.

`subsetSums_perm` proves equality under any dimension permutation. Sorting
therefore retains every positive dissociated six-box, and the accompanying
permutations retain every ORDERED role assignment. The original box-pair
order is `(d1,d2,d3,w,v,u)`, not numerical order. `boxRolePrototype` restores
these roles, and `outerBoxRolesAt` retains every translation
`0 <= t <= 108 - sum(dimensions)`. Soundness proves that generated inputs
have exactly the required box conditions. No saved fixture list is assumed.

`minimumCoordinates_same_outer_box` identifies the seven minimum coordinates
with the original natural gap/offset readout. `outer_sink_coverage_of_budget`
then routes every hypothetical original budget-108 labelling into a generated
outer branch, its ACTUAL sink positions, and `sinkIntervalAnchors` with the
prescribed nineteen-weight half. The stronger
`pruned_outer_sink_coverage_of_budget` retains the already kernel-checked
278-pair filter and BOTH odd-run restrictions on that same box.

`outer_critical_branch_of_budget` carries the twelve critical families to any
covered box. It retains the weight-108 path, saturated caps on its edges and
zero caps away from it. A path visiting 8 forces the translated box span to
equal 108; the branch missing 8 explicitly retains 5,7,15. The existing
`oriented_cap_constraints` still transports the same original cap function
to one of all 64 signed orientations and an endpoint-fixed integer gauge.
No independent relaxed half or unproved 246-pair domain is substituted.

`Clift109OuterBoxChecks.lean` kernel-evaluates two small dimension domains and
checks that the earlier completely classified ordered box is retained with
w=4 and d3=8. Thirteen new public theorems and their private dependencies are
included in the fail-closed axiom audit. No placeholder, project-defined axiom,
native acceptance of a theorem, or assumed exclusion is introduced.

## Bounded exact checks and remaining scale

The new suffix-recursion Python driver agrees on its ENTIRE dimension output
with the existing independent prefix bit-popcount generator: **31,048** sets.
Every one of the 64 subset sums of every output is also explicitly replayed.
There are **263,256** set/translation pairs. Lean `#eval` independently returns
31,048 in **159.303 guarded seconds**; this is computational evaluation,
not a kernel cardinality theorem. Its generator definition is unchanged in
the final source; the module subsequently gained proof declarations only.

All permutations give 189,544,320 ordered role inputs. Applying the checked
278-pair domain leaves 60,622,992, computed afresh from the complete dimension
domain and matched against the saved independently checked packing counts.
The saved common-box counts further project to 7,749,936 ordered role inputs
passing both odd-run bounds, or 984,480 top-pinned inputs. Those odd-run counts
were NOT rerun here. They identify the scale of remaining certification,
not feasible labellings or a kernel-checked 246-pair reduction.

All 216 saved coordinate fixtures, representing 48 ordered role inputs,
belong to the complete outer domain. This membership check does not prove
that they exhaust its interval outputs. The unchanged graph regression
separately checks all 3,456 negative cycles, its 120-addition replay and seven
corruptions; it does not promote enumeration completeness or global optimality.

Reproduce the new bounded check at an unused output path:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 scripts/experiment_clift109_outer_boxes.py --output /tmp/outer-boxes.json
```

Bounds: six positive dimensions with total at most 108, all allowed
translations, and 278 input pairs. Python 3.12.14, standard library and the
existing project module, no seed, 90-second bound; **9.153 seconds** for the
saved run. The JSON records commands, input hashes, output digest, timings
and scope. Existing-output refusal is checked and preserves the bytes.

## Environment, sources and verification

Work is confined to `/workspace/scholz-brauer`, origin
`https://github.com/solresol/scholz-brauer.git`. Clean `work`, fetched and live
main all equal `587fd0e21d5e23e84849f284b038ede18d2f8726` at entry. Ancestry
is equal and the ff-only merge is current. No competing research process or
research marker is found; an exclusive checkout-local marker protects this
run. Read published START.md; no applicable AGENTS.md or checkout-local
`.agents/skills` exists. The full startup gate passes for all three projects.
This run starts 17 November UTC / Wednesday 18 November Australia/Sydney;
the weekday preference is secondary to the identified coverage obligation.

Reuse installed absolute Lean/Lake 4.27.0 and `prepare.env_for('scholz')`, two
threads, isolated archive cache, 2 GiB reserve and 12 GiB process-group RSS
guard. A missing exact-pinned `Mathlib.Data.List.Permutation` object is built
in THIS checkout only (502 jobs, 6.013 guarded seconds); no dependency
revision, toolchain, Lake configuration or manifest changes. New modules
build in 13.020 guarded seconds. Final full incremental build: **1,189 jobs,
5.008 guarded seconds**. Fail-closed audit: **492 entries, 39.055 seconds**,
only propext, Quot.sound and Classical.choice, including all thirteen new
public theorems and transitive dependencies. Only the old generated simp
warning remains. Early elaboration/API errors are corrected before these
checks; no timeout or failed check establishes a mathematical conclusion.

Read the 13 November weekly human literature checkpoint, four UTC dates old,
retaining its HAL/publisher access limits. No external theorem is relied on
and no broad literature search is repeated. Fresh access on 17 November to
[Clift's primary page](https://www.additionchains.com/ScholzBrauer.html) and
[selected diagram](https://www.additionchains.com/LargeNonHansen.png) matches
the previous hashes. The existing graph reconstruction is reused without
claiming fresh visual inspection. All eleven selected parent sums check;
all sixteen published ordered 5,784,689 chains match the archive and pass
fresh strict 27-addition witness checks. No published optimality is assumed.
URLs, content versions/hashes, access date and claim limits are recorded in
`data/2026-11-17-outer-boxes-sources.json`.

No sibling checkout, published shared runtime, environment setting,
credential, schedule or user-machine change. No whole-integration or remote-CI
claim. Build/audit logs and final source/pin/dependency verification accompany
this result.

## Next obligation

Kernel-certify pruning/evaluation of the staged complete outer domain and
its remaining sink-position/classifier outputs, then their signed cap systems.
Preserve the prescribed source/sink halves, both odd-run restrictions,
twelve critical families, all 64 orientations and the two critical branches.
The 32 common-box pair removals still need kernel certification if used.
Saturated-residue pruning does not apply below seven odd residues; the
small-step compatibility problem, including (2,3), remains open. Complete
input coverage supplies the missing coverage theorem, not the much smaller
48-input fixture list or a proof of the selected-109 exclusion.
