# Reuse obstructs the two-detour extension on Clift's 109 graph

8 October 2026, Thursday, Australia/Sydney (AEDT). Milestone 3.
Milestones 1 and 2 and the one-gap family were complete at `2c12087`.

## Mathematical result and its boundary

For the selected parent graph below, allow arbitrary positive bases at vertices
5 and 7, while keeping every other base equal to `M(v)=2^v-1`. Allow every
nonnegative edge shift, subject to carry-free sums and the target `M(109)`.
The exact minimum sum of outgoing shift caps is **110**, exceeding the desired
**108**. There are 2,304 labellings, modulo swapping parallel equal-parent
edges; eight attain 110, all with the ordinary bases `B5=31`, `B7=127`.
Independent replay verifies their 121-addition allocations.

Thus the hypothesis that freeing the two detour bases suffices to recover the
108-doubling budget is **false**. Any successful labelling of this selected
graph must also change at least one of the other bases. This does not exclude
all labellings of the graph, let alone disprove Scholz.

Lean proves a structural reason the detours cannot retain arbitrary bit patterns:
under these fixed surrounding bases, **B5 must be `31*2^k`, `0≤k≤10`, and B7
must be `127*2^k`, `0≤k≤8`**. It also proves the standard Mersenne-orientation
minimum 110 and the specific failure of the earlier one-gap repair at its reuse.
The minimum over the larger two-exception domain is an exact Python result;
its enumeration soundness is not formalised in Lean.

## Primary graph and the alternate-parent distinction

[Clift's primary notes](https://www.additionchains.com/ScholzBrauer.html), live
undated page, and the [109 diagram](https://www.additionchains.com/LargeNonHansen.png)
were retrieved and inspected on 8 October 2026. The unmodified diagram and
retrieval hashes are retained in `data/2026-10-08-clift109*`.
The selected source graph is:

| Vertex | Selected parents |
| --- | --- |
| 2 | 1 + 1 |
| 4 | 2 + 2 |
| 5 | 4 + 1 |
| 7 | 5 + 2 |
| 8 | 4 + 4 |
| 15 | 8 + 7 |
| 23 | 15 + 8 |
| 28 | 23 + 5 |
| 51 | 28 + 23 |
| 58 | 51 + 7 |
| 109 | 58 + 51 |

All source sums were checked, including every alternative parent pair. The sole
alternative is **8=7+1**. With it, the same value sequence is a star source and
admits an all-marked Hansen certificate; both facts are kernel checked. Its
ordinary star lift independently replays in 119 additions. No claim that this
11-step source is optimal, or that 119 is the Scholz bound at 109, follows.

The diagram's selected graph has no Hansen marking: doubling 4 to 8 requires
4 to remain the latest marked parent, but the intervening selected sum 7=5+2
cannot use 4. Lean checks the incompatible anchor requirements for every
marking of the prefix through 7. The graph must not be described as a source
value sequence that admits no Hansen marking. The earlier derivative example
on Clift's page explicitly selects 8=7+1 and is a different parent graph.

Clift reports a stronger obstruction for arbitrary edge labellings with distinct
path sums 0..108 and a critical path. That full claim remains a literature claim
here; it is neither assumed nor established by this run. No novelty or priority
claim is made.

## Structural proof in Lean

`Clift109.detour_bases_rigid` uses four equations with arbitrary natural shifts:

```
B7  = 2^a B5 + 2^b M(2)
M15 = 2^c B7 + 2^d M(8)
M28 = 2^e B5 + 2^f M(23)
M58 = 2^g B7 + 2^h M(51).
```

Positivity gives `B5≤B7≤M15`. The last two equations make each detour base a
power-of-two divisor of the complement of a shifted contiguous Mersenne block.
Exhausting the possible block shifts, with bounds proved from the equations,
shows that only shifted M5 and M7 fit below M15. This is a theorem for arbitrary
positive integer bases and all nonnegative shifts, not extrapolation from a
bounded base test. It needs neither a carry-free assumption nor a budget bound.
The finite kernel checks range over `Fin 28 × Fin 6` and `Fin 58 × Fin 8`;
quotient/remainder identities transport their conclusions back to the bases.

The earlier family at `A=4,B=2` constructs `B5=121`, then `B7=127`. Lean proves
that `121*2^a + M23*2^b ≠ M28` for all naturals a,b, so the repaired base cannot
survive its later use at vertex 28 while 23 and 28 retain their Mersenne bases.
The proof bounds both shifts before its finite kernel check. It does not infer
impossibility from a timeout or an arbitrary search cutoff.

The eight Boolean arguments of `mersenneCaps` cover all 256 standard Mersenne
orientations; the three parallel-edge choices do not affect caps. Lean proves
their cap sum is at least 110, with equality attained. This theorem is explicitly
about standard orientations, not all arbitrary base choices.

## Complete restricted enumeration

`scripts/experiment_clift109.py` uses Python exact integers and the standard
library. No random seed or solver is used in the completed experiment.

1. Since `M28 = 2^a M23 + 2^b B5`, a is in 0..5. Subtract the known term and
   divide the positive remainder by every power of two dividing it exactly.
   This yields **28** possible B5 values, including even bases.
2. The analogous equation at 58 gives a in 0..7 and **58** possible B7 values.
   These domains cover every solution of those equations, irrespective of cost.
3. Check all **1,624** base pairs against every local sum. A positive shifted
   term is no greater than its child, so its shift is below the child's bit
   length. Enumerate the first shift and recover the second by exact division,
   checking a power-of-two quotient and bitwise disjointness. There are **63**
   viable base pairs, yielding **2,304** complete labellings.
4. Independently produce B5 from M4 and 1 with shifts in 0..27, and B7 from B5
   and M2 with shifts in 0..57. Check both later uses of B7 and the use of B5
   at 28. The **87,464** B7 production checks recover the same 63 pairs.
   Independent nested enumeration of both shifts agrees on all their local
   label lists; it does not use the division-based local-pair generator.
5. Enumerate every Cartesian product of local choices and take exact outgoing
   maxima. Costs range from **110 to 192**. All eight minima have B5=M5 and
   B7=M7. Sort each minimum's allocation and pass it to the existing independent
   summand-index checker; each yields 121 additions with endpoint M109.

The enumerated objective is the sum of outgoing caps. With the 11 source
additions it gives 121 at minimum. For a graph with 109 distinct path sums
0..108, a critical path would have weight 108 and collect every cap; hence it
would require cap sum 108. The restricted minimum excludes that possibility
in this family. It is not the minimum over all addition chains for M109.

The original alternate-parent star graph provides a separate 119-addition
witness. Its existence is consistent with the obstruction for the selected
graph and demonstrates why parent choices must remain explicit.

Saved experiment: Python 3.9.6, **0.276683 seconds**, no random seed.
`2026-10-08-clift109-checks.json` contains full domains, viable pairs, cost
histograms, minimum labels/caps and ordinary certificates.

## Failed broader approaches and changed strategy

Two deliberately bounded probes of arbitrary labellings returned `unknown`
with reason `timeout` using Z3 4.15.3.0 and seed 0:

- Integer path weights: 109 terminal expressions, all distinct in 0..108,
  nonnegative edge labels bounded by source caps summing to 108; **30.044365s**
  with a 30,000ms solver limit.
- 109-bit node supports and disjoint shifted summands, terminal all ones,
  zero-extended cap sum 108; **60.068868s** with a 60,000ms limit.

Exact probe source, commands and encodings are retained in
`2026-10-08-clift109-probes.json`. The temporary dependency was installed under
`.git/research-python`; it is not a project or integration dependency. Neither
probe returned an exclusion certificate. Before treating a future bit-vector
result as a proof, the correspondence with integer path sums must also be
justified. These attempts establish nothing about the unrestricted graph.

Rather than extending their timeouts, the completed work used the explicit
one-gap extension hypothesis and its repeated-node constraints. The resulting
rigidity theorem explains an obstruction the solvers did not expose. Next work
should propagate analogous interval/complement constraints through additional
free vertices or critical-path cases before another unrestricted solver run.

The first Python attempt used `int.bit_count`, absent in the active Python
3.9.6; replacing it with the existing project's portable `bin(...).count('1')`
fixed that compatibility error. Independent forward enumeration initially
omitted B7's use at 15 and produced extra base pairs; adding that required
local equation made it agree with the complete backward enumeration. No failed
attempt was counted as a completed experiment.

## Commands and verification

```
python3 scripts/experiment_clift109.py --output results/2026-10-08-clift109-checks.json
# From lean/:
lake env lean ScholzBrauer/Clift109.lean
# From the repository root:
python3 scripts/verify_integration.py --output results/2026-10-08-integration-checks.json
```

Pinned Lean 4.27.0, mathlib a3a10db0e9d66acbebf76c5e6a135066525ac900 and
transitive dependencies are unchanged. The inspected Apache-2.0 upstream
addition-chain definitions are reused. Its open Scholz statement stays outside
compiled imports and supplies no assumption. Final full integration passed in **118.810990 seconds**, with **175** named
theorem audits, five upstream snapshot hashes and 94 final input hashes.
The 783-job Lean build passed in 17.358160s; the audit passed in 13.584462s.
All proof dependencies are among `propext`, `Quot.sound` and `Classical.choice`.
The compiled-source scan found no prohibited proof tokens. A first integration
passed before the additional rigidity proof; the final run was required by that
substantive proof addition and supersedes its input hashes. No package pins,
exporters or certificate formats changed. Reviewed the complete source/document
diff and structured generated evidence before committing. Local verification
and remote CI status are separate.

## Next obligation

The full selected-graph obstruction remains open **in this repository**, with
Clift's published claim already acknowledged. Extend the proved complement
restrictions to other changing bases, or split into critical-path cases with
complete coverage. Do not repeat the finished two-base enumeration or move to
the larger 5,784,689 graph without a specific mathematical reason.
