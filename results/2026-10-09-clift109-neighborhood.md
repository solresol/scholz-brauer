# Shifted-Mersenne obstruction and a 109-doubling repair

9 October 2026, Friday, Australia/Sydney (AEDT). Active milestone 3.
Milestones 1 and 2 and the infinite one-gap family were already complete.

## Results and boundaries

For Clift's selected 109 graph, **every allocation whose bases are shifted
Mersenne values needs at least 109 doublings**. This allows an arbitrary
nonnegative shift at every vertex, with no finite search bound on the shifts.
The seed remains 1 and the terminal remains `2^109-1`.
`Clift109Shifted.lean` proves this from the actual sum equations, not from
an assumed orientation or the output of a solver. A checked allocation attains
109, so the minimum in this family is exactly 109. The required budget is 108.

The exact neighborhood experiment also allows arbitrary binary patterns.
Keep bases 5 and 7 free, and additionally free any one or two of
`{2,4,8,15,23,28,51,58}`. All other bases retain their unshifted Mersenne values.
Across all 36 complete cases, the minimum is 109 if vertex 28 is free, and 110
otherwise. Hence any budget-108 labelling would have to change **at least three
vertices outside 5 and 7**, and the Lean result says **at least one base must
have a non-Mersenne odd part**. These are necessary conditions, not existence.
The computational neighborhood exclusion is not kernel-certified.

Neither result excludes arbitrary labellings, proves source or Mersenne
optimality, or establishes a new Scholz instance. The alternate parent choice
`8=7+1` already has a 119-addition star lift; today's 120-addition witness is
an improvement only within the selected `8=4+4` graph. No novelty is claimed.

## General two-block proof

For positive `p,q`, Lean proves, for all natural `a,b,t`,

```
M(p)*2^a + M(q)*2^b = M(p+q)*2^t
    -> (a=t+q and b=t) or (a=t and b=t+p).
```

The proof inducts on the common output shift. At output shift zero, parity
forces an input shift to be zero, and the usual Mersenne block identity fixes
the other. At a positive output shift, mixed parity is impossible; both input
shifts zero would make the sum too small. Cancel a factor two and apply the
induction hypothesis. No carry-free hypothesis is needed for this lemma.

For base offsets `t_v`, edge labels `a,b` and outgoing caps `c_v`, apply the
lemma to the exponents `t_p+a,t_q+b`. Each graph step gives one of two sets of
linear inequalities. The three equal-parent steps have identical orientation
constraints. The remaining eight orientation choices yield 256 linear cases.
The lower-bound proof discharges these inequalities in Lean. There is no
finite cap restriction, solver result, unproved axiom or target conjecture in
the theorem hypotheses.

## Attaining 109

All bases are ordinary Mersennes except `B5=2*M5=62` and
`B28=2*M28=536870910`. In the existing selected-parent order, edge shifts are:

```
(1,0), (2,0), (2,1), (1,0), (4,0), (7,0),
(0,15), (6,0), (22,0), (7,0), (0,58).
```

The caps in source order are
`[1,2,4,1,0,15,0,6,22,58,0,0]`, summing to 109.
Lean checks the actual eleven sum equations, the endpoints and the cap sum.
The existing independent index checker replays the complete sorted allocation:
109 doublings plus 11 graph sums, or 120 additions. The experiment retains all
minimizing bases/labels/caps and one complete certificate per case, and replays
every minimizer independently.

## Why the finite enumeration is exhaustive

All arithmetic is exact Python integer arithmetic; there is no random seed or
solver dependency. Source values and selected parents are read against the
existing primary-source fixture.

For a known positive target `T` and known parent `K`, every solution of
`u*2^a + K*2^b=T` has both shifts less than `bit_length(T)`. Enumerate each
positive remainder `T-K*2^b` and divide repeatedly by two until its odd part.
This gives every possible positive `u`. For equal unknown parents, enumerate
`u=T/(2^a+2^b)` with `a>b`, requiring exact division. Equal shifts would overlap;
swapping parallel equal-parent edges preserves every relevant equation and cap.

Intersect all available one-unknown consumption domains. Check every fully
specified graph equation, not merely the one used for branching. If no such
domain is available, produce a base from two known parents. Its smallest fixed
descendant bounds it, since every nonnegatively shifted positive parent is at
most its child. Enumerating both shifts below that bound's bit length therefore
covers all possibilities. The terminal guarantees a fixed descendant.
Each branch assigns one new base, so recursion terminates. Once every base is
known, enumerate the Cartesian product of every exact carry-free local shift
pair, with the same justified finite bounds. Compute outgoing maxima and their
sum without imposing the hoped-for 108 bound.

Nested two-shift enumeration independently checks all local options for every
minimizing base assignment. A separately computed cap list and the existing
index certificate checker validate every minimum. These independently check
witnesses, not completeness of the exhaustive exclusion. The completeness
argument above and the Python implementation remain outside Lean.

The final integration JSON records each case's candidate branches, viable
base assignments, enumeration digest, labelling count, entire cost histogram,
minimizers and runtime under `clift109_neighborhood`. Cases overlap; their
counts must not be added and described as distinct labellings of the union.

## Rechecked source and failed approaches

Reopened [Clift's primary notes](https://www.additionchains.com/ScholzBrauer.html)
and retrieved the [selected graph](https://www.additionchains.com/LargeNonHansen.png)
on 9 October 2026. The live undated diagram still has SHA-256
`58a2ef45e38701676b1621f38f2995ea3f08f18f410eb44dd129da9163b005a6`, matching
our previously visually checked source. Rechecked the source sums. The notes'
full graph impossibility remains a literature claim here; no latest-frontier
or priority assertion is made. The inspected, Apache-2.0 upstream
formal-conjectures addition-chain definition remains in use; its unproved
Scholz statement remains uncompiled.

A critical-path split plus the first path-sum moment reduced the previous
unrestricted encoding to 12 candidate paths. All 12 integer and all 12 hybrid
bit-vector cases timed out at 10 seconds each, seed 0. Those are unknown, not
exclusions. `results/2026-10-09-clift109-probes.json` retains exact encodings and
per-case times. An exploratory integer optimization of the shifted-Mersenne
family found exact optimum 109 in 0.043 seconds; its result motivated, but is
not a dependency of, the Lean proof. Z3 4.15.3.0 was installed temporarily in
`.git` and removed after the run; no project dependency changed.

The unrestricted path split was not sufficient. Future work should exploit
the new necessary conditions or generalize the complement/interval argument
to bases with several binary intervals. Do not simply increase solver timeouts,
repeat the completed neighborhood, or move to larger graphs.

## Verification

The final verification command is:

```
python3 scripts/verify_integration.py --output results/2026-10-09-integration-checks.json
```

It invokes `python3 scripts/experiment_clift109_neighborhood.py`, the existing
integration checks, and (from `lean/`) `lake build` and `lake env lean Audit.lean`.
Lean is pinned to 4.27.0 and mathlib to
`a3a10db0e9d66acbebf76c5e6a135066525ac900`; no dependency pin changed.

During proof development, unconstrained `omega` and an explicit orientation
split with `omega` were interrupted because of slow arithmetic processing.
Splitting with `linarith` completed the lower-bound proof but took several
minutes. `grind`, after normalizing numerical indices and merging the three
equal-parent constraints, completed the same bound faster and is retained.
The first attained-witness proof needed its final list-membership disjunction
simplified; this was an elaboration error, not a failed mathematical claim.
Two early shell invocations used the wrong relative Lean path and failed;
neither is counted as a successful build.

The final run uses the pinned environment, full integration and the named
theorem axiom audit. Exact commands and measured outcomes are
recorded in `results/2026-10-09-integration-checks.json` and the research log.

Final integration passed in **198.022009 seconds**. The complete neighborhood
experiment took **69.229385 seconds** on Python 3.9.6 and independently replayed
1,124 minimizing occurrences across overlapping cases. The Lean build passed
973 jobs in **39.260573 seconds**; the new module took 26 seconds. All **182**
audited theorems passed in **8.630805 seconds**, with only `propext`,
`Quot.sound`, and `Classical.choice`. Five vendor hashes and all 96 recorded
source/input hashes matched after verification; the compiled proof-token scan
was clean. Local validation does not imply completion of remote CI.
