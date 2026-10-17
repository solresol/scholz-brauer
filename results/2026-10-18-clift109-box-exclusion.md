# Budget 108 is impossible for Clift's selected 109 graph

18 October 2026, Sunday, Australia/Sydney (AEDT). Milestone 3. Milestones 1
and 2 are complete and were not reopened.

## Result

Let G be the selected parent graph of Clift's 109 diagram (8=4+4; table in
`2026-10-08-clift109-obstruction.md`). A *labelling* assigns an arbitrary
nonnegative integer shift to each of the 22 edges. With seed B1=1 and
B_v = 2^a B_p + 2^b B_q at every vertex, all bases are determined. The cost is
the sum over tails u of cap_u, the largest outgoing shift of u; the allocated
chain for B109 has 11 + cost additions.

**Every labelling with B109 = M109 = 2^109-1 has cost at least 109. Cost 109 is
attained.** So no labelling of the selected graph meets the 108-doubling
budget, with no restriction on any base: no fixed vertex, no carry-free
assumption (it is forced), no bound on shifts. This is Clift's reported
obstruction for this graph: no edge labelling with path sums exactly 0..108
whose weight-108 path collects every cap.

This is a **computational proof**: a complete enumeration of every
"interval configuration", carried out by two independent programs, then exact
certificates for each case. It is not a Lean theorem. It establishes no
Scholz instance, optimum, Mersenne-chain length or novelty. The value
sequence with the alternative 8=7+1 is a star source with a 119-addition lift
(8 October); the obstruction concerns only the selected parent graph.

It supersedes the partial exclusions of 8-17 October. All of their numerical
results are recomputed exactly from the new enumeration (see Cross-checks).

## Reduction

Write a path for a source-to-sink path and s(π) for the sum of its shifts.

1. **Paths.** By induction, B_v = sum over paths π from 1 to v of 2^s(π), and
   the number of such paths is v. So B109 is a sum of 109 powers of two.
2. **Distinct weights.** The binary weight of x+y is at most that of x plus
   that of y. If two of the 109 exponents coincided, B109 would be a sum of 108
   powers of two, with binary weight at most 108 < 109 = weight of M109. So
   the 109 path weights are distinct; the largest is at least 108.
3. **Cost bounds every path.** The tails along a path are distinct and each
   shift is at most its tail's cap, so cost >= s(π) for every path. Hence
   cost >= 108 always. If cost <= 108, all weights lie in 0..108, so they are
   exactly {0,...,108}: an **interval labelling**, and cost = 108.
4. **Critical path.** In an interval labelling with cost 108, let π* be the
   unique weight-108 path. Then 108 = s(π*) <= sum of caps on π* <= cost = 108,
   so every vertex off π* has all outgoing shifts 0 and every edge of π* has
   the largest shift leaving its tail.
5. **The 8-box.** Let S_v (R_v) be the multiset of weights from 1 to v (from v
   to 109). With Greek names for the shifts in parent order
   (α,β: 1→2; γ,δ: 2→4; ε: 4→5; ζ: 1→5; η: 5→7; θ: 2→7; ι,κ: 4→8; λ: 8→15;
   μ: 7→15; ν: 15→23; ξ: 8→23; π: 23→28; ρ: 5→28; σ: 28→51; τ: 23→51;
   φ: 51→58; χ: 7→58; ψ: 58→109; ω: 51→109), expanding gives
   - paths through 8: S_8 + R_8 = t + SS(u,v,w,d1,d2,d3), the 64 subset sums of
     u=|α-β|, v=|γ-δ|, w=|ι-κ|, d3=|λ+ν-ξ|, d2=|π+σ-τ|, d1=|φ+ψ-ω|;
   - the other 45: (S_4+ε+R_5) ⊔ (S_2+θ+R_7) ⊔ (ζ+R_5), which normalise to
     A1+R(u,v)+R5, A2+P(u)+R7 and A3+R5, where P(a)={0,a}, R(a,b)=P(a)+P(b),
     R7 = R(d1,d2) ∪ {p}, R5 = R7 ∪ (q+P(d1)).
   The twelve integers (u,v,w,d1,d2,d3,t,p,q,A1,A2,A3) are the *configuration*.
   In an interval labelling the 64 box weights are distinct, so the six
   differences are positive with distinct subset sums and t + sum <= 108.
6. **Gauge.** Adding g_v to both in-shifts of v and subtracting it from its
   out-shifts preserves every path weight. Fix a configuration, which of its
   two box-only differences is w (the other is d3), the signs of λ+ν-ξ, π+σ-τ
   and φ+ψ-ω, and order each parallel pair larger first (an automorphism).
   The map from shifts to configuration is then affine of rank 12 with a
   section, so every such labelling is one explicit particular labelling plus
   an integer gauge g in Z^10 (its coboundary lattice is saturated: the
   incidence matrix is totally unimodular). Point 4 becomes a system of
   difference constraints on g: feasible iff it has no negative cycle.
7. **Halving.** If X = A ⊔ (A+d), then A = X/(2^d+1) is unique and every
   maximal run of X in steps of d has even length. If X = (A ⊔ (A+d)) ⊔ E with
   |E| = k, X has at most k odd runs in steps of d.

## Complete enumeration

Let C be [0,108] minus the box. Then C = P(d1)+Z ⊔ E with
E = p + (A1+R(u,v) ⊔ A2+P(u) ⊔ {A3}) of size 7, and C = P(u)+Y ⊔ (A3+R5).
So C has at most 7 odd runs in steps of u and in steps of d1.

`scripts/clift109_box_search.cpp` (primary, C++17) enumerates every 6-set of
positive integers with distinct subset sums and sum at most 108 (31,048), every
t (263,256 pairs), keeps both odd-run bounds (109,247 pairs survive), and every
role assignment. It enumerates each rectangle, pair and point of E inside C,
halves C minus E by d1 with exact integer division (3,540,289 candidates), then
recovers A3 as an element of Z and q from the five q-dependent elements, and
checks the complete partition. Exactly **216 configurations** remain.

`scripts/clift109_box_dual.py` (independent, Python) shares only the box idea.
It generates subset-sum sets by a popcount test, halves on the *source* side
by u with a peeling algorithm, enumerates A3+R5 with run-parity pruning, then
splits Y by v. It finds the same 216 configurations. Its 3,540,289 halving candidates equal
the C++ count, as they must: the two steps are the same check with the roles
of (u,v) and (d1,d2) exchanged.

All six-sets in the solutions are {1,2,4,8 or 15,23 or 28,51 or 58}: either
(u,v)=(1,2) or, dually, (d1,d2)=(1,2).

## Certificates

For each configuration, each choice of w among its two box-only differences
and each of eight orientations (3,456 cases):

- the particular labelling is rebuilt and its 109 explicit path weights are
  checked to be exactly 0..108;
- the unique weight-108 path is found, and Bellman-Ford finds a **negative
  cycle** in the cost-108 difference system. Every cycle is stored as named
  constraints; an independent checker re-derives each constraint and checks
  that the cycle telescopes to 0 <= negative. **No case admits cost 108.**
- the exact minimum cost is computed by min-cost flow on the LP dual, with an
  explicit nonnegative optimal labelling of equal value (so the value is
  certified exactly in integers). During development it agreed with an
  independent floating-point LP (SciPy/HiGHS) on all 3,456 cases.

Minimum costs range from 109 to 250; **69 cases attain 109**. One optimal
labelling per such case was sorted into an ordinary allocation and replayed
by the existing independent checker: each uses 120 additions for M109.

By points 3-4, the minimum over all labellings is therefore exactly 109.

The minimum is not confined to shifted Mersennes. Twelve configurations attain
109; in 34 of the 69 minimal cases the stored optimum has no intermediate base
that is a shifted Mersenne. For example, the dual configuration
(u,v,w,d1,d2,d3) = (51,23,4,1,2,8) admits shifts, in parent order,
(51,0) (23,0) (12,0) (0,5) (12,8) (16,0) (0,8) (5,0) (0,3) (0,1) (1,0),
with B2 = 2^51+1 and caps 51,23,12,0,1,16,0,5,0,0,1 (sum 109).

## Cross-checks with earlier work

Each earlier family is recounted from the 216 configurations: fix the listed
bases to Mersenne values (which fixes their gauges), then enumerate every
nonnegative gauge point. All counts and complete cost histograms equal the
stored values from independently written code with different algorithms.

| Family (date) | Base assignments | Labellings | Minimum |
| --- | --- | --- | --- |
| All bases Mersenne (8 Oct; Lean minimum) | 1 | 256 orientations | 110 |
| 5, 7 free (8 Oct) | 63 | 2,304 | 110 |
| 5, 7 and one or two others free (9 Oct), 36 cases | all 36 equal | all 36 equal | 109 iff 28 free |
| 2, 4, 5, 7, 8, 15 free (14 Oct) | 2,763 | 52,512 | 110 (88 bases) |
| Every base a shifted Mersenne (9 Oct; Lean) | - | - | 109 |
| B58 = M58 fixed (16 Oct), 29 pairs | 4,279,900, pair by pair | - | 109 iff l = 0 |

The 16 October compatible pairs (0,0..21), (1..7,0) and its 109 witness are
recovered exactly, as are the full cost histograms of the 8, 9 and 14 October
families. 3,000 random arbitrary labellings (seed 20261018) check the box
formula against explicit path weights and the particular-plus-gauge claim.

## Failed and bounded probes

- CP-SAT (OR-Tools 9.15.6755, Python 3.12.7, 8 workers, default seed) on the
  raw 22-shift model with 109 all-different path weights and cap sum <= 109
  returned UNKNOWN after 120 s without even finding the known cost-109
  labelling. No exclusion follows; the solver is not a project dependency.
- A first Python prototype of the box search took 25 s on the 6-set
  {1,2,4,8,16,32} alone; the final programs use the odd-run and halving
  prunings above.
- For Lean planning: even with the box pinned at the top (8 on the critical
  path), 466,380 E-candidates remain over 31,048 offsets (64 configurations).
  The 12509 exclusion needed 263 s of kernel time for 29,865 contexts, so a
  direct kernel replay of this search is not realistic. A formal proof needs
  a substantially smaller argument.

## Commands and verification

    uv run scripts/experiment_clift109_box.py --output results/2026-10-18-clift109-box-exclusion.json
    uv run scripts/check_clift109_box.py results/2026-10-18-clift109-box-exclusion.json

The experiment started 2026-10-18T00:14:10+11:00 and refuses to replace an
existing report. It ran under `uv run` (Python 3.12.7), exact integers, standard
library only, random self-test seed 20261018; input hashes are in the JSON.
The C++ program was compiled by the driver with Apple clang 21.0.0,
`-O2 -std=c++17 -Wall -Wextra -Werror`. Timings: C++ enumeration 481.6 s
(a standalone run of the same source took 174.7 s; the longer time overlapped
other jobs), independent Python enumeration 507.6 s, certificates and exact
minima 2.0 s, cross-checks 78.3 s, total 1073.0 s. The report is 3.4 MB.

The standalone checker shares no code with the experiment except the existing
`check_allocation`/`check_certificate` replay. It passes in about 1 s and
rejects seven deliberately corrupted reports: changed cycle constant, dropped
constraint, wrong constraint kind, missing case, wrong configuration, wrong
minimum and invalid optimum. It now runs in `verify_integration.py`; the
20-minute enumeration remains a separate research run.

During development the C++ enumeration was run three times with identical
output (216 configurations), the Python enumeration twice, and the cross-check
code was also run against an earlier SciPy LP and the C++ output alone. These
repetitions were development checks, not independent results.

Required integration passed once:

    uv run scripts/verify_integration.py --output results/2026-10-18-integration-checks.json

169.4 s under Python 3.12.7, all 26 commands successful, including the new
certificate check (1.1 s). Pinned Lean 4.27.0 build 5.6 s; the 196-theorem axiom
audit 18.2 s, only standard axioms. Five vendor and 104 input hashes matched,
including the new evidence JSON. No Lean source, toolchain or dependency changed.

## Next obligations

The selected 109 graph is resolved computationally. Remaining work:
formalise steps 1-7 in Lean and find a proof of the finite classification small
enough for the kernel (a slicker argument for min(u,d1)=1 would be a natural
start); then apply the box method to other non-Hansen parent graphs. Clift's
5,784,689 example remains deferred.
