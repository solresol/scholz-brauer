# General path-weight bounds for Clift labellings in Lean

18 October 2026, Sunday, Australia/Sydney (AEDT). Milestone 3. This is the
formal part of the 109 reduction in `2026-10-18-clift109-box-exclusion.md`.

## Statements

`lean/ScholzBrauer/CliftLabelling.lean` works with an arbitrary source chain,
given by its parent steps `(p, q)` latest first. `valid` checks that every step
adds two earlier values and exceeds all earlier values. A labelling gives the
parent edges of `v = p + q` the shifts `a v` and `b v`; `cap` bounds outgoing
shifts. `weights a b L v` is the multiset of shift sums of the paths from 1 to
`v`, and `capBelow cap L v` sums the caps of the chain values below `v`.

- `card_weights`: vertex `v` has exactly `v` paths from the seed.
- `base_eq_sum`: if `B 1 = 1` and every step equation holds, then
  `B v = sum of 2^w` over the path weights of `v`.
- `weight_le_capBelow`: every path weight is at most `capBelow cap L v`.
- `bw_add_le`, `bw_mersenne`, `nodup_of_bw_eq`: binary weight (digit sum in
  base 2) is subadditive; `2^n - 1` has weight `n`; so a sum of `k` powers of
  two with weight `k` has distinct exponents.
- `weights_nodup`: `B n = 2^n - 1` forces `n` distinct path weights.
- `capBelow_ge`: every labelling has `n - 1 <= capBelow cap L n`.
- `weights_eq_range`: if `capBelow cap L n <= n - 1`, the weights are exactly
  `Multiset.range n`.

No carry-free, positivity, base-shape or shift-bound hypothesis is used. A
labelling lift of an `r`-step source therefore never has fewer than `n-1+r`
additions; it can at best match the Scholz-type bound for that source.

Instances:

- `Clift109.cost_ge_108`: every labelling of the selected 109 graph uses at
  least 108 doublings; `Clift109.weights_range_of_budget`: a labelling within
  108 has path weights exactly `0..108`. These are steps 1-3 of the 109
  reduction. The computational enumeration shows 108 is not attained.
- `NonHansen29.cost_ge_28`: every labelling of Clift's 29 graph (parents
  `(1,1),(2,2),(4,4),(8,1),(9,4),(8,8),(16,13)`) uses at least 28 doublings. The
  6 October one-base repair uses exactly 28, so it is optimal among labellings
  of that parent graph (35 additions). This is not an addition-chain optimum.

## Proof notes

Subadditivity uses Mathlib's Legendre formula
`sub_one_mul_padicValNat_factorial` at `p = 2`: `v_2(n!) + s_2(n) = n`. Since
`m! n!` divides `(m+n)!`, `v_2(m!) + v_2(n!) <= v_2((m+n)!)`, which rearranges to
`s_2(m+n) <= s_2(m) + s_2(n)`. A repeated exponent `x` lets `2^x + 2^x` be merged
into `2^(x+1)`, giving one fewer term than the binary weight requires. The cap
bound is an induction over the chain: a weight of the newest vertex is an
earlier weight plus one shift, bounded by its parent's cap, and that parent is
one of the earlier vertices excluded from its own bound.

The instance facts `valid`, the value list and the cap sum are checked by
`decide`. No development step failed except two base cases that needed `simp`
instead of `rfl`, a missing namespace on the Legendre lemma, and `if_pos rfl`
being preempted by simp (replaced by an explicit `rw`). Unused simp arguments
were removed; the module compiles without warnings.

## Verification

From `lean/`: `lake build` built 1,125 jobs (the new module in 22 s), and
`lake env lean Audit.lean` reports only `propext`, `Quot.sound` and
`Classical.choice` for all 13 new public theorems (209 audited in total).
Required integration passed once:

    uv run scripts/verify_integration.py --output results/2026-10-18-integration-checks-lean.json

258.8 s under Python 3.12.7, all 26 commands successful; Lean 4.27.0 build and
the 209-theorem audit pass with only standard axioms; five vendor and 105 input
hashes match. No toolchain or dependency change.

## Next obligations

Formalise the 8-box identity and dissociation, the critical-path zero
conditions and the gauge description for the 109 graph. The finite
classification still needs a much smaller argument before it can be
kernel-checked.
