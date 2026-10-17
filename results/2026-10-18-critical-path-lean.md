# Critical paths for budget-attaining Clift labellings

18 October 2026, Sunday, Australia/Sydney (AEDT). Milestone 3. The clean
checkout at f737015 already contained the completed Hansen and 12509 proofs,
the complete computational 109 obstruction, and Lean reduction steps 1-3.
The older automation handoff was superseded by those interactive commits.

## Mathematical result

For any valid selected-parent source ending at n, with seed B1=1, terminal
Bn=2^n-1, nonnegative edge shifts and outgoing caps totalling at most n-1,
Lean now proves there is a path from 1 to n with weight exactly n-1 such that:

- each edge on the path has shift equal to its tail's cap;
- every source vertex below n skipped by the path has cap zero.

The specialised `Clift109.critical_path_of_budget` also states that every
outgoing edge from any skipped vertex has shift zero. Together with the earlier
interval theorem, this closes **step 4** of the computational 109 reduction.
The caps need only bound every outgoing shift; equality with the chosen shift
is proved. No positive-cap, carry-free, base-shape or finite-shift assumption is
introduced. The singleton source n=1 is covered by the general theorem.

This is a kernel-checked structural theorem. It is not the full Lean exclusion
of budget 108, a new Scholz instance, or an addition-chain optimality theorem.
The existing exact minimum of 109 doublings for the selected graph remains
computational; the full finite classification is not imported or assumed.

## Proof and representation

The existing `weights` multiset forgets which tails a path visits, which blocked
a precise statement of the skipped-vertex condition. The small inductive
`CliftLabelling.Path` relation records actual selected-parent paths as lists of
(tail, shift) pairs, latest first. Its seed, older-vertex and two parent
constructors follow the existing recursive graph definition. No new checker,
certificate format, exporter, solver or dependency was added.

`Path.weight_mem` proves its shift sum belongs to the existing weight multiset.
`critical_path_of_weight` constructs a path whenever that multiset contains the
full earlier-cap sum. At a parent p, the inequalities

    parent weight + edge shift <= capBelow(p) + cap(p) <= total earlier caps

must both be equalities. Thus the edge saturates cap(p), the parent weight
saturates its own prefix budget, and every skipped vertex above p has zero cap.
Induction handles vertices below p. The auxiliary `cap_zero_above` uses nested
filters and the existing prefix-sum bound, with exact natural arithmetic.
`critical_path_of_budget` supplies the attaining weight using the already
proved lower bound and interval equality.

Development failures were limited to simplification: unfolding `weights` left
an `if True` unreduced, obscuring a commutative addition equality; explicitly
reducing `ite_true` fixed it. An unavailable Boolean simp lemma was replaced by
`Bool.eq_iff_iff` and arithmetic. No mathematical hypothesis failed, no new research search
was run, and no timeout was interpreted as evidence. The final direct module
check passed without warnings in 10.26 seconds at the default heartbeat limit.

## Sources and verification

Re-read the adapted Google DeepMind addition-chain definitions, the pinned
upstream open Scholz reference and Apache-2.0 licence. The unproved reference
remains outside the compiled library. Lean stays pinned at 4.27.0 with the
existing locked dependencies. Re-fetched the primary [Clift page](https://www.additionchains.com/ScholzBrauer.html)
and [109 diagram](https://www.additionchains.com/LargeNonHansen.png): both hashes
match 17 October. URLs, hashes and access time are recorded in
`data/2026-10-18-critical-path-source-recheck.json`. No novelty or latest-frontier
claim is made, and no published optimality assertion is needed for this proof.

Commands:

    cd lean && lake env lean ScholzBrauer/CliftLabelling.lean
    uv run scripts/verify_integration.py --output results/2026-10-18-integration-checks-critical-path.json

The second command runs from the repository root. The existing required suite
includes the pinned Lean build and axiom audit, source-hash checks and saved
certificate verification. The large completed 109 enumeration is not rerun.

Required integration passed once in **151.595785 seconds** under Python
3.11.6, with all 26 commands successful. Pinned Lean 4.27.0 built 1,125 jobs
in 15.021225s; the 213-theorem axiom audit passed in 9.080743s, including all
four new public theorems and their private dependencies. Only `propext`,
`Quot.sound` and `Classical.choice` occur. All five vendor hashes and 105 input
hashes matched, including a final report readback. The compiled proof-token
scan found no `sorry`, custom `axiom` or `native_decide`. The saved 3,456-cycle
109 certificate check passed; the large enumeration was not repeated. Exact
command outputs and input hashes are in the integration JSON. No random seed
or new computational experiment was used. Reviewed the complete source,
documentation and evidence diff before commit.

## Sunday assessment and next obligation

Milestones 1 and 2 remain complete. Milestone 3 advanced by closing the whole
critical-path obligation, generally and for the selected 109 graph. The current
representation suffices for this step; no strategy reset is warranted.

Next formalise the 64-path box identity and distinct subset sums, then the
gauge description. The finite classification still needs a smaller proof than
a direct replay of the large search. Do not resume the superseded fixed-tail
case analyses or repeat the completed 216-configuration enumeration. The
5,784,689 data remain scoped evidence, with no labelling or Scholz result here.
