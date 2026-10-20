# The 109 box and signed integral gauge classification

21 October 2026, Wednesday, Australia/Sydney (AEDT). Milestone 3.
Milestones 1 and 2 were already complete at the starting commit 7cea133.
The clean main checkout fetched and fast-forwarded without changes; no competing
local research process was present. The prior overlap blocker had cleared.

## Mathematical results

For arbitrary nonnegative shifts on Clift's selected graph (8=4+4),
`weights_box_partition` gives an exact multiset identity: all 109 path weights
are a 64-weight box plus a 45-weight remainder. Multiplicities are preserved.
The box consists of choosing one route from each of these six pairs, written
from sink to seed using the existing first/second-parent shifts a,b:

    (a58+a109,b109), (a28+a51,b51), (a15+a23,b23),
    (a8,b8), (a4,b4), (a2,b2).

`box_normalize` writes this as t+SS(d1,d2,d3,w,v,u), where each difference is
the maximum minus the minimum of its pair, and t is the sum of the six minima.
The general `choices_normalize` proves the identity for any list of pairs.
With seed B1=1, all graph production equations and B109=2^109-1,
`box_dissociated` proves all 64 subset sums distinct. This needs no budget,
carry-free or intermediate-base hypothesis. Each difference is therefore
positive, and the six differences are pairwise distinct. With outgoing caps
summing to at most 108, `box_constraints_of_budget` proves t+sum(differences)<=108.
This closes the box identity and dissociation obligation, with the exact raw
remainder retained for subsequent normalization.

The adjacent gauge obligation also advances substantially. For arbitrary
**integer** edge shifts, `gaugeCoordinates` gives twelve explicit signed
coordinates, before absolute-value/minimum normalization. The first six are
signed versions of the differences above. `canonicalA` and `canonicalB`
provide an integral section for every twelve-tuple, proved by
`gaugeCoordinates_section`. `gauge_reconstruction` expresses every labelling
as this representative plus g(head)-g(tail), with ten explicitly given interior
potentials and g1=g109=0. `gaugeCoordinates_eq_iff` proves both directions:
equal coordinates if and only if the labellings differ by such an integer gauge.
Thus integral reconstruction is proved directly, without a matrix-saturation
assumption or an external linear-algebra calculation.

The canonical representative may have negative shifts. This is intentional and
does not claim it is itself a valid addition-chain allocation. The general
`CliftLabelling.weights_gauge` proves potential telescoping using the existing
natural path-weight multiset, when both original and transformed edge shifts
are natural; potentials may still be arbitrary integers. Its selected-graph
corollary proves equality of terminal weights for equal signed coordinates.
No new path enumeration, exporter, certificate format, checker, solver,
dependency or research experiment was needed.

## Boundaries and next obligation

The signed coordinates are **not yet identified in Lean** with the
absolute-value orientations and normalized 45-weight remainder in the saved
216-configuration enumeration. Prove that link, transport the critical-path
cap constraints, then obtain a smaller kernel-checkable finite classification.
The raw exact partition and the signed gauge classification are completed
statements; neither assumes the enumeration's completeness.

The full exclusion of budget 108 and the attained minimum 109 for this graph
remain computational. This run proves no new Scholz instance, source optimum,
Mersenne-chain optimum or general extension. The completed 109 and 5,784,689
large searches were not repeated. No novelty or latest-frontier claim is made.
There is no recurring proof-strategy failure: the existing multiset representation
handles the box directly, and signed integer coordinates remove orientation
case splits from the integral gauge argument.

## Sources, failures and checks

Re-read the repository's adapted formal-conjectures definitions, pinned upstream
open Scholz reference and Apache-2.0 licence. The unproved reference remains
uncompiled and unimported. Lean 4.27.0 and mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900` are unchanged.
Re-fetched the primary [Clift page](https://www.additionchains.com/ScholzBrauer.html)
and [109 diagram](https://www.additionchains.com/LargeNonHansen.png): hashes match
18 October. Access date/time and version hashes are recorded in
`data/2026-10-21-box-source-recheck.json`. Only the selected graph is used;
published source optimality/completeness is unnecessary for today's theorems.

Development failures were local elaboration and simplification errors: `rfl`
pattern substitution renamed a variable, multiset disjointness needed its
membership lemma, an identity map needed explicit membership construction,
integer-valued map lambdas needed natural-domain annotations, and unfolding
`weights` required `ite_true`. A final list disjunction needed empty-list
simplification. One command ran from the repository root instead of `lean/`
and failed before compiling. These were corrected; no timeout or failed
mathematical hypothesis was interpreted as evidence. No increased heartbeat
limit was needed. Final standalone checks had no warnings: box 5.45 s, gauge
4.88 s; the box dependency build also passed (6.4 s for the new module).

Commands, from `lean/`:

    lake env lean ScholzBrauer/Clift109Box.lean
    lake build ScholzBrauer.Clift109Box
    lake env lean ScholzBrauer/Clift109Gauge.lean

Required integration, from the repository root:

    uv run scripts/verify_integration.py --output results/2026-10-21-integration-box-gauge.json

No random seed or bounded input range applies to the new symbolic theorems:
they quantify over all shifts satisfying the stated assumptions. The existing
integration suite retains its own fixed inputs, seeds and exact checks.

A concrete next proof route (not yet a theorem): for the signed coordinates,
put m(x)=min(x,0) and L=m(d1)+m(d2). Replace each of the six differences by its
absolute value, t by t+sum(m of the six differences), p by p-L,
q by q-m(d2), A1 by A1+m(u)+m(v)+L, A2 by A2+m(u)+L, and A3 by A3+L.
Factor the raw remainder through R7=SS(d1,d2) plus {p} and
R5=R7 plus (q+SS(d1)) before normalization. The negative shifts of the canonical
representative mean the natural-only gauge transport theorem cannot be applied
to it directly; prove the identity after integer casting, or extend the existing
weight recursion to integer shifts with a proved natural-cast bridge. Do not
assume this proposed normalization or the enumeration's completeness.

## Integration outcome

Required integration passed once in 210.903700 s using Python 3.11.6:
29 commands succeeded, the pinned Lean build completed 1,127 jobs in
11.952277 s, and the 236-theorem audit passed in 9.342116 s. The audit includes
all 23 new public theorems and their transitive dependencies; only `propext`,
`Quot.sound` and `Classical.choice` occur. All five vendor hashes and 120 input
hashes matched, including final report readback. No proof placeholders, custom
axioms or `native_decide` occur in the new modules. The structured mathematical
summaries match the previous 19 October integration; observed differences are
runtime/date, Python executable, temporary paths and command diagnostics.
The existing suite's saved-certificate checks passed; the full large searches
were not rerun. The complete code/documentation/source-evidence diff was
reviewed and `git diff --check` passed before commit. This establishes local
integration success; no remote CI result is claimed.
