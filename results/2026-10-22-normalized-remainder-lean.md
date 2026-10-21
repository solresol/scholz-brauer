# Normalized 109-path decomposition in Lean

22 October 2026, Thursday, Australia/Sydney (AEDT). Milestone 3.
Milestones 1 and 2 remain complete. Clean main started at 85b1d38, with the
expected solresol/scholz-brauer origin; fetch and fast-forward were already
current. Process-cwd inspection found no competing run. The run used its own
exclusive `.git/scholz-brauer-research.lock`.

## Completed obligation

The signed gauge coordinates now connect to the exact normalized weight
formula used by the saved 109 enumeration. `Clift109Normalize.lean` proves:

- `weightsZ_cast` and `weightsZ_gauge`: integer path weights agree with the
  existing natural recursion and telescope integer potentials even when a
  canonical representative has negative edges. This was the concrete blocker
  in the previous handoff; natural-only transport could not be applied there.
- `canonical_weights` and `weights_coordinates`: every natural labelling has
  the signed coordinate decomposition, retaining all occurrences. Write
  SS for subset sums, R7=SS(d1,d2)+{p} and R5=R7+(q+SS(d1)). The remainder is
  A1+SS(u,v)+R5, A2+SS(u)+R7, and A3+R5, of sizes 28,10,7 respectively;
  these sit beside the translated 64-weight box.
- `zSS_abs`, `rem7_normalize`, `rem5_normalize`, and the box/remainder
  normalization theorems: replace each difference by its absolute value,
  with the minimum translations proposed on 21 October. The complete multiset
  remains unchanged, not merely its support or cardinality. This proves the
  proposed formula, rather than assuming the finite enumeration.
- `normalize_gaugeCoordinates`: the resulting twelve coordinates equal the
  direct minimum-based formulas in `invariants` from the existing experiment.
  This is a mathematical identification of formulas, not a verified compiler
  or proof that Python executes those formulas correctly.
- `normalized_interval_of_budget`: seed 1, the selected graph equations,
  terminal M109 and cap budget at most 108 imply that the normalized 64+45
  decomposition is exactly the multiset of integers 0..108.
- `canonical_cap_constraints`: the actual outgoing cap inequalities become
  integer difference constraints on the signed section, with endpoint
  potentials zero and both lower and upper edge bounds retained.

No new exporter, certificate format, solver, search or dependency was added.
The new integer recursion is a small mathematical extension of the existing
recursion with a proved bridge, needed specifically for negative canonical
edges. The original addition-chain definitions and completed theorems are reused.

## Limits and next obligation

Absolute values discard orientation information. Equality of normalized
weights is not asserted to imply gauge equivalence or cap feasibility. Recover
the finite sign/orientation choices and transport the signed cap inequalities
to the oriented representatives used by the enumeration; combine with the
existing critical-path saturation theorem. Then prove a smaller finite
classification or another structural reduction suitable for the kernel.

The full selected-109 exclusion at budget 108 and attained minimum 109 remain
computational. This run proves no new Scholz instance, source optimum,
Mersenne-chain optimum or universal extension. No completed large search was
repeated and no novelty or latest-frontier claim is made.

## Sources, proof attempts and validation

Rechecked the live primary Clift page and 109 diagram on 22 October. Both
SHA-256 hashes match 21 October; URLs, timestamps and version hashes are in
`data/2026-10-22-normalization-source-recheck.json`. Only the selected graph is
used, not claims about optimality or completeness of published chain lists.
Re-read the adapted formal-conjectures definitions, uncompiled upstream Scholz
statement and Apache-2.0 licence. The unproved target supplies no hypothesis.
Lean 4.27.0 and mathlib a3a10db0e9d66acbebf76c5e6a135066525ac900 remain pinned.

All new theorems are symbolic over arbitrary edge shifts under their stated
hypotheses; no finite input range or random seed applies. Exact integer/multiset
algebra replaces a search. A first draft of the integer recursion returned a
seed at every unknown vertex; the cast proof rejected it, and the base case was
corrected to match the existing `v=1` guard. Other development errors involved
an unavailable tactic/lemma name, excessive congruence decomposition and
simplification. Sorting 109 cons cells and simplifying whole record expressions
hit the default 200,000-heartbeat bound. Rather than raising it, the proofs now
normalize integer terms then use associativity/commutativity for the multiset,
and prove the three remainder offset equalities separately. Final standalone
compilation passed without warnings in 14.61 seconds at default heartbeats.
No failed attempt was counted as a proof or mathematical exclusion.

Commands:

    cd lean
    /usr/bin/time -p lake env lean ScholzBrauer/Clift109Normalize.lean
    cd ..
    uv run scripts/verify_integration.py --output results/2026-10-22-integration-normalization.json

Required integration passed once in **232.987320 seconds**, using Python
3.11.6. All 29 commands succeeded. Lean built 1,128 jobs in 17.418905 seconds;
the 253-theorem audit (including all 17 new public theorems and their transitive
dependencies) passed in 10.388034 seconds, using only `propext`, `Classical.choice`
and `Quot.sound`. Five vendor hashes and all 121 input hashes match, including
an independent final report readback. No proof placeholders, custom axioms or
`native_decide` occur in the new module. The existing mathematical summaries
agree with 21 October after excluding runtime/date and temporary-path diagnostics.
The suite checks existing certificates; it does not rerun the completed full
109 or 5,784,689 enumerations. Complete proof, documentation, source evidence and
structured integration differences were inspected; `git diff --check` passed.
This establishes local validation; remote CI is not claimed.
