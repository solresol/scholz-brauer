# Oriented normalization and cap constraints — 23 October 2026

Friday, Australia/Sydney. Milestone 3 advanced; milestones 1 and 2 remain
complete. The checkout was clean on main at 1176782; origin was verified as
solresol/scholz-brauer and fetch/fast-forward reported already current. Process
inspection found only this run's node runtime and transient inspection commands.
No necessary exact-search blocker remained, so this computational day continued
Lean proof work. No completed search was repeated.

## Mathematical result

In `lean/ScholzBrauer/Clift109Normalize.lean`, `Orientations = Fin 6 → Bool`
has kernel-checked cardinality 64. `orientCoordinates` restores the six signed
differences AND the six minimum-offset corrections. `orient_normalize` recovers
every original signed tuple using its sign bits. `normalize_orient` gives the
reverse identity for every tuple with six nonnegative differences; its other
coordinates are arbitrary integers. `normalize_eq_iff` therefore classifies
exactly every preimage of normalization by these finite choices. Zero differences
can make choices repeat a representative; no 64-distinct-preimages claim is made.

`oriented_weights` proves that every such oriented canonical section has the
same normalized 109-path multiset. `oriented_cap_constraints` transports the
nonnegative lower bounds and outgoing cap upper bounds of every natural
labelling to one of those sections, preserving both zero endpoint potentials
and the original cap function (hence any cap budget).

This closes the lost-sign reconstruction and normalized cap-transport
obligations. It does not prove cap feasibility from weight equality, nor identify
the chosen canonical section with the Python enumerator's particular gauge.
The next proof should combine these explicit integer difference constraints
with critical-path saturation, then reduce the remaining interval configurations
to a kernel-suitable finite classification. Full selected-109 exclusion and
minimum 109 remain computational. No new Scholz instance, source optimum,
Mersenne optimum or novelty claim is made.

## Method and sources

The proof uses exact integer algebra for arbitrary coordinates, with no bounded
search domain or random seed. Only cardinality 64 uses finite kernel reduction.
No new solver, exporter, certificate format, dependency or verification layer
was introduced. Six public theorems and their dependencies enter `Audit.lean`.

Rechecked the live primary Clift page and diagram; both hashes match 22 October.
URLs, access time and version hashes are recorded in
`data/2026-10-23-orientation-source-recheck.json`. Only the selected parent graph
is used. Re-inspected the adapted formal-conjectures definitions, retained
uncompiled Scholz statement and Apache-2.0 licence. The unproved target remains
outside the compiled library. Lean 4.27.0 and mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900` remain pinned.

Initial elaboration tried vector notation and Matrix simplification lemmas not
imported by this module. Replaced them with an explicit function on Fin values;
no extra import was needed. The attempted `Fintype.card_fun` lemma was likewise
unavailable; the 64-choice count closes by `decide +kernel`. Removed unused
simplification arguments. No mathematical obstruction or failed search occurred.
Final standalone compilation passed without warnings in 5.36 seconds at default
heartbeat limits.

Commands:

    cd lean
    /usr/bin/time -p lake env lean ScholzBrauer/Clift109Normalize.lean
    cd ..
    uv run scripts/verify_integration.py --output results/2026-10-23-integration-orientations.json

Required integration passed once in 216.847775 seconds using
Python 3.11.6: all 29 commands passed, Lean 4.27.0 built successfully
in 17.118742 seconds, and the 259-theorem audit passed in
9.853275 seconds using only propext, Classical.choice and Quot.sound.
All 121 recorded input hashes matched on independent readback; the suite
verified five vendor hashes. The changed proof contains no placeholders,
custom axioms or native_decide. Full source/documentation diff and structured
integration evidence reviewed; git diff --check passed. Remote CI was not checked.
