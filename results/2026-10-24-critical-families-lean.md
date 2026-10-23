# Critical-path families and oriented zero constraints — 24 October 2026

Saturday, Australia/Sydney. Milestone 3 advanced; milestones 1/2 remain complete.
Clean main c82c64d fast-forwarded to f9b112c after confirming the intended origin.
Process inspection showed this run's Node runtimes and transient commands only.
The fetched changes add a weekly literature requirement and improve integration
failure diagnostics; they do not change mathematical source.

## Completed obligation

For any labelling of the selected 109 graph with seed 1 and terminal M109,
box dissociation forces positive differences at the three doubling steps.
Their common parent caps at 1, 2 and 4 must therefore be positive. At budget
108 the critical-path theorem forces all three parents onto the path.

`tailPaths` is a finite recursion on the existing parent-step list.
`Path.tails_mem` proves erasure of every actual path belongs to it, independently
of edge shifts. Filtering for the three mandatory vertices leaves exactly
fifteen tail sequences, counted with `decide +kernel`. This is a necessary
superset: it neither asserts feasibility nor identifies these with the twelve
families reported for a different, run-generalised graph.

`critical_fifteen_of_budget` retains path validity, weight 108, saturation of
all visited caps and zero caps outside the path. `oriented_critical_constraints`
combines it with the normalized integer interval 0..108 and six-bit orientations.
All oriented edge expressions lie between zero and their original cap; every
edge out of a skipped tail equals zero. This closes the combination of finite
critical paths with normalized cap constraints. No bound is imposed on gauge
potentials. The remaining task is to prune interval configurations and prove
finite exclusion; the full 109 exclusion and minimum 109 remain computational.
No new Scholz instance, source/Mersenne optimum or novelty is claimed.

## Method, provenance and checks

Exact symbolic Lean proof, with finite kernel evaluation only for graph facts
and cardinality 15. No random seed, heuristic search or new research enumeration.
The small finite tail recursion is needed to turn the existing existential path
into explicit cases; no exporter, checker format, solver or dependency added.
No failed proof approaches this run. Standalone final compilation passed without
warnings in 7.14 seconds at default heartbeats.

The live Clift page and diagram match the preceding recorded hashes; URLs,
access time and version hashes are in `data/2026-10-24-critical-source-recheck.json`.
Only the selected graph is relied on. The new roadmap's weekly human-authored
literature findings were not found in the repository; broader current literature
was not assessed. This limitation does not affect the internal Lean implication.
Inspected the adapted upstream addition-chain definitions, pinned provenance and
Apache-2.0 header, and the separate uncompiled open Scholz statement. The target
is not imported or assumed. Lean 4.27.0 and mathlib's existing pin are unchanged.

Commands:

    cd lean
    /usr/bin/time -p lake env lean ScholzBrauer/Clift109Normalize.lean
    cd ..
    uv run scripts/verify_integration.py --output results/2026-10-24-integration-critical-families.json

Required integration passed once in 219.813415 seconds: Python 3.11.6,
30 commands, Lean 4.27.0 / 1,128 build jobs (18.275108 s), and 264 audited
theorems (10.174235 s) with only propext, Classical.choice and Quot.sound.
All 122 recorded input hashes matched independent readback and five vendor
hashes were checked. The extra integration command/input comes from the fetched
runner regression, not new research infrastructure. The changed Lean module has
no sorry, custom axiom or native_decide. Complete proof/documentation diff and
structured integration evidence reviewed; git diff --check passed.
Remote CI was not checked.
