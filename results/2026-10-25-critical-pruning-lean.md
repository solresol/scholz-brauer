# Critical-path pruning — 25 October 2026

Sunday, Australia/Sydney. Milestone 3 advanced; milestones 1 and 2 remain
complete. Clean main 4ff74d3 fast-forwarded to 8e4ae2a, bringing in the weekly
literature review. The intended origin was verified; process cwd checks found
only this run's runtime and retained runtimes from yesterday, no competing
research process. No unrelated changes were present.

## Closed obligations

A critical path cannot miss both 8 and 15. If it misses 8, its cap is zero,
so a15=b23=0. The third route difference is then a23, which is positive by
box dissociation; hence cap15 is positive and 15 must be on the critical path.
Filtering the previous fifteen tail families leaves twelve (kernel evaluation).
The finite graph also forces any remaining path missing 8 to visit 5 and 7.
These are necessary families, not feasible labellings. This count is established
for the selected 109 graph, independently of the earlier large-graph count.

The second closed obligation connects path membership to the 64-weight box.
The small `throughWeights` recursion was needed because the existing unfiltered
path multiset loses whether a path visits 8. Its membership proof reuses the
existing Path induction; expanding the fixed graph gives exactly `box a b`.
A critical path through 8 contributes weight 108 to that box. Every subset sum
is at most the sum of its differences; the existing upper bound therefore
becomes equality: offset + sum(differences) = 108.

`critical_twelve_of_budget` combines pruning, saturation, zero skipped caps,
the conditional box-top equality and the missing-8 detour condition. No new
solver, exporter, certificate format, dependency or research search was added.
The full 109 exclusion/minimum remains computational; no new Scholz instance,
source/Mersenne optimum, general extension or novelty is claimed.

## Sunday assessment and next obligation

The current symbolic strategy closed further obligations, so no representation
reset is needed. The twelve-family split now supplies two concrete next cases:
use the fixed box offset when 8 is visited, and exploit mandatory 5,7,15 and
zero cap8 otherwise. Finite interval classification and kernel exclusion remain.
Do not assume every critical path visits 8 or rerun completed enumerations.

The fetched weekly literature review was read before choosing work. Its scoped
findings supply no checked replacement for this reduction; no external theorem
was imported. Clift's live page and PNG were retrieved and both SHA-256 hashes
match 24 October; URLs and access date are in the accompanying source record.
The adapted formal-conjectures definitions, Apache-2.0 licence/provenance and
separate uncompiled Scholz statement were inspected. The open target is neither
imported nor assumed. Existing Lean 4.27.0/mathlib pins are unchanged.

## Verification and failed approaches

Exact symbolic proofs plus finite kernel evaluation of graph facts; no random
seed or heuristic experiment. A first edit command used the wrong working
directory and changed nothing. The first Path induction proof accidentally
referred to the outer vertex in its older case; explicitly binding the induction
case vertex fixed it. Simplification closed the box identity directly, so an
extra ac_rfl and unused simp argument were removed. No failed mathematical
hypothesis is recorded. Final standalone compilation passed without warnings
in 6.14 seconds at default heartbeats.

Commands (Lean commands from lean/):

    /usr/bin/time -p lake env lean ScholzBrauer/Clift109Normalize.lean
    uv run scripts/verify_integration.py --output results/2026-10-25-integration-critical-pruning.json

Required integration passed once in 222.73589 seconds: 30 commands, 273
audited theorems with only the permitted standard axioms, all 122 input hashes
independently read back and five vendor hashes checked. The integration command
includes its existing bounded computational regressions; these are validation,
not new research experiments. The complete source/documentation diff and
structured report were inspected, and git diff --check passed. Remote CI was
not checked.
