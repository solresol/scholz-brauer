# Joint halving-step packing — 3 November 2026

Tuesday, Australia/Sydney. Active milestone 3; milestones 1 and 2 remain
complete. Clean main at 42fb162, correct origin, fetch/ff-only already current;
no competing research process found. Read the previous residue result and the
30 October weekly literature checkpoint before choosing this obligation.

## Completed mathematical reduction

`Clift109Packing.lean` proves that a nonnegative k-dimensional box with distinct
subset sums has span at least 2^k-1. The proof embeds the subset-sum multiset
in the integer interval from zero to the sum of its dimensions and compares
cardinalities. It also proves that deleting dimensions preserves dissociation.

Apply this first to all six dimensions, and then to the four dimensions left
after removing u and d1. The six-dimensional box requires span at least 63;
the four-dimensional box requires at least 15. Consequently every hypothetical
budget-108 labelling of the selected 109 graph satisfies:

- box offset at most 45;
- offset + u + d1 at most 93, hence u+d1 at most 93;
- u and d1 are distinct (transported from the existing dissociation theorem);
- both belong to yesterday's 27-value residue domain;
- min(u,d1) at most 29, since all larger domain entries are at least 51.

The final `joint_steps_of_budget` theorem carries these joint step restrictions
all the way from the original base equations and outgoing cap bounds. No
assumption about feasibility, enumeration completeness or the target is added.
This excludes all 64 ordered pairs with both steps in 51..58; excluding equal
steps leaves 646 of the original 729 necessary pairs. This count is a separate
exact Python comprehension over the explicit domain (0.000051 seconds,
Python 3.9.6, deterministic, no seed), not a count of feasible configurations:
`[(u,d) for u in steps for d in steps if u != d and u+d <= 93]`.

The generic packing theorem and its application close a joint pruning obligation.
They do not finish interval classification, prove min(u,d1)=1, rule out every
budget-108 labelling, prove a minimum Mersenne length, or prove general Scholz.
The full selected-109 exclusion remains computational in this repository.

## Validation and proof development

Standalone `lake env lean ScholzBrauer/Clift109Packing.lean` from `lean/`
passed without warnings in 8.15 seconds. Proof development required an explicit
order split for the natural gap/integer absolute-value identity and simplifying
the empty-list case in residue membership; neither was a mathematical obstacle.
No new infrastructure, exporter, certificate format, solver or dependency.

Lean 4.27.0 and pinned mathlib are unchanged. Inspected the adapted upstream
addition-chain definitions and the archived Scholz statement with Apache-2.0
attribution; the open upstream target is not imported or assumed.

Integration command: `python3 scripts/verify_integration.py --output
results/2026-11-03-integration-packing.json`. Passed once in 268.953655 seconds: all 30 commands, full build (1133 jobs;
12.941229 seconds), and 314-theorem audit with only propext, Classical.choice
and Quot.sound. Independently matched all 126 recorded input hashes; five
vendored hashes checked. Mathematical summaries agree with 2 November after
excluding execution metadata and command transcripts. Reviewed source/docs
diff and report; whitespace and proof-token checks clean. Remote CI not checked.

## Sources and next obligation

Reused the 30 October weekly literature review; no novelty or external frontier
claim. Rechecked the live primary [Clift account](https://www.additionchains.com/ScholzBrauer.html)
and [diagram](https://www.additionchains.com/LargeNonHansen.png). Both SHA-256
hashes match 2 November; access date and hashes are in
`data/2026-11-03-packing-source-recheck.json`. Only the selected parent graph is
used, not any published optimality or computational exclusion assertion.

Next combine the smaller necessary pair domain with exact exceptional-residue
fingerprints, odd runs and the twelve critical families/64 orientations to
finish interval/cap classification. The 646 pairs are still a loose superset;
repeating the completed large search does not supply the missing Lean proof.
