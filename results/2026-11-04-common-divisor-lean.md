# Common-divisor obstruction — 4 November 2026, Sydney

Active obligation: kernel-checked interval/cap classification for a hypothetical
108-doubling labelling of Clift's selected 109 graph. The full arbitrary-label
minimum of 109 is already an exact computational result; this run does not
repeat that enumeration or promote it to a Lean theorem.

## Runtime and source gate

The selected runtime reported configuration version
`f4c4ae6d-5a2c-43a6-a161-c34781e84e76~cecfgver_6aea433dd60c81a2acd44e4790f53979`.
The published Start gate passed for all three prepared projects, without
installation, cache retrieval, preparation or shared-environment changes:

```sh
source /workspace/shared/theorem-provers/env.sh
python3 /workspace/shared/theorem-provers/check.py
```

Only `/workspace/scholz-brauer` was edited. It was clean on branch `work`,
origin `https://github.com/solresol/scholz-brauer.git`, at
`4d351b1aa302819ceb0ff9b7f2832cbb69c37616`, equal to freshly fetched and live
`origin/main`; `git merge --ff-only origin/main` reported already up to date.
No competing research process or existing run lock was found; an exclusive
temporary `.git/scholz-brauer-research.lock` protected the run. No applicable
AGENTS.md was found. Sibling checkouts and the published runtime were unchanged.

Read TODO, the latest relevant research log/results, and the Lean reductions
before choosing this lemma. Reused the 30 October weekly literature handoff;
no new external theorem is needed. The live primary
[Clift account](https://www.additionchains.com/ScholzBrauer.html) and
[selected diagram](https://www.additionchains.com/LargeNonHansen.png) were
accessed on 3 November UTC / 4 November Sydney. Their SHA-256 hashes match
3 November, as recorded in
`data/2026-11-04-common-divisor-source-recheck.json`. Only the selected graph
is used, with its actual parent choices; no published optimality assertion
is assumed. Inspected the adapted upstream addition-chain API, archived open
target and Apache-2.0 attribution; the open target is not imported.

## New kernel-checked reduction

`Clift109CommonDivisor.lean` uses the shape, rather than just the cardinality,
of the seven source-side exceptions. They are three translated pairs at step
d1 and the singleton A3+p. The other 102 weights are 51 pairs at step u.
Modulo any common divisor d of u and d1, all these pairs contribute evenly.
Consequently the odd-residue fingerprint of the entire interval 0..108 is
exactly the singleton `{(A3+p) mod d}`. Multiplicities and signed coordinates
are retained throughout; no carry-free or distinct-residue hypothesis is added.

For d=gcd(u,d1), the previous positivity and min(u,d1)≤29 give 1≤d≤29.
A kernel decision over these thirty Fin cases proves that the interval has
exactly one odd residue iff d divides 54 or 55. Thus every original labelling
satisfying the terminal equation and outgoing cap budget satisfies the new
gcd restriction. The proof is transported from the proved normalization,
halving and packing theorems, with no finite-enumeration completeness premise.

The finite set `commonDivisorPairs` retains both 27-value residue domains,
unequal steps and sum at most 93, and adds the gcd condition. Lean proves its
cardinality is **606** and proves every budget-108 labelling's pair belongs to
it. This removes 40 ordered pairs from the previous 646. For example, (4,8),
(7,14), (13,26), (17,51), (19,57) and (29,58), and their reversals, are excluded.
The generic common-divisor theorem also retains the exact exceptional residue
phase for subsequent classification.

This is a necessary domain, not 606 feasible configurations. It neither proves
min(u,d1)=1 nor finishes interval/cap classification or the selected-109 Lean
exclusion. No new Scholz result, Mersenne optimum or novelty claim is made.

## Verification and reproducible arithmetic check

Lean 4.27.0 and mathlib revision
`a3a10db0e9d66acbebf76c5e6a135066525ac900` are unchanged. Commands use the
absolute binaries returned by `prepare.m.installed_tools`, the environment
from `prepare.env_for('scholz')`, `LEAN_NUM_THREADS=2`, and the Scholz archive
directory. Costly commands run under the published guarded runner's existing
2 GiB reserve, 12 GiB process-group RSS and 1800-second timeout.

Standalone `lake env lean ScholzBrauer/Clift109CommonDivisor.lean` passed
without warnings in 44.071 guarded seconds, at default heartbeats. An initial
36.061-second attempt exposed only a missing singleton-count simplification;
an explicit equality split fixed it. No unfinished draft is retained.
Seven new public theorems are included in `Audit.lean`.

The unchanged full integration invocation was
`python3 scripts/verify_integration.py --output
results/2026-11-04-integration-common-divisor.json`, executed through a temporary
launcher that resolves Lean/Lake command arguments to the installed absolute
binaries and uses the published guard. It stopped after 405.668 guarded seconds:
the existing chain-9 evidence checker reached its unchanged 180-second limit:

```sh
python3 scripts/check_clift5784689.py \
  results/2026-10-19-clift5784689-chain9.json \
  --detour results/2026-10-19-clift5784689-chain9-detour.json
```

No subprocess output was returned; this attempt is inconclusive. The five
preceding checks returned successfully, including the existing 109 neighborhood
regression and all 3,456 saved selected-109 budget certificates. The integration
runner writes a report only on total success, so no successful full report was
created. The bounded failure and successful-prefix evidence limits are recorded
in `results/2026-11-04-integration-common-divisor-timeout.json`. No timeout,
resource limit, source pin or test was changed, and no larger-graph search was
restarted. The full direct pinned Lean build subsequently passed **1135 jobs**
in **58.772 guarded seconds**, including the new module and library root.
The direct axiom audit then passed all **328** entries in **41.220 guarded
seconds**, using only the permitted standard axioms propext, Quot.sound and
Classical.choice. Its complete transcript is
`results/2026-11-04-lean-audit.txt`; the checked command, source/input hashes,
pin/dependency recheck, five vendor hashes and audit parser result are in
`results/2026-11-04-common-divisor-verification.json`. The new proof has no
placeholder, project-defined axiom, native decision shortcut or assumed target.
The full staged source/evidence/documentation diff was reviewed; recorded hashes
match the staged files and the whitespace check passes. Remote CI was not checked.

An independent standard-library Python 3.12.14 recount compares divisibility
with exact residue multiplicity, using these complete input bounds:

```python
from collections import Counter
from math import gcd
steps = [1,2,3,4,5,6,7,8,9,11,13,14,17,18,19,26,27,28,29,
         51,52,53,54,55,56,57,58]
old = [(u,d) for u in steps for d in steps if u != d and u+d <= 93]
new = [(u,d) for u,d in old if 54 % gcd(u,d) == 0 or 55 % gcd(u,d) == 0]
recount = [(u,d) for u,d in old
           if sum(n % 2 for n in Counter(i % gcd(u,d) for i in range(109)).values()) == 1]
assert new == recount and len(old) == 646 and len(new) == 606
assert len(set(old) - set(new)) == 40
```

The check took 0.041979 seconds, with no random seed or external dependency;
the full removed-pair list, bounds, base commit and Lean source hash are in
`results/2026-11-04-common-divisor-pairs.json`. This recount is separate from
the kernel-checked cardinality theorem and is not an optimality experiment.

## Next obligation

Combine this 606-pair domain and its exact common-divisor residue phase with
the existing individual residue fingerprints, both odd-run restrictions,
twelve critical families and 64 orientations. The outstanding obstacle is a
small complete interval classification followed by cap infeasibility; the
pair restrictions alone still leave a loose superset. In particular (2,3)
survives all current pair tests, so the common-divisor argument cannot itself
establish min(u,d1)=1. Its singleton residue phase must be combined with the
actual exceptional positions and interval/cap constraints. No completed search
needs rerunning or a higher solver timeout.
