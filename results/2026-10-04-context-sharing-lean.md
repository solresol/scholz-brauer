# 4 October 2026 — sound context sharing; full exclusion still incomplete

Sunday, Australia/Sydney (AEDT). Milestone 1 was already complete. Milestone 2
advanced through a proved context-sharing argument and a checked terminal-gap
portion, but **the numerical interval remains `16 ≤ ell(12509) ≤ 17`**.
The optimum 17 and the end-to-end Scholz instance are still computational results,
not completed Lean theorems. No new numerical bound was obtained today.

## Completed proof obligations and exact result

`ChainReach.enlarge` proves that reachability from a prefix implies reachability
from any superset of its values, with the same endpoint and step budget. Hence
exclusion on a superset rules out every included actual prefix. The superset
need not itself be an addition chain. Node identity alone still proves nothing.

`checkContext_sound` and `checkContext_lower_bound` formalise the corresponding
local-certificate argument. Each state checks its endpoint envelope, coverage
of all viable next sums, and every child: parent values are retained, the new
value is included, the endpoint matches, and the remaining budget decreases.
The checker tests a sublist relation; soundness uses only subset inclusion.
Induction on the budget requires all lookup states to pass, without assuming
table order, a Python equivalence or an unproved target.

An exact experiment groups all 1,345,873 occurrences of the existing certificate
by `(node, budget, endpoint)` and unions their prefixes. The naive hypothesis
that these unions preserve the original edges is **false**. Of 29,859 initial
groups, two require new edges:

- Node 29162, budget 2, endpoint 7168: `5120 + 6144 = 11264` is a new viable sum.
- Node 29372, budget 2, endpoint 8192: new sums 8960, 9472, 9728, 10496,
  10752 and 11264 appear.

The summands arise across contexts that were separate in the original traversal.
Skipping these sums would invalidate coverage. Six additional gap contexts
handle all seven edges (the 11264 context is shared as a checked union).
The completed compression has 29,865 states, 546,523 value entries and 195,752
edges. Every local condition was checked in exact Python arithmetic after construction;
the existing independent checker separately replayed the original DAG. These
computational checks do not establish full Lean acceptance.

The active-value filter has a proved justification: if `n ≤ (a+b)*2^k` and
`b ≤ m`, then `n ≤ (a+m)*2^k`. Both summands of a viable pair survive the filter.
Across the compressed data this reduces potential ordered pairs from 25,509,935
to 1,806,894. These are operation counts, not new optimality searches.

## What the kernel actually accepted

The general soundness and lower-bound bridge compile. The new abstraction also
checks the small 7/3 exclusion and rejects five corruptions: missing inherited
value, missing new value, false widened gap, wrong endpoint and wrong budget.
The previously proved `ell(7)=4` is unchanged.

`Exclusion12509ContextsData.lean` compiles the complete table as constructor data.
`Exclusion12509Part00.lean` kernel-checks the first 78 chunks, comprising states
0 through 2495. `Exclusion12509Partial.lean` aggregates their acceptance in
`contexts12509_prefix_checked` and proves `contexts12509_gap_excluded`: every
gap-labelled context selected from that checked prefix excludes its target.
The proof uses a constant lookup for a gap rule, which has no child dependencies;
it does not assume acceptance of the unchecked remainder. The retained prefix
contains all 429 gap contexts, plus 2067 split contexts. It is **not** a complete
root exclusion, and it does not prove that every source path has reached a
checked state. The formal source interval remains [16,17].

No candidate optimality or full Scholz theorem is imported. The exporter can
produce the remaining candidate parts and final theorem, always reporting
`lean_proof: false`; generation is not kernel acceptance.

## Resource limits, failures and changed strategy

Commands, timestamps and outputs are in `2026-10-04-context-exclusion-probes.json`.
Probes used one Lean worker and a 2048 MB Lean allocation limit. The normal Lake
builds used the pinned toolchain without an explicit allocation cap. Some short
probes overlapped builds; substantial host memory/CPU contention means these are
resource observations, not controlled benchmarks.

- The old context-specific representation passed a 523-occurrence subtree in
  54.481574 seconds, including data preparation. Source node 2652, prefix
  `[1,2,3,5,10,20,40,80,160,320,640,960]`, five remaining additions; 39 fragments.
- Whole-table lookup during a 32-context check exceeded 2 GB after 38.710978
  seconds. Selecting a chunk before evaluating its data passed nine sampled
  batches in 58.584172 seconds; the sample was not sufficient to predict full cost.
- The complete single-module proof attempt timed out at **1500.021954 seconds**,
  with no successful completion. No lower bound follows from that timeout.
- Twelve separately compiled modules allow at most three concurrent proof jobs
  and preserve completed work. This attempt timed out at **1800.044418 seconds**.
  Only Part00 completed, in **1184 seconds**. Its checked source and compiled
  checkpoint were retained; the unverified remainder was moved outside the library.
- A hierarchy of separately named lookup functions showed no improvement on the
  same sample (63.091344 seconds) and was discarded. A terminal-batch profile with
  dummy versus real lookup took 3.58 versus 3.40 seconds; it did not support an
  unused-lookup bottleneck. Direct Boolean sublist checking took 11.46 versus
  12.82 seconds in one loaded-host split-group probe and was not retained.
- A scratch Lean residue-envelope proof passed, but moduli `2,4,...,16384`
  pruned **zero** of 1,345,873 original occurrences (23.912750 seconds). This
  unsuccessful approach was not added to the library.

At 08:58 AEDT the eight-CPU, 16 GB host had load average 27.29, about 15 GB used
and 6 GB compressed memory. Overlapping probes were stopped. All research jobs
from this run were stopped or completed before finalisation.

**Reassessment:** context sharing closes a missing soundness obligation, but the
list-based full evaluation still exceeds the measured budgets. Do not repeat
these whole builds unchanged or discard the successful checkpoint. Next profile
compact set-based inclusion/coverage on expensive split contexts under a small
kernel budget, checking support for exact operations before implementing another
representation. Preserve a formal soundness bridge and reuse accepted facts.
The remaining obligation is still full kernel acceptance, followed by optimum 17
and combination with the already proved Hansen bound 12525. Milestone 3 is deferred.

## Inputs and reproduction

Input: `results/2026-09-25-12509-exclusion-certificate.json`, SHA256
`516a54800a296da300cc15da318c40b06b08a18270c93b8467f3f843a8b074e9`.
Its 29,437 syntax nodes cover 1,345,873 contextual occurrences. The existing
independent checker replays all occurrences before export. Exact integers,
Python 3.11.6, no random seed. The compression is not a new minimum-chain search.

Pins are unchanged: Lean 4.27.0, mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`, formal-conjectures
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`. Reinspected the vendored definitions,
open Scholz statement and Apache-2.0 provenance. The open target is not imported.

Generate into fresh paths from the repository root:

```sh
python3 scripts/export_lean_contexts.py --data-output /tmp/Contexts.lean --proof-output /tmp/Optimal-candidate.lean --parts-output /tmp/context-parts --prefix-parts 1 --prefix-output /tmp/Partial.lean
python3 scripts/verify_integration.py --output results/integration-local.json
```

Integration compares the retained data, Part00 and partial aggregate byte for
byte, builds the retained library and audits its transitive dependencies. The
remaining candidate files are deliberately not compared as compiled artifacts
or counted as completed proofs. The CI timeout was raised to 60 minutes because
the retained checkpoint itself took about twenty minutes in its measured first
compilation; no new scheduled jobs or remote runners were added.

Final integration passed in **108.402295 seconds**, with **121
explicit theorem audits**, 68 input hashes and 5 vendored-file hashes. Only
`propext`, `Quot.sound` and `Classical.choice` appear; no custom axiom, `sorryAx`,
native acceptance oracle or assumed Scholz theorem. The retained partial module
and its gap-exclusion theorem compiled successfully. Results:
`results/2026-10-04-integration-checks.json`. The full diff and generated retained
files were reviewed; unverified candidate files are outside the compiled library.

## Source recheck

On 4 October, re-read [OEIS A349044](https://oeis.org/A349044) and
[Clift's notes](https://www.additionchains.com/ScholzBrauer.html). Both displayed
17-addition witnesses match the stored chains. These live pages supplied no
immutable revision; details are in `data/2026-10-04-source-recheck.json`.
Their optimality claims are not assumptions in the Lean development.

Clift's small non-Hansen source `[1,2,4,8,9,13,16,29]` remains the next lead for
milestone 3. No extension experiment was run today. Larger reported obstructions,
optimality and novelty claims remain outside the verified results.
