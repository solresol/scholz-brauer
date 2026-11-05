# Kernel sparse-domain refinement — 6 November 2026, Sydney

Scheduled trigger: 5 November 2026, 21:00 UTC (6 November, 08:00 Sydney).
Active obligation: the Lean exclusion of a 108-doubling labelling of Clift's
selected 109 parent graph. Its exact computational minimum remains 109.

## Mathematical increment and scope

The preceding run proves both `threePairCompatible u d1` and its reverse,
but evaluates the 606-to-344 refinement only in Python. This run supplies a
kernel-evaluable exclusion for those predicates and transports the resulting
finite domain to the original graph-labelling hypotheses.

`Clift109SparseCheck.lean` first proves that XOR of powers of two encodes the
multiplicity parity of a nonnegative integer multiset. Reducing residues before
encoding therefore retains the exact `oddLabels` fingerprint, including repeated
residues and cancellations. Each three-pair-plus-singleton fingerprint forces

```
edge(x) XOR edge(y) = intervalFingerprint XOR edge(z) XOR singleton(s),
edge(x) = 2^x XOR 2^((x+d) mod m),  0 <= x,y,z,s < m.
```

At any set bit q of an edge, its start is either q or (q-d) mod m. At any set
bit of a nonzero XOR of two edges, at least one of its edges contributes that
bit. Trying those two starts and removing the chosen edge thus recognizes
every possible two-edge XOR. The zero XOR and a zero individual edge are
handled explicitly. A bounded structural top-bit scan is proved correct under
the established mask-width bound; no machine-word or overflow assumption is
used. Only the m-squared possibilities for (z,s) need finite evaluation.

`Clift109SparseChecks00.lean` through `Clift109SparseChecks12.lean`
kernel-reduce 131 failing directions, grouped into thirteen modulus modules.
`Clift109SparseChecks.lean` composes their membership proofs, covering
262 ordered pairs after swapping. `Clift109SparseDomain.lean` defines the
remaining `sparseStepPairs`, checks its cardinality 344 and proves
`sparse_pairs_of_budget`: every original labelling with seed 1, all selected
production equations, outgoing shift/cap inequalities, endpoint M109 and total
cap budget at most 108 has (u,d1) in that domain. This theorem uses the existing
normalization, positivity, packing and sparse-fingerprint theorems.

This is a **necessary 344-pair domain**, not a feasibility theorem. The domain
still contains (2,3), itself kernel checked. The proof does not establish that
any retained pair has a whole interval configuration or feasible caps, does not
prove min(u,d1)=1, and does not close the selected-109 exclusion or prove a new
Scholz instance. Exact equivalence of the lookup checker with every positive
sparse predicate is unnecessary and is not claimed. The previous Python
evaluation of both directions is still available as computational evidence.

## Reproducibility and controls

The generator reuses the immutable preceding report (SHA-256
`4c9ce9bafd676be265d58ee3c22d3489ee30197670246f2cafd77e383f30504a`).
It compares a top-bit implementation with all 606 saved directional decisions,
already checked by exhaustive odd supports and independent cycle recurrence,
then chooses one failing direction per removed unordered pair. Its emitted
Lean statements are independently checked by the kernel; the generator and
saved negative decisions are not trusted premises.

```
python3 scripts/export_lean_sparse_checks.py \
  --check --report results/2026-11-06-sparse-check-chunk-export.json
python3 scripts/export_lean_sparse_checks.py --check
```

Python 3.12.14, standard library only, no random seed, hard 60-second bound.
The final source-reproduction and 606-decision comparison took 0.506427 seconds.
There are 204,792 finite (z,s) targets across the 131 emitted checks in thirteen
modules. Each residue lies in 0..m-1, and the largest modulus is 58. No interval enumeration or unrestricted
solver was run.

The existing selected-109 certificate regression passed: 216 configurations,
all 3,456 negative cycles, exact minimum 109, a replay of 120 additions and
seven rejected corruptions. This checks saved computational evidence and does
not turn its whole-graph minimum into a Lean theorem.

```
python3 scripts/check_clift109_box.py \
  results/2026-10-18-clift109-box-exclusion.json
```

## Environment, sources and verification

Read the published `/workspace/shared/theorem-provers/START.md`; the saved Start
skill was absent from the catalog and the checkout's `.agents/skills` location.
No applicable AGENTS.md was present. The published Start gate passed before
research, with no dependency preparation or environment publication. The clean
`work` checkout at `86d8906c7dbc9b495d7bc32cfa7325dbddc1034c` equalled freshly
fetched live main; ancestry counts were 0/0 and ff-only refresh was already
current. GitHub's primary API independently confirmed public repository ID
1368051643, `solresol/scholz-brauer`, main, with the authorized HTTPS origin.
No competing research process or run marker was found; this run held an
exclusive repository marker during the work. Sibling checkouts and published state are read-only.

Reviewed the latest available weekly handoff,
[30 October](2026-10-30-literature-review.md), seven days old in Sydney.
No later handoff was present; no fresh broad literature search or current
novelty claim is made. No new external mathematical theorem is relied on.
The primary [Clift account](https://www.additionchains.com/ScholzBrauer.html)
and [selected diagram](https://www.additionchains.com/LargeNonHansen.png) were
accessed 5 November UTC / 6 November Sydney. Both hashes match the preceding
access. The page is undated; content hashes identify its version. Source URLs,
timestamps, sizes and hashes are in
`data/2026-11-06-sparse-check-source-recheck.json`. Only the actual selected
graph and cap interpretation are used; the published exclusion is not assumed.

Lean 4.27.0 and mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900` are preserved. All commands use
the absolute installed tools returned by `prepare.m.installed_tools`,
`prepare.env_for('scholz')`, the Scholz archive directory and LEAN_NUM_THREADS=2.
Costly commands use the published runner's unchanged 2 GiB disk reserve,
12 GiB process-group RSS limit and 1,800-second command limit. No limit was
raised. Pin hashes, clean exact dependency HEADs and five vendored primary
source hashes were rechecked.

Development probes: direct triple-mask evaluation was stopped as too expensive,
without a result or exclusion claim. A merge-sort formulation did not kernel
reduce its well-founded recursion and was discarded. A first logarithmic
top-bit formulation was replaced by structural bounded scanning. The final
general checker and the individual (58,5) exclusion passed before the full
generated build; the latter took 21.019 guarded seconds. These probes motivate
the quadratic checker and add no extra mathematical assumptions.

The first monolithic batch reached the unchanged 1,800-second command limit.
It is inconclusive, with no completed module claimed. Its exact generator and
source are retained under `research-drafts/2026-11-06/`, and its failure log is
`2026-11-06-sparse-check-monolithic-timeout.txt`. The active proof divides the
finite checks by modulus and composes them as membership implications, avoiding
a combined Boolean computation. Each modulus module uses the same published
resource guard, and all thirteen are built sequentially. The modules for 53,
56,57,58 import their predecessor, retaining a chain of the larger checks.
No limit was increased.

An assembly tactic mismatch was corrected with `List.forall_mem_append` and
per-row membership implications; no finite modulus checks were repeated. The
short failed assembly build is retained in
`2026-11-06-sparse-check-assembly-error.txt`.

Full pinned `lake build` passed **1,152 jobs** in
**37.049 guarded seconds**, after all thirteen modulus modules passed. This
includes all 131 finite rejections, the 344-pair cardinality and the graph-level
domain theorem. Recorded guarded
module times sum to 1693.263 seconds; the first modulus-52 compile
additionally took 504 seconds as reported by Lake. Its outer guard timing was
lost during a connection refresh; a cached build verified the matching source
and artifact in 2.006 seconds before resuming. The full final-build transcript
is `2026-11-06-sparse-check-build.txt`.

`lake env lean Audit.lean` passed **362 entries** in
**24.019 guarded seconds**. The existing fail-closed
`verify_integration.check_axioms` verifies exact agreement with `Audit.lean`
and permits only propext, Quot.sound and Classical.choice. Twenty-eight new
public entries include the 131 finite facts transitively. No placeholder, native
decision shortcut, project axiom or assumed target is used. The transcript is
`2026-11-06-sparse-check-audit.txt`; exact argv, bounds, pin checks and source
hashes are in `2026-11-06-sparse-check-verification.json`.

Full integration is **not rerun**: the unchanged chain-9 evidence checker
previously timed out at 180 seconds, and this increment does not address that
obstacle. That outcome remains inconclusive. No remote CI success is claimed.

## Next obligation

Combine the now kernel-checked 344-pair necessary domain with actual exceptional
positions, box dissociation, both odd-run restrictions, twelve critical families
and 64 orientations to finish interval/cap classification. The top-pinned box
branch and the branch missing 8 remain distinct constraints to handle. No
completed 109 or 5,784,689 enumeration needs rerunning.
