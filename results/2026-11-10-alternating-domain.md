# Alternating fingerprints — 10 November 2026, Sydney

Scheduled trigger: 9 November 2026, 21:00 UTC / 10 November, 08:00 Sydney.
Active obligation: exclude every 108-doubling labelling of Clift's selected
109 graph in Lean. The graph's exact computational minimum remains 109.

**The necessary halving-step domain is now kernel checked at 278 ordered
pairs, down from 344, with transport to every original budget-108 labelling.**
The full build and 423-entry axiom audit pass. The full selected-109 exclusion
remains open; (2,3) still belongs to the necessary domain.

## Mathematical increment

For a positive regular step m, define

```
D_m(x) = (-1)^(floor(x/m)) * 4^(x mod m).
T_m = sum(D_m(i), i=0,...,108).
E_(m,d)(x) = D_m(x) + D_m(x+d).
```

The Lean definition uses the parity of the integer quotient, so signed x is
allowed. Translation by m negates D_m. Consequently every regular m-pair
cancels in the signed sum of the exact interval equation already proved in
`Clift109PlacedPairs.lean`. Any placement of three d-pairs and singleton s
therefore satisfies

```
T_m = E(x) + E(y) + E(z) + D_m(s),
0 <= x,y,z; x+d,y+d,z+d < 109; 0 <= s < 109.
```

This uses actual position information that multiplicity parity modulo m loses.
It is a necessary scalar invariant: no injectivity, carry-free assumption,
equivalence to placement, or arithmetic uniqueness of radix four is assumed.
Repeated pair starts and overlapping endpoints are permitted in the finite
relaxation. The exact placement theorem supplies the implication despite this
relaxation.

## Finite certificates and trust boundary

Let E be a candidate list covering all possible edge values, and let C be
any Boolean classifier. The checker verifies:

1. The saved target equals the defined T_m.
2. Every start in `range (109-d)` has its edge value in E.
3. C accepts the sum of every two entries of E.
4. Whenever C accepts `T_m - e - D_m(s)` for an edge e and singleton s,
   s belongs to the supplied allowed-singleton list.

The first two edges from any placement pass check 3; its third edge and the
proved signed equation then force its actual singleton into that allowed list.
`checkAlternating_sound` proves this implication. The balanced tree used for C
has no assumed sortedness or set-correctness theorem. Incorrect generated data
must still satisfy every coverage and rejection check. Extra accepted values
only add obligations in check 4.

The exporter supplies 48 certificates: 34 empty directional domains and both
directions for seven unordered pairs with disjoint singleton domains. The empty
directions remove 52 ordered pairs; shared-singleton incompatibility removes
14 more. Their two-edge classifiers contain 69,252 nodes in total.
`decide +kernel` verifies the finite checks; Python does not accept proofs.
The elaborator reifies only integer data and tree constructors.

The kernel-checked necessary domain has cardinality 278 and still contains
(2,3). Even an exact finite placement test lets the two directions use unrelated
halves and other coordinates. No box/cap feasibility or full graph exclusion
follows from these certificates alone.

## Reproduction and bounded evidence

```
python3 scripts/export_lean_alternating_checks.py --check \
  --report /tmp/clift109-alternating-recheck.json
```

Choose an unused report path; the exporter refuses replacement.
Standard-library Python, no random seed or
external solver, with a 60-second bound and measured runtime **0.427 seconds**.
It checks all 344 input pairs against the preceding complete
placement computation and records hashes, finite bounds and candidate domains.
Its `lean_proof: false` is intentional: builds and axiom auditing are separate.
Neither the old placement enumeration nor a completed graph search is repeated.

Project commands use `prepare.env_for('scholz')`, its isolated archive cache,
LEAN_NUM_THREADS=2, and the absolute Lean/Lake binaries from
`prepare.m.installed_tools`. Costly commands use `prepare.m.run` with the saved
2 GiB disk reserve, 12 GiB process-group RSS guard and 1,800-second bound.

After the mandatory Start gate, the final build and audit can be reproduced by:

```python
import sys
from pathlib import Path
sys.path.insert(0, '/workspace/shared/theorem-provers')
import prepare
env = prepare.env_for('scholz')
lean, lake = prepare.m.installed_tools(
    prepare.B / 'runtime', 'leanprover/lean4:v4.27.0', env)
root = Path('/workspace/scholz-brauer/lean')
for args in (['build'], ['env', str(lean), 'Audit.lean']):
    prepare.m.run([str(lake), *args], root, env, (root, prepare.B))
```

An initial unsplit large certificate was stopped after 216 seconds as observed
Lean RSS approached 10 GiB. Caching the target, naming data blocks and directly
reifying integer literals did not by themselves finish the large check in the
bounded probes; those probes were deliberately terminated, not successful
checks or mathematical exclusions. Their logs are retained separately. The
final proof composes small closed `List.all` checks and uses the core's
kernel-oriented integer comparisons. A representative two-edge-sum fragment's
cumulative type-checking time drops from 4.73 to 1.45 seconds. No comparison
correctness theorem is assumed: the arbitrary classifier must pass all coverage
checks. No resource limit was increased.

An initial conjunction-association error in batch assembly was corrected.
A premature file-layout change interrupted a later module after eight had
passed; the grouped layout and successful outputs were restored. The complete
final batch consists of nineteen passing modules. The largest successful
module takes **84.065 guarded seconds**. Logs retain the inconclusive stops,
assembly error and layout interruption; none is reported as a proof or
mathematical exclusion.

## Startup, sources and validation

The full published Start gate passed before research: exact tools and pins,
clean dependency HEADs, saved readiness receipts and representative imports for
all three projects. `/workspace/shared/theorem-provers/START.md` was read;
there was no applicable AGENTS.md or executor Start skill in the live catalog.
No installation, preparation, receipt fabrication or runtime repair occurred.
The clean `work` branch equalled freshly fetched origin/main at
`64947275a177ca571c21bb1ef9111182d4136004`. Ancestry was verified before creating
tracking main; work was preserved. The authorized origin is exactly
`https://github.com/solresol/scholz-brauer.git`. The parent launch verified
repository ID 1368051643 and checked terminal status of prior research threads.
No local competing research process or marker was present; this run created
its own exclusive marker. Only this checkout changes.

The [6 November weekly handoff](2026-11-06-literature-review.md) was read before
choosing work, including its HAL and publisher full-text access limits. It is
three UTC days old. No new external theorem or broad literature search is used.
[Clift's account](https://www.additionchains.com/ScholzBrauer.html) and the
[selected diagram](https://www.additionchains.com/LargeNonHansen.png) were
accessed 9 November 2026 UTC; both hashes match the preceding access. The
undated source versions, URLs, hashes and timestamps are in
`data/2026-11-10-alternating-source-recheck.json`. Only the graph and outgoing
cap interpretation are used, not the published exclusion or an optimum claim.

Lean 4.27.0 and mathlib a3a10db0e9d66acbebf76c5e6a135066525ac900 remain pinned.
The final `lake build` passes **1,175 jobs in 30.131 seconds**. Its only warning
is an unused simp argument in one generated two-chunk assembly.
`lake env lean Audit.lean` passes **423 entries in 21.134 seconds**;
`verify_integration.check_axioms` checks their exact order and permits only
propext, Quot.sound and Classical.choice. The 58 new public entries include
the finite restrictions, cardinality and original-graph transport; all their
private dependencies are covered. No placeholder, project-defined axiom,
native decision shortcut or assumed target occurs. Reviewed pin hashes,
exact clean dependency HEADs, shared deployment integrity and five vendored
source hashes pass.

The generator's exact-byte check and all 344 signed-domain decisions are in
`2026-11-10-alternating-candidates.json`; the preceding sparse exporter also
reproduces its unchanged proof sources. The saved selected-109 regression
passes all 3,456 negative cycles, the computational minimum 109, the
120-addition witness replay and seven corruption controls. That checker does
not make the graph minimum a Lean theorem.

Final evidence: `2026-11-10-alternating-batches.json`,
`2026-11-10-alternating-initial-batches-build.txt`,
`2026-11-10-alternating-batches-build.txt`, `2026-11-10-alternating-build.txt`,
`2026-11-10-alternating-audit.txt` and `2026-11-10-alternating-verification.json`.
The verification record includes hashes of every compiled new proof source.
The unchanged chain-9 integration timeout is not repeated and remains
inconclusive. No whole-integration or remote-CI success is claimed.

## Next obligation

Combine the retained actual exceptional positions with a common dissociated
box, both odd-run restrictions, the twelve critical families and 64 orientations
to finish interval/cap classification. Keep the branch through 8 with box maximum
108 separate from the branch missing 8, which visits 5,7,15. Matching singleton
positions alone supplies neither compatible remaining coordinates nor a feasible
cap assignment.
