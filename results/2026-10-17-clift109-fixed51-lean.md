# Fixed-B51 local classification and separated-tail obstruction in Lean

17 October 2026, Saturday, Australia/Sydney (AEDT). Milestone 3 remains active;
milestones 1 and 2 are complete and were not reopened.

## Mathematical result

Write Mv=2^v-1. Fix B51=M51 and terminal B109=M109 in Clift's selected graph.
All earlier intermediate bases are arbitrary positive naturals and all edge
shifts are arbitrary nonnegative naturals. Repeated consumption gives
2*B7<B51: B23>B7 and B51>=2*B23+B5. No seed, carry-free or population-count
hypothesis is needed for the following Lean results.

The complete local domain of (B58,B7), satisfying the production equation at
58, the terminal equation and 2*B7<M51, is exactly:

| B58 | B7 | Parameter range |
| --- | --- | --- |
| M58*2^t | M7*2^l | 0<=t<=51, 0<=l<=43 |
| M51*2^58+M7 | M7 | one pair |
| M7*2^102+M51 | M7*2^l | 0<=l<=43 |

This is 2,333 distinct pairs. `Clift109.fixed51_local_domain` proves both
necessity and sufficiency. Sufficiency constructs the two tail equations;
it does not assert that earlier graph equations can produce these bases.
`fixed51_tail_rigid` derives the necessary domain directly from the actual
selected graph, proving its repeated-use bound.

**The third row is excluded at budget 108 in Lean.** Its production equation
forces a58=0 and b58=102-l; its terminal equation forces a109=0 and b109=51.
Since l<=43, the outgoing cap at vertex 7 is at least 59 and the cap at vertex
51 is at least 51. Thus cap7+cap51>=110 before adding any other nonnegative
caps. `fixed51_separated51_cost` proves this inequality, and
`fixed51_budget_tail` eliminates that form from the graph's necessary domain.
The bound 110 is not asserted to be attained by a full graph allocation.

These results strengthen the 16 October local computation by removing its
carry-free and bit-count assumptions and supplying kernel proofs. The prior
fixed-B58 minimum 109 remains a computational result, not a newly proved Lean
minimum. Combining its stated carry-free scope with today's exclusion leaves
51 changed shifted M58 forms and the separated-7 form for whole-graph work.
Both terminal parents varying is still outside these reductions. No new
Scholz instance, source optimum, Mersenne-chain optimum, arbitrary-labelling
impossibility or novelty is claimed.

## Proof strategy and exact ranges

Reused `fixed51_terminal_domain`, the Mersenne-complement classification,
`factor_of_shifted_odd`, the selected graph and its existing sum equations.
No new checker, certificate format, exporter, solver or dependency was added.

The terminal equation gives B58<2^109. The positive M51 term in its production
then bounds its shift a58<59. The residual after subtracting this term is
B7*2^b58. Two private `decide +kernel` lemmas classify residual odd parts:

- Shifted forms: t in Fin52, a58 in Fin59 (3,068 pairs).
- Separated forms: parameter in Fin58, a58 in Fin59 (3,422 guarded pairs;
  the 59 parameter-zero cases are vacuous).

Each residual either has odd part M7 or has an odd part v with 2*v>=M51.
The latter contradicts 2*B7<M51 because removing powers of two cannot change
the odd part. This handles the unknown B7 and its unbounded shift symbolically;
no arbitrary base or exponent cutoff is assumed. The existing source equation
bounds also force l<44. Explicit algebra supplies witnesses for every listed
pair, so the domain theorem is an iff.

A short exact Python arithmetic probe independently checked the same residual
identities before formalisation (3,068 plus 3,363 nonvacuous pairs, no seed or
floating point). It was a development check, not the proof of completeness;
the final Lean theorem contains and kernel-checks the complete finite claims.

## Development obstacles and validation

An initial relative-path edit command ran from lean/ and failed before changing
any file; the incidental check was of the prior module. A parser error in nested
let expressions and over-eager simplification of residual expressions were
corrected. Explicit `simp only` preserves the residual equalities needed by
the odd-factor lemma. A placeholder in the cost proof needed an explicit goal.

Broad `omega` calls in the cost proof exhausted 200,000 and then 1,000,000
heartbeats; increasing the limit did not fix the problem. The final strategy
uses `Nat.one_le_iff_ne_zero` directly, clears resolved residual cases and uses
`nlinarith only` on the two relevant terminal facts plus positivity. An initial
restricted call lacked positivity of 2^d; supplying it closes the inequality.
The final proof uses the default heartbeat limit. Failed attempts establish
nothing; only the final successful module and integration checks count.

Direct final command, from lean/:

    /usr/bin/time -p lake env lean ScholzBrauer/MersenneComplement.lean

Passed in 7.39 seconds. Earlier successful incremental checks of the residual
lemmas, local necessity, and full local iff/graph theorem took 6.59, 7.70 and
11.78 seconds respectively. These were development stages, not repeated
independent claims.

Required integration command (one run):

    python3 scripts/verify_integration.py --output results/2026-10-17-integration-checks.json

Passed once in **191.902104s**, Python 3.9.6: all 25 commands returned zero.
Pinned Lean 4.27.0 built all 974 jobs in **19.105721s**. The **196-theorem**
axiom audit passed in **7.267471s**, using only propext, Quot.sound and
Classical.choice. Five vendor hashes and all 99 research-input hashes match,
including a separate final readback. The compiled proof-token scan is clean.
Five public theorems were added to Audit.lean; their private residual
dependencies are audited transitively. Toolchain and dependencies are unchanged.
The existing computation suite ran for required integration only; no repeated
experiment is counted as a research result. Complete proof, records and
structured integration output were reviewed before committing.

## Sources and next obligation

Clift's primary [account](https://www.additionchains.com/ScholzBrauer.html) and
[selected diagram](https://www.additionchains.com/LargeNonHansen.png) were
re-fetched on 17 October. Their hashes match the checked 8/16 October versions;
URLs, access timestamp and hashes are in
`data/2026-10-17-clift109-source-recheck.json`. The selected graph uses 8=4+4;
the alternate 8=7+1 makes the same value sequence star/Hansen. This distinction
is unchanged. No literature claim about unrestricted impossibility is assumed.
The vendored formal-conjectures addition-chain definitions, uncompiled Scholz
statement and Apache-2.0 licence were inspected. The open upstream target is
not imported or assumed.

Next: determine whole-graph compatibility and minimum caps for the remaining
changed shifted M58 forms and separated-7 form. Reuse the current enumerator
and repeated-consumer domains or prove tail-cost comparisons first. In the
shifted-block family, the existing two-block theorem supplies both orientations;
for t>0 the terminal shifts are a109=51-t, b109=0. This suggests comparing
costs with completed fixed-B58 cases, but no such general cost reduction is
proved in this run. Do not repeat the completed fixed-B58 or early-base searches,
raise unrestricted solver timeouts, or move to larger source graphs without a
concrete blocker requiring it.
