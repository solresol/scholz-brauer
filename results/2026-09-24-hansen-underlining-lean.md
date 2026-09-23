# 2026-09-24 — Hansen underlining in Lean

Thursday, Australia/Sydney. This increment formalises the source marking
criterion needed by the Hansen lift. It does not yet formalise that lift.

## Proved increment

`lean/ScholzBrauer/Hansen.lean` adds decidable `IsHansenFrom source anchor steps`.
Each certificate entry supplies a value and a Boolean marking flag. Starting
from `[1]` and anchor `1`, the checker requires both summands to be stored,
one to be the current anchor, and the new value to exceed every previous value.
Marking updates the anchor; an unmarked entry retains it. The base case requires
the source endpoint to equal the anchor.

Ten general theorems prove:

- exact source and replay-certificate lengths;
- successful ordinary source replay, hence source validity under the adapted
  formal-conjectures `IsAdditionChain` predicate;
- equality between the carried anchor and the latest actual marked value;
- equality between the completed source endpoint and its final anchor;
- retention of every marked value and its bound by the final anchor;
- valid continuation and anchor availability at every cut in the certificate;
- use of the latest actual mark as a summand at every next step;
- that a nonempty accepted certificate's final flag must be true.

The replay certificate uses `(anchor, value-anchor)`. Its proof derives the
subtraction identity from the checked sum; it does not accept a truncated
subtraction as evidence. These proofs do not assume source optimality or Scholz.

Five named theorems in `Example12509.lean` check the 17-step marking, source
list, replay, marked-value list and source-certificate length. Its unmarked
values are 4 and 13. In particular the step to 24 uses anchor 12, even though
13 is the preceding source value. The marking and oriented parent indices
match the saved Python Hansen certificate exactly. This finite fixture match
is not a general Python/Lean format-equivalence theorem.

## Source and dependency checks

Reopened [Clift's primary exposition](https://www.additionchains.com/ScholzBrauer.html)
and [OEIS A349044](https://oeis.org/A349044) on 24 September 2026. The underlining
criterion and both published 17-step source lists match the local fixtures.
Clift's HTML SHA-256 is unchanged:
`d8a9482f19403d42110b52462f88aee41bf291e2a908a203fb9efb8320bd9eef`.
These are live pages with no immutable revision; retrieval metadata is in
`data/2026-09-24-hansen-sources.json`. The original Hansen article was not
inspected; this formalisation follows the rechecked Clift criterion.
No larger non-Hansen dataset or current-frontier/novelty claim is used.

Inspected the vendored upstream addition-chain definitions, Scholz statement,
provenance and Apache-2.0 licence. Reused the local adaptation and replay API.
The upstream open theorem remains an uncompiled reference and supplies no
assumption. Pins are unchanged: Lean **4.27.0**, mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`, formal-conjectures snapshot
`40e7c98697de6f66b8cbdbf641749ab39ed9c152` and locked transitive dependencies.

## Verification

Final source build completed all **751 jobs**. The reproducible combined run:

```sh
python3 scripts/verify_integration.py --output results/2026-09-24-integration-checks.json
```

passed in **29.925100 seconds**, starting at **08:08:38 AEST**. Choose a fresh
output filename when repeating. It includes `lake build` (**4.497340 s**),
`lake env lean Audit.lean` (**7.114341 s**), the pinned version check and all
five vendored source hashes. All **43 named theorems** pass the axiom audit;
only the standard allowed Lean axioms occur. Compiled local sources have no
`sorry`, custom axiom, `admit` or `native_decide`.

Nine new kernel-evaluated examples cover `[1]`, ordinary marked steps,
unmarked endpoints, unavailable summands, repeated/decreasing entries,
a stale anchor, incorrectly marking 13 before 24, and the known Hansen
source `[1,2,4,8,9,12,17,29]`.

The existing deterministic exact-integer integration checks also pass:
842 star prefixes and 1,051 Hansen sources (at most six additions, endpoint
at most 32), binary exponents 1..256, 30,582 marking masks, all 5,248 accepted
lifts, both stored large certificates, 576 small search decisions (targets
1..64, limits 0..8), and checkpoint/negative cases. Both exhaustive traversals
again exclude every <=16-step chain for 12509. These are regressions;
today's new result is the formal underlining API, not a new numerical bound.
Python **3.11.6**, Apple clang **21.0.0**, no random seed; exact commands,
outputs, runtimes and final source hashes are in the integration JSON.

`results/2026-09-24-marking-fixture-check.json` records an additional
**0.003964 s** exact fixture check: parse the explicit Lean `(value, flag)`
literals; compare `[1]` plus values and marked indices with the source JSON
and saved certificate; reconstruct each parent as the latest earlier mark
and the stored complement, then compare all 17 oriented parent pairs.
The saved Mersenne certificate hash remains
`3662884e8f514fb682c6407ebe3593d724471183c9d21d09aa11e37342fe0c11`.

Development caught Lean keyword/normalisation/elaboration errors and one
incorrect working-directory path; these were corrected without changing the
mathematical claims. A source-retrieval check initially inserted spaces
inside HTML inline tags and failed string matching; removing tags and
normalising comma whitespace recovered the exact source list. No failed
mathematical hypothesis or counterexample arose.

## Conclusion and next step

Hansen underlining, its source replay and latest-marked-anchor invariant are
now kernel checked, including the concrete 12509 certificate. The Lean source
bounds remain `[14,17]` and its Mersenne upper bound remains **12526**.
The separately rechecked computational evidence establishes `ell(12509)=17`
and `ell(2^12509-1)<=12525`, hence Scholz at 12509. Neither the exclusion nor
the Hansen Mersenne lift is yet a Lean proof. No optimum for the Mersenne target
or universal conjecture result is asserted.

Next formal lemma: for successive marked values a<h, prove that the maximum
shift assigned to a is h-a, then telescope these maxima to n-1. Next
computational/formal bridge: design bounded Lean-checkable exclusion evidence.
Keep larger non-Hansen searches deferred until the lift infrastructure is ready.
