# 2026-09-26 — Hansen shift maxima and telescoping in Lean

Saturday, Australia/Sydney. This increment formalises the shift accounting
needed by the stored-node Hansen lift. It does not yet construct that lift.

## Proved increment

`lean/ScholzBrauer/HansenShift.lean` defines the shift requests to an anchor
through the next marked step, their executable maximum, the next mark and a
list of proposed caps indexed by marked values. The final anchor has cap zero;
unmarked source values need only their unshifted base node in the construction.

Eight general theorems prove:

- every entry of a valid source prefix is at most the next marked value;
- for an accepted continuation, the maximum request is exactly the gap between
  the current anchor and the next mark;
- each individual request is bounded by that maximum;
- the first proposed cap equals the maximum, and caps align in length with marks;
- the sum of caps plus the initial anchor equals the final anchor;
- starting from 1, this sum is `n-1`, giving budget `n-1+r` with `r` source steps.

The maximum theorem assumes the upstream `IsAdditionChain` predicate for the
source prefix and the proved Hansen checker for its continuation. It does not
assume a lift, source optimality or the target conjecture. The proof follows
accepted source extensions: an intervening unmarked consumer is smaller than
the next mark, so its requested shift cannot exceed the marked step's request.
The count then telescopes over the actual marked gaps.

Three named 12509 specialisations check the cap list

```text
1, 4, 6, 12, 24, 48, 96, 192, 384, 13, 781, 1562, 3124, 6248, 13, 0
```

and instantiate the general count theorem: **12508** shifts and an allocation
budget of **12525** after the 17 source steps. The cap list corresponds to
`hansen12509_marks`; source values 4 and 13 are unmarked. The count identity is
not yet an existence theorem for 12525 additions in Lean.

Eight kernel-evaluated examples cover the singleton source, retention of anchor
12 through the consumer 13 before 24, the marked-cap plan for Clift's 29 source,
and an invalid decreasing example whose maximum exceeds the proposed gap.
That rejected example illustrates the need for acceptance hypotheses; it is
not a counterexample to a claim about valid addition chains.

## Sources and dependency boundary

Reopened [Clift's exposition](https://www.additionchains.com/ScholzBrauer.html)
and [OEIS A349044](https://oeis.org/A349044) on 26 September 2026. The two
17-step witnesses and the OEIS 18-step star witness match the fixtures.
Clift's latest-mark labelling and maximum outgoing shift describe the
construction used here. Direct HTML retrieval again has SHA-256
`d8a9482f19403d42110b52462f88aee41bf291e2a908a203fb9efb8320bd9eef`.
Both pages are live, without immutable revision; access metadata is in
`data/2026-09-26-hansen-shift-sources.json`. The original Hansen article was
not inspected. No larger chain data, novelty or current-frontier claim is used.

Inspected and reused the adapted formal-conjectures definitions, retained
Scholz statement and Apache-2.0 attribution. The upstream open statement is
uncompiled and supplies no hypothesis. Pins are unchanged: Lean **4.27.0**,
mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`, formal-conjectures snapshot
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`, and locked transitive dependencies.

## Verification

```sh
python3 scripts/verify_integration.py --output results/2026-09-26-integration-checks.json
```

Completed in **47.006420 seconds**, starting **08:09:01 AEST**. Use a new output
filename to repeat; the runner refuses to overwrite records. Its input hashes,
exact commands and outputs include:

- `lake build`: all **752 jobs**, **4.502474 s** in the integrated run;
- `lake env lean Audit.lean`: **54 named theorems**, **7.244577 s**, only
  `propext`, `Quot.sound` and `Classical.choice` dependencies;
- all five vendored source hashes and the running pinned Lean version;
- the existing star/Hansen certificate replays, both exhaustive 12509 exclusions,
  portable exclusion certificate, bounded search oracle and negative checks.

The Hansen verifier now independently recomputes shifts by marked intervals,
compares the full source-index allocation (including zeroes) with the generator,
and verifies the stored complement for each consumer. This passes for all
**5248** accepted underlinings among **30582** masks on **1051** source chains
(at most six additions, endpoint at most 32), plus both published 12509 witnesses.
It also parses the explicit Lean fixture literals and checks the source, marks
and caps against the saved JSON certificate. This is a finite fixture match,
not a general proof of Python/Lean format equivalence. The combined Hansen
check takes **1.506840 s** and its results are embedded in the integration JSON.

Python **3.9.6**, Apple clang **21.0.0**, exact integer arithmetic, no seed.
The compiled local Lean sources contain no `sorry`, `admit`, custom axiom,
`unsafe` or `native_decide`. All recorded input hashes still match after the
checks. Development corrected a duplicated working-directory path, Boolean
simplification in one rewrite, and comma normalisation in a source-page check;
none changes the mathematical claim. Full source/document diffs and structured
verification records were inspected before committing.

## Conclusion and next

The Hansen shift maximum and telescoping budget are now kernel checked,
including the budget 12525 at 12509. The actual Lean Mersenne upper bound
remains **12526**, and the Lean source-length interval remains **[14,17]**.
The independently checked computational optimum 17 and 12525-step Hansen
witness still establish the numerical Scholz instance computationally.
No Mersenne optimum, universal conjecture proof or new numerical bound is claimed.

Next define shifted nodes with value `2^k*(2^a-1)` and prove distinctness for
positive exponents via their odd parts. Then prove summand availability and
sorted replay, turning today's budget into an actual chain-length theorem.
The exclusion checker soundness proof remains a separate task: start with 7/3
before attempting kernel evaluation of the 12509 DAG. Larger non-Hansen cases
remain deferred.
