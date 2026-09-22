# Research roadmap

Updated 2026-09-23 (Wednesday, Australia/Sydney).

## Verified foundation

- [x] Reconcile the initial README with the README-only checkout.
- [x] Pin Lean/mathlib; inspect and adapt the formal-conjectures addition-chain API.
- [x] Prove summand-pair replay correctness and its exact step count.
- [x] Check the published 12509 witness in Lean and independently in Python.
- [x] Generate and independently check the 12526-step star lift for 12509.
- [x] Check all star prefixes with at most six steps and endpoint at most 32,
  binary lifts for 1..256, and malformed/corrupted certificates.
- [x] Prove doubling certificates and a Brauer block in Lean: replay success,
  endpoint, exact added length, and preservation of stored values.
- [x] Integrate small Python checks, Lean build and axiom audit in one command;
  retain input hashes and correct the stale regression-report date.
- [x] Reconcile the week's witnesses, formal proofs and remaining optimality gap.
- [x] Retrieve Clift's primary account of Hansen underlining and edge labelling.
- [x] Implement a complete underlining detector and exact stored-shift lift;
  independently replay a saved 12525-step certificate for 12509.
- [x] Compare against all marking masks for 1,051 small source chains; check
  all 5,248 accepted lifts and both published 17-step 12509 sources.
- [x] Prove complete star-source replay, stored Mersenne membership and exact
  `n-1+r` count in Lean, including `[1]`; instantiate the 18-step 12509 source.
- [x] Prove the conditional Scholz corollary for an optimal checked star source;
  audit all new theorems and distinguish the formal 12526 bound from Python's 12525.

- [x] Exclude all <=16-step chains for 12509 with two independent exact traversals;
  cross-check 576 small decisions against unpruned enumeration and test restart
  frontier coverage. Combine with the saved lift to establish Scholz at 12509
  computationally, without treating the search as a Lean proof.

## Next informative increments

1. **Optimality formal certificate:** the Wednesday computational exclusion is
   complete: independent C++ and Python traversals exhaust all chains of at most
   16 steps for 12509. Together with the witnesses this establishes ell(12509)=17
   and Scholz at 12509 computationally. Next design a Lean-checkable exclusion
   certificate or prove completeness of a small exact enumerator; the current
   search transcript is reproducible evidence, not a kernel proof. Keep the
   Lean interval [14,17] distinct from the computational optimum 17.
   Excluding star chains of at most 17 steps is optional later work: the star
   optimum 18 remains a literature claim and is unnecessary for this instance.
2. **Hansen formalisation (Thursday):** define a decidable underlining certificate
   over source values, check the 17-step 12509 marking, and prove the
   latest-underlined-anchor invariant. Then formalise stored shifted Mersenne
   values and telescoping of maximal shifts. Reuse `mersenne_block_identity`
   and the addition-chain/replay API; the simple sequential star blocks alone
   do not handle interleaved Hansen nodes. Monday's
   report contains a mathematical construction argument; it is not a Lean
   theorem. Retrieve Hansen's original 1959 article when accessible; this
   Monday run used Clift's primary exposition, while the original scan was unavailable.
3. **Later:** independently check Clift's non-Hansen data before
   scheduling larger cases such as 5,784,689. Do not infer a current frontier
   from the initial README or from failure to find a witness. The source page
   is now accessible, but its larger examples have not been imported or checked.

Bounded exhaustive star-prefix enumeration verifies the lift implementation;
it is not an optimal-chain search. No failed mathematical hypothesis or conjecture
counterexample has been recorded yet. Wednesday's expanded integration includes
both exclusion searches. The rejected
test-design assumption that non-star chosen parent indices imply non-star values
remains explicitly retired: 6=3+3 can also be 5+1 in [1,2,3,5,6].
The whole-star invariant is proved; do not repeat it. The bridge between Lean's
summand-value certificates and Python's summand-index format remains unproved.
