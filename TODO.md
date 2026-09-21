# Research roadmap

Updated 2026-09-22 (Tuesday, Australia/Sydney).

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

## Next informative increments

1. **Optimality (Wednesday computational increment):** obtain auditable primary
   data/lower-bound certificates for
   ell(12509)=17 and ell*(12509)=18. The present local lower bound is only 14.
   The checked 12525-step witness is only a numerical upper bound until ell(12509)>=17
   or another sufficient argument is established. The locally proved interval
   for the Scholz right side is [12522,12525]. Start with published exhaustive
   search data and its methodology; bound and checkpoint any attempted local
   exclusion of chains of length <=16. A timeout is not a lower bound.
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
counterexample has been recorded yet. Tuesday's expanded integration passed. The rejected
test-design assumption that non-star chosen parent indices imply non-star values
remains explicitly retired: 6=3+3 can also be 5+1 in [1,2,3,5,6].
The whole-star invariant is proved; do not repeat it. The bridge between Lean's
summand-value certificates and Python's summand-index format remains unproved.
