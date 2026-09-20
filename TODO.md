# Research roadmap

Updated 2026-09-21 (Monday, Australia/Sydney).

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

## Next informative increments

1. **Lean:** define checked star-source steps, compose `brauerBlock_replay`
   using `replayFrom_append`, and maintain membership of every earlier
   Mersenne endpoint. Telescope the block counts to `n-1+r` for a source
   with `r` additions ending at `n`, including the singleton source `[1]`.
   Instantiate the result at the rechecked 18-step source for 12509.
   Keep the general star bound separate from any optimality hypothesis.
2. **Optimality (next computational increment):** obtain auditable primary
   data/lower-bound certificates for
   ell(12509)=17 and ell*(12509)=18. The present local lower bound is only 14.
   The checked 12525-step witness is only a numerical upper bound until ell(12509)>=17
   or another sufficient argument is established. The locally proved interval
   for the Scholz right side is [12522,12525]. Start with published exhaustive
   search data and its methodology; bound and checkpoint any attempted local
   exclusion of chains of length <=16. A timeout is not a lower bound.
3. **Hansen formalisation:** after the whole-star proof, formalise underlining,
   stored shifted Mersenne values and telescoping of maximal shifts. Monday's
   report contains a mathematical construction argument; it is not a Lean
   theorem. Retrieve Hansen's original 1959 article when accessible; this
   run used Clift's primary exposition, while the original scan was unavailable.
4. **Later:** independently check Clift's non-Hansen data before
   scheduling larger cases such as 5,784,689. Do not infer a current frontier
   from the initial README or from failure to find a witness. The source page
   is now accessible, but its larger examples have not been imported or checked.

Bounded exhaustive star-prefix enumeration verifies the lift implementation;
it is not an optimal-chain search. No failed mathematical hypothesis or conjecture
counterexample has been recorded yet. Monday's expanded integration passed. The rejected
test-design assumption that non-star chosen parent indices imply non-star values
remains explicitly retired: 6=3+3 can also be 5+1 in [1,2,3,5,6].
Tuesday's next formal lemma is the stored-Mersenne invariant in item 1;
do not repeat the already proved single-block lemma.
