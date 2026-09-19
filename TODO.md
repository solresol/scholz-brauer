# Research roadmap

Updated 2026-09-20 (Sunday, Australia/Sydney).

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

## Next informative increments

1. **Lean:** define checked star-source steps, compose `brauerBlock_replay`
   using `replayFrom_append`, and maintain membership of every earlier
   Mersenne endpoint. Telescope the block counts to `n-1+r` for a source
   with `r` additions ending at `n`, including the singleton source `[1]`.
   Instantiate the result at the rechecked 18-step source for 12509.
   Keep the general star bound separate from any optimality hypothesis.
2. **Hansen (next computational increment):** retrieve the primary definition
   and constructive proof, specify exactly which extra values the lift needs,
   and check a witness for 12509.
   Aim for an independently checked length-12525 Mersenne certificate. The
   currently checked chain is not yet proved to satisfy a Hansen definition.
   Monday's first task is primary-source retrieval and an executable specification
   of the stored-value requirements; bound any construction search explicitly.
3. **Optimality:** obtain auditable primary data/lower-bound certificates for
   ell(12509)=17 and ell*(12509)=18. The present local lower bound is only 14.
   A 12525-step witness is only a numerical upper bound until ell(12509)>=17
   or another sufficient argument is established. The locally proved interval
   for the Scholz right side is [12522,12525].
4. **Later:** recheck Clift's non-Hansen claims from the primary source before
   scheduling larger cases such as 5,784,689. Do not infer a current frontier
   from the initial README or from failure to find a witness.

Bounded exhaustive star-prefix enumeration verifies the lift implementation;
it is not an optimal-chain search. No failed mathematical hypothesis or conjecture
counterexample has been recorded yet. Sunday's integration passed. The rejected
test-design assumption that non-star chosen parent indices imply non-star values
remains explicitly retired: 6=3+3 can also be 5+1 in [1,2,3,5,6].
Tuesday's next formal lemma is the stored-Mersenne invariant in item 1;
do not repeat the already proved single-block lemma.
