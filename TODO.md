# Research roadmap

Updated 2026-09-18 (Friday, Australia/Sydney).

## Verified foundation

- [x] Reconcile the initial README with the README-only checkout.
- [x] Pin Lean/mathlib; inspect and adapt the formal-conjectures addition-chain API.
- [x] Prove summand-pair replay correctness and its exact step count.
- [x] Check the published 12509 witness in Lean and independently in Python.
- [x] Generate and independently check the 12526-step star lift for 12509.
- [x] Check all star prefixes with at most six steps and endpoint at most 32,
  binary lifts for 1..256, and malformed/corrupted certificates.

## Next informative increments

1. **Lean (next daily increment):** formalise the star-step construction using
   `append_sum`; prove the endpoint and exact length of repeated doubling plus
   a stored Mersenne value.
   Prove a general star lift before connecting it to an optimality hypothesis.
2. **Hansen (next computational increment):** retrieve the primary definition
   and constructive proof, specify exactly which extra values the lift needs,
   and check a witness for 12509.
   Aim for an independently checked length-12525 Mersenne certificate. The
   currently checked chain is not yet proved to satisfy a Hansen definition.
3. **Optimality:** obtain auditable primary data/lower-bound certificates for
   ell(12509)=17 and ell*(12509)=18. The present local lower bound is only 14.
4. **Later:** recheck Clift's non-Hansen claims from the primary source before
   scheduling larger cases such as 5,784,689. Do not infer a current frontier
   from the initial README or from failure to find a witness.

Bounded exhaustive star-prefix enumeration verifies the lift implementation;
it is not an optimal-chain search. No failed mathematical hypothesis or conjecture
counterexample has been recorded yet. Sunday integration should rerun the
certificate checks and retain the distinction between witnesses and optima.
