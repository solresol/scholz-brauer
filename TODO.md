# Research roadmap

Updated 2026-09-28 (Monday, Australia/Sydney).

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

- [x] Formalise a decidable Hansen marking checker, source replay and exact
  source length; prove the latest-marked-anchor invariant at every source cut,
  stored-mark maximum and mandatory final mark. Check the 17-step 12509 marking
  in Lean and match it to the saved Python certificate.

- [x] Generate a portable exclusion DAG for 12509 and independently check every
  rule, complete split and context of shared nodes. Compare all 576 small
  decisions against unpruned enumeration and test malformed, omitted-branch,
  shared-context and budget cases. Save reproducible evidence and integrate it.

- [x] Prove in Lean that each marked interval has maximum shift equal to its
  endpoint gap, and telescope the shift caps to n-1. Specialise the count to
  12509: 12508 shifted copies plus 17 source steps gives budget 12525. Match
  marked caps to the saved JSON and check all 5248 accepted small underlinings.

- [x] Integrate the 21–26 September evidence with explicit matching of source,
  exclusions and Mersenne witness; rerun full integration and adversarial report
  checks. Keep computational optimality, formal shift budget and formal Mersenne
  bound separate in the weekly evidence map.

- [x] Export checked index certificates to bounded Lean value fixtures; kernel-check
  singleton and Clift interleaving-29 replays, independently read back all 5248
  small accepted underlinings, and reject corrupted emitted replay in Lean.

## Next informative increments

**Next scheduled work:** Tuesday, prove injectivity of
`(a,k) ↦ 2^k*(2^a-1)` for positive `a`, using unique odd parts. Then prove
summand availability and sorted replay for the general Hansen lift. The bounded
Python-index to Lean-value exporter and the singleton/interleaving-29 fixtures
are complete; their finite replays do not prove general format equivalence.
Do not repeat the completed anchor, shift-count or fixture work.

1. **Optimality formal certificate:** the Wednesday computational exclusion is
   complete: independent C++ and Python traversals exhaust all chains of at most
   16 steps for 12509. Together with the witnesses this establishes ell(12509)=17
   and Scholz at 12509 computationally. Friday's portable certificate and
   independent Python checker are complete. Next formalise the three exclusion
   rules (`bound`, `gap`, `split`), prove checker soundness for arbitrary valid
   prefixes against upstream `IsAdditionChain`, and kernel-check 7 with limit 3.
   Then evaluate the 12509 DAG with measured resource limits; sharing syntax
   does not permit caching truth by node id across different prefixes.
   The saved proof object is not yet a kernel proof. Keep the
   Lean interval [14,17] distinct from the computational optimum 17.
   Excluding star chains of at most 17 steps is optional later work: the star
   optimum 18 remains a literature claim and is unnecessary for this instance.
2. **Hansen lift formalisation:** the underlining certificate, latest-marked
   anchor invariant, shift maximum and telescoping count are complete. Do not
   repeat them. Next define shifted nodes `(a,k)` with value `2^k*(2^a-1)`
   and prove distinctness for positive source exponents (unique odd part).
   Then prove availability of each summand, sorted replay and the resulting
   n-1+r chain length. The proved 12525 allocation budget alone is not an
   addition-chain bound. Reuse
   `mersenne_block_identity` and the source/replay API; simple sequential star
   blocks do not handle interleaved Hansen nodes. Monday's construction argument
   is not a Lean lift theorem. Retrieve Hansen's original 1959 article when
   accessible; the current criterion uses Clift's rechecked primary exposition.
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

The second retired implementation shortcut is caching exclusion truth by shared
node id alone: Friday's adversarial context case refutes it. Neither shortcut
is a failed mathematical conjecture. A 12525 shift allocation is not yet a Lean
chain, and a valid 12526-step star witness alone does not establish the desired
12525 numerical bound; Sunday's composition regressions enforce the latter.
