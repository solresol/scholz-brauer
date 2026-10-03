# Research roadmap

Updated 2026-10-04 (Sunday, Australia/Sydney).

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

- [x] Prove positive shifted-Mersenne injectivity and duplicate-free value
  conversion in Lean; prove positivity and local doubling/base-sum identities.
  Audit all seven new theorems; keep allocation and sorted replay separate.

- [x] Expose bounded labelled Hansen allocations and their summand dependencies.
  Independently check complete families, closure, count, endpoint and sorted
  replay for 29 and both 12509 sources; compare all 5248 small underlinings,
  reject corrupted objects and save reproducible 29/12509 allocations.

## Milestone 1 — general Hansen lift: COMPLETE

- [x] Define the finite allocated label family and prove base/shift membership.
- [x] Prove positive exponents, no duplicate labels or values, and exact size.
- [x] Prove availability of both summands for every non-seed node, including
  retained anchors across unmarked values.
- [x] Prove the endpoint envelope and both endpoint memberships.
- [x] Prove sorted chain validity, successful replay and exactly `n-1+r` additions.
- [x] Apply the general theorem to the 17-step source for 12509, proving
  `ell(2^12509-1) ≤ 12525` in Lean. Audit all dependencies.

`HansenAllocation.lean` and `HansenLift.lean` complete the proof obligations.
The replay theorem exhibits a summand-value certificate for the explicit sorted
chain; it does not claim equality with the saved Python index certificate.
No further exporters, allocation checkers or small Hansen enumeration are needed.

## Milestone 2 — end-to-end Lean Scholz at 12509: ACTIVE

- [x] Formalise the portable exclusion rules (`bound`, `gap`, `split`) and prove
  soundness for arbitrary valid prefixes against upstream `IsAdditionChain`.
  Prove the extension doubling bound, complete reachability representation and
  transport from accepted exclusion to the infimum defining `ell`.
- [x] Kernel-check target 7 with limit 3 and conclude `ell(7)=4` using a witness.
- [ ] Kernel-check the 12509 lower bound with measured resource limits, obtaining
  `ell(12509)=17`; combine with `mersenne12509_length_le_12525`.

`Exclusion.lean` covers the first two obligations. Its split rule checks all
necessary next values and all supplied children; extra edges add obligations.
Recursion decreases the step budget, and all shared nodes are checked in context.
The 16-addition JSON remains the source for the outstanding exclusion.

- [x] Kernel-check exclusion through 15 additions, strengthening the formal
  interval to `[16,17]`. The smaller certificate has 475 nodes and 7544 contextual
  occurrences; 403 proof fragments compose via `checkExclusionWith_split`.

Balanced tree lookup, direct data reification, Boolean list checks and sequential
context-specific proof composition remove the observed data/stack/memory blockers
for this smaller case. Monolithic checks still fail at the 2 GB limit. Explicit
primitive recursion did not solve that failure and was not retained.

- [x] Prove reachability under context enlargement and soundness of local checks
  on shared supersets, including child inclusion, endpoint, budget and coverage.
- [x] Complete exact context-union compression of the full saved DAG. Refute the
  naive unchanged-edge union hypothesis: two groups need seven additional edges,
  discharged by six additional gap contexts.
- [x] Kernel-check the first 2,496 contexts and prove exclusion for every
  gap-labelled context in the checked prefix, without assuming the remainder.

The full certificate now has 29,865 abstract contexts, but **full acceptance
remains unproved**. A single-module build timed out at 1500 seconds. A checkpointed
build with at most three workers timed out at 1800 seconds, retaining only
`Exclusion12509Part00.lean` (78 local checks, compiled in 1184 seconds under load).
No source optimum 17 or numerical Scholz theorem is imported into the library.
The exporter can regenerate the remaining candidate parts; generation is not proof.

**Reassessment.** Context union removes duplicated prefix occurrences, but the
current list-based local evaluator still fails the full-run budget. Do not repeat
these full builds unchanged. Preserve the compiled checkpoint and first profile
compact set-based child inclusion/coverage on expensive split contexts, with a
small kernel budget, before implementing another representation. Check kernel
support for the required exact operations and retain an explicit soundness bridge.
Unused-lookup specialisation and direct Boolean sublist checking did not show a
material improvement in the recorded probes. Control host memory contention;
measure expensive contexts rather than extrapolating from a few easy samples.
See `results/2026-10-04-context-sharing-lean.md`.

The two exhaustive searches and portable DAG already establish optimality
computationally. Lean source bounds are `[16,17]`. The Mersenne upper bound
12525 is now a Lean theorem. Sharing certificate syntax does not permit caching
truth by node id across different prefixes. Excluding 17-step star chains is
unnecessary for this milestone; star optimum 18 remains a literature claim.

## Milestone 3 — a specific extension beyond Hansen: DEFERRED

Start with a small documented non-Hansen chain and state an explicit stronger
hypothesis that a bounded exact experiment can refute. Check the source data,
record exact bounds and structural obstructions or failed hypotheses. Move to
larger documented cases only after that experiment and infrastructure are sound.
Clift's documented small non-Hansen source `[1,2,4,8,9,13,16,29]` was re-read
on 4 October and is the next source to validate after milestone 2. No extension
experiment was run today. Clift's 5784689 data and optimality claims have not
been independently checked;
no frontier or novelty claim follows from this repository's results.

## Retained constraints and failed shortcuts

- Sequential whole-anchor blocks fail when shifted values interleave with
  later source bases. The completed lift allocates first, then sorts by value.
- Non-star chosen parent indices do not imply non-star values: in
  `[1,2,3,5,6]`, both `6=3+3` and `6=5+1` are possible.
- Exclusion truth cannot be cached by DAG node alone across different prefixes.
  The new theorem permits reuse only on explicitly checked supersets. Naive union
  with unchanged edges fails: `5120 + 6144 = 11264` is one missing cross-context sum.
- A proved scratch residue envelope pruned none of the 1,345,873 occurrences for
  moduli `2,4,...,16384`; that unsuccessful approach was not added to the library.
- Finite construction tests are not optimality searches. A witness bound and
  source optimality are separate obligations. Neither unsuccessful search nor
  timeout proves exclusion.
- No mathematical extension hypothesis has yet been tested or refuted.

## Publication follow-up — 3 October 2026

- [x] Package v0.1.0 with licence, source/AI attribution, citation metadata,
  Zenodo metadata, release notes and CI using the existing verification command.
- [ ] Connect the public GitHub repository in the author's Zenodo account,
  publish the archive, verify its DOI and add it to the citation metadata.
- [ ] If proceeding with Palomar, prepare the independent statement and
  Comparator/metadata interface and resolve module-header compatibility;
  rebuild and compare before submitting an immutable commit. Not yet submitted.
- [ ] Develop a preprint with a collaborator contributing mathematical or
  formalisation work. A software release is not journal peer review.

Publication work does not close milestone 2 or establish novelty priority.
