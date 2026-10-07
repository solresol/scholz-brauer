# Research roadmap

Updated 2026-10-08 (Thursday, Australia/Sydney).

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

## Milestone 2 — end-to-end Lean Scholz at 12509: COMPLETE

- [x] Formalise the portable exclusion rules (`bound`, `gap`, `split`) and prove
  soundness for arbitrary valid prefixes against upstream `IsAdditionChain`.
  Prove the extension doubling bound, complete reachability representation and
  transport from accepted exclusion to the infimum defining `ell`.
- [x] Kernel-check target 7 with limit 3 and conclude `ell(7)=4` using a witness.
- [x] Kernel-check the 12509 lower bound with measured resource limits, obtaining
  `ell(12509)=17`; combine with `mersenne12509_length_le_12525`.

`Exclusion.lean` covers the first two obligations. Its split rule checks all
necessary next values and all supplied children; extra edges add obligations.
Recursion decreases the step budget, and all shared nodes are checked in context.
The 16-addition JSON is the source for the now-completed exclusion.

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

- [x] Prove exact list/bit-set membership and sound bit-set context checking,
  including independently checked parent and child encodings.
- [x] Kernel-check all 29,865 contexts, excluding every chain through 16 additions.
- [x] Prove `length12509_eq_seventeen` and combine with the general Hansen bound
  in `scholz12509`. Audit the entire transitive proof dependency set.

The 4 October list-based attempts timed out at 1500/1800 seconds. The 5 October
bit-set representation removes repeated list inclusion and edge-membership work;
its full accepted certificate closes this milestone. The original checked prefix
is retained. See `results/2026-10-05-scholz12509-lean.md` for resource evidence.

Do not repeat the 12509 search, add another exclusion format, or rebuild the
completed checkpoint without a concrete reason. The formal source optimum is 17;
the formal Mersenne upper bound is 12525. A minimum Mersenne length is not proved.
Star optimum 18 remains a literature claim and is unnecessary for this result.

## Milestone 3 — extension beyond Hansen: SPECIFIC FAMILY PROVED

- [x] Recheck and validate Clift's `[1,2,4,8,9,13,16,29]`, including unique
  parent pairs and exclusion of every Hansen marking (also kernel checked).
- [x] Refute the standard all-Mersenne orientation hypothesis for this graph:
  eight possibilities have minimum 32 doublings, exceeding the budget 28.
- [x] Test the stronger one-base repair hypothesis. With Mersenne bases at
  source values 1,2,4,8,16, enumerate every nonnegative label assignment with
  at most 28 doublings. Forward/reverse exact enumeration agrees on one
  solution: base9=8161, base13=8191, labels (5,0,0,1,13,0).
- [x] Independently replay its 35 additions and kernel-check the bound,
  non-Hansen status, restricted orientation minimum and local repair identity.

- [x] Prove the parametric one-gap family for `n=3*2^a+2^b+1`, `1 ≤ b < a`:
  valid source of `a+4` additions, available summands, strict replay order,
  endpoint and exactly `n-1+(a+4)` lifted additions.
- [x] Prove the general repaired-block theorem for a prefix ending at `2^A-1`
  containing `2*(2^B-1)`, with `B≥1` and `B+2≤A`; connect it to the existing
  Hansen allocation under the explicit hypothesis `(B,1) ∈ hansenLabels 1 steps`.
- [x] Prove exclusion of every source marking for `a≥3`; refute the unrestricted
  non-Hansen claim at `(a,b)=(2,1)` by a kernel-checked marking using `8=7+1`.
- [x] Check all 36 parameter pairs `2≤a≤9`, `1≤b<a`: direct replay equals
  separately sorted allocation, no collisions/carries, exact count, all 57,376
  endpoint-fixed markings, independent index replay.
- [x] Kernel-check source-29 exclusion through six additions, prove `ell(29)=7`
  and combine it with the new family theorem to prove the Scholz instance at 29.

`OneGapLift.lean` closes the whole-family construction and classification
obligations proposed on 6 October. Explicit insertion inside a doubling run
establishes strict order and distinctness directly; no new allocation framework
or general odd-part injectivity theorem was needed. The original 29 labelling
uniqueness remains a restricted computational assertion, not a Lean completeness
result. Neither all family sources nor their Mersenne lifts are proved optimal.
The Scholz corollary for other members retains an explicit source-optimality
hypothesis. No novelty claim is made.

- [x] Reconstruct Clift's reduced 109 diagram from the primary PNG and check
  every selected sum and alternative parent. Distinguish its selected `8=4+4`
  graph from the star/Hansen value sequence with `8=7+1`.
- [x] Kernel-check the selected-prefix marking obstruction and minimum 110
  doublings among all 256 standard Mersenne orientations.
- [x] Refute the hypothesis that arbitrary bases at 5 and 7 alone recover the
  108-doubling budget: all 1,624 candidate pairs, 63 viable pairs and 2,304
  labellings have minimum 110. Independent forward/backward and local-pair
  enumerations agree; all eight minimum allocations independently replay.
- [x] Prove in Lean that the repeated uses at 15, 28 and 58 force B5 and B7 to
  be shifted M5 and M7. Prove the prior one-gap base 121 cannot feed M28
  alongside unchanged M23 for any nonnegative shifts.

The complete two-exception minimum is an exact computational result; the
structural rigidity, standard-orientation minimum and specific reuse obstruction
are Lean theorems. The graph's full arbitrary-labelling impossibility remains
Clift's literature claim, not an assumed or locally completed theorem. Two
bounded unrestricted Z3 probes timed out (30s/60s); those are not exclusions.
See `results/2026-10-08-clift109-obstruction.md`.

**Next substantive question.** Extend the complement/interval restrictions to
additional changing bases or cover all critical-path cases of this same graph.
A successful budget-108 labelling, if one existed, would have to change a base
outside vertices 5 and 7. Reassess the structural representation before another
unrestricted solver attempt; do not merely increase its timeout. Do not repeat
the completed two-base enumeration or add a certificate format. Larger
5,784,689 data and optimality claims remain deferred.

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
- For the source ending at 29, retaining standard Mersenne bases/orientations
  cannot meet the 28-doubling budget. One exceptional base at 9 repairs it;
  uniqueness is only within the explicitly searched fixed-spine family.
- A non-Hansen selected parent graph need not give a non-Hansen value sequence:
  Clift's 109 diagram selects `8=4+4`, while `8=7+1` makes its sequence star.
- The local one-gap repair can fail at a later reuse: base 121 at vertex 5
  cannot combine with shifted M23 to form M28. Keeping both detour bases free
  still requires at least 110 doublings in the checked 109 family.
- The proposed parametric sources are not all non-Hansen: `(2,1)` has the
  alternative `8=7+1`. The classification theorem requires `a≥3`.

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

Publication work is separate from the completed mathematical milestones and
does not establish novelty priority.
