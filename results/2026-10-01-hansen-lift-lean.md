# 2026-10-01 — Thursday — general Hansen lift completed in Lean

Australia/Sydney. **Milestone 1 is complete.** For every accepted marked source
with `r` additions ending at `n`, Lean now proves allocation and summand closure,
a sorted addition chain ending at `2^n-1`, a successful summand-value replay
with exactly `n-1+r` additions, and the resulting minimum-length upper bound.
Applying the theorem to the checked 17-step source for 12509 proves
`additionChainLength (2^12509-1) ≤ 12525` in Lean.

This closes the missing general proof obligations; it is not another finite
construction experiment. Source optimality remains separate: Lean still gives
`14 ≤ additionChainLength 12509 ≤ 17`, so the end-to-end Scholz instance has
not yet been kernel checked. The computational optimum remains 17. No minimum
Mersenne-chain length, general Scholz theorem or novelty claim is made.

## Representation and proof

`HansenAllocation.lean` uses the label interface established on 30 September.
A label `(a,k)` represents `2^k*(2^a-1)`. Its executable list `hansenLabels a steps`
is grouped by marked intervals:

- Empty continuation: the terminal base `(a,0)`.
- Unmarked step `v`: its base `(v,0)`, followed by the same anchor's continuation.
- Marked step `v`: all `(a,k)` for `0 ≤ k ≤ v-a`, then the continuation at `v`.

This is an allocation order, not numerical order. It handles the previously
identified interleaving without attempting sequential whole-anchor replays.
The list contains each base once; marked anchors receive exactly their full
shift interval and unmarked entries receive no positive shifts.

The proofs establish downward shift closure, positive exponents, duplicate-free
labels, and exact list length `steps.length + sum(hansenShiftCaps a steps) + 1`.
The existing positive-label injectivity then gives duplicate-free values.
The existing telescoping theorem turns the count into `n+r` nodes from `[1]`.
Every label also satisfies `a+k ≤ n`, which bounds its value by `2^n-1`.

The central dependency proof is `hansenLabels_base_sums`. Its induction carries
an ambient allocation containing all prefix bases and the remaining labels.
For `v=a+b`, prior source membership supplies `(b,0)` and the existing proved
shift-demand maximum supplies `(a,b)`, even across unmarked steps. The local
Mersenne identity gives their exact sum. `hansenLabels_closed` combines this
with predecessor-shift membership and the doubling identity, covering every
non-seed allocated node.

`HansenLift.lean` maps the labels to numerical values and merge-sorts them.
Membership and length are preserved by the sort permutation. Positivity and
seed membership establish head 1; duplicate-free sorted values establish strict
increase; dependency closure supplies every required sum. The envelope and
final-base membership establish the endpoint. Thus `hansenLift_chain` proves
exactly the upstream `IsAdditionChain` predicate and the required count.

`additionChain_exists_replay` proves that any such chain has a successful replay
in its given order: remove the last node, use positivity to put both summands
in the prefix, replay that prefix, then append the final sum. Therefore
`hansenLift_certificate` proves successful replay of the sorted allocation with
exactly `n-1+r` pairs. This is an existential certificate theorem for an explicit
sorted chain; no new file of 12525 pairs is generated and no equality with the
Python index certificate is asserted.

`hansenLift_upper_bound` applies the existing minimum-length API.
`scholz_of_optimal_hansen` states the conditional result when this particular
accepted source has minimum length; that optimality hypothesis is explicit.
`Example12509.lean` supplies the already kernel-checked marking and 17-step
source, yielding `hansenLift12509_chain`, `hansenLift12509_certificate` and
`mersenne12509_length_le_12525`. No large-value reduction is needed.

## Verification and sources

Started from clean `main` at `94963511e9d2eadc92383215c3e62bfc6f8142c1`, correct
`git@github.com:solresol/scholz-brauer.git` origin and no competing process.
Acquired the exclusive research lock. Fetch and fast-forward-only merge were
already current. No on-disk AGENTS.md applied; followed the supplied instructions.

Reinspected the pinned Apache-2.0 formal-conjectures definition, minimum-length
API, open Scholz statement and licence. The open statement remains an uncompiled
reference and is never imported. Dependencies remain Lean **4.27.0**, mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`, and upstream reference revision
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`.

Rechecked [OEIS A349044](https://oeis.org/A349044) for the exact 17-step source
and [Clift's exposition](https://www.additionchains.com/ScholzBrauer.html) for
the latest-underlined-anchor criterion and marked endpoint on **1 October 2026**.
These are live pages without a recorded immutable version. Published optimality
assertions are not hypotheses of any new proof. Source metadata is in
`data/2026-10-01-hansen-lift-sources.json`. Hansen's original article was not read;
no claim about a current literature frontier is made.

Commands (Lake commands run from `lean/`):

```sh
lake env lean ScholzBrauer/HansenAllocation.lean
lake build ScholzBrauer.HansenAllocation
lake env lean ScholzBrauer/HansenLift.lean
lake build
```

After resolving elaboration issues, the full build passed **756 jobs**. Boundary
applications include the singleton source and the interleaved 29 source.
A singleton `decide` check initially stuck on reduction through `mergeSort`;
using its proved simplification rules resolved this. This was a reduction issue,
not a failed mathematical claim. No placeholders remain in compiled proofs.

Then, from the repository root, ran the existing integration exactly once:

```sh
python3 scripts/verify_integration.py --output results/2026-10-01-integration-checks.json
```

It started **08:11:24 AEST** and passed in **43.178642 s**, using Python **3.11.6**,
exact integers and no randomness. All subprocesses exited zero; **55 input
hashes** and **five vendor hashes** matched. Its Lean build passed 756 jobs in
**1.325261 s** and its **94-theorem** audit passed in **7.714423 s**. All new
allocation, lift and 12509 theorems are audited. Only `propext`, `Quot.sound`
and `Classical.choice` occur; no `sorryAx`, custom axiom, `native_decide` or assumed
Scholz target is used.

The existing integration also rechecked both exhaustive 12509 exclusions,
the portable DAG, the saved Mersenne certificate and existing small construction,
export, allocation and negative checks. No ranges were broadened or experiments
added. Those computational checks retain their previous scope; they do not
supply Lean exclusion soundness. Two Python-only reports now say explicitly
that they do not check the general Lean lift, avoiding stale global claims that
the lift is unformalised. Integration's status fields now report the proved lift
and 12525 bound while keeping formal optimality false.

## Next obligation

Milestone 2: formalise exclusion-certificate soundness for arbitrary valid
prefixes, kernel-check target 7 at limit 3, then evaluate the 12509 certificate
to obtain the lower bound 17. Combine it with the now-proved Hansen upper bound.
Do not repeat allocation, shift counting, interleaving fixtures or export work.
Milestone 3's non-Hansen extension experiment remains deferred.
