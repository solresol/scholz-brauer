# 2026-09-30 — Wednesday — labelled Hansen allocation certificates

Australia/Sydney. Added a bounded label-only generator, a separate allocation
checker and saved dependency graphs for 29 and 12509. They reproduce the
existing Mersenne witnesses and expose the membership obligations for Lean.
No new numerical bound, optimum, general Lean theorem or novelty is claimed.

## Format and mathematical interface

`hansen-labelled-allocation-v1` records the increasing source values, marked
indices including both endpoints, one shift cap per source value, explicit
target exponent and addition count, and a list of node records. Every record
has a `label: [a,k]` and two `summands` labels, except the seed `[1,0]`, whose
summands are `null`. Numerical Mersenne values are not stored. Source order
is part of the statement; the serialization order of node records is immaterial.
Unknown extra object fields are ignored; all required fields are checked.

For a source `a_0=1 < ... < a_r=n`, let `cap(a)` be the gap to the next mark
when a is marked and not final, and zero at unmarked or final source values.
The entire allocated family is

```
F = {(a,k) : a is a source value, 0 <= k <= cap(a)}.
V(a,k) = 2^k * (2^a - 1).
```

The exact dependency rules are:

- Seed `(1,0)`: no dependencies.
- Shift `(a,k+1)`: two copies of `(a,k)`.
- Source base `(v,0)`, with `v=a+b` and a the latest prior mark:
  `(a,b)` and `(b,0)`, in that order.

`hansen_allocation.py` reuses the existing checked source plan, which computes
caps by maximising demands. It emits labels and dependencies without constructing
large integers. `check_hansen_allocation.py` imports no generator. It instead
partitions the source at consecutive marks, derives each cap from their gap,
checks every intervening source step by subtraction and prior membership,
and requires exactly the full family F, with no duplicates or omitted labels.
It checks every dependency against the rule and the allocated family.

The checker then checks `a+k <= n`, evaluates every V exactly, requires distinct
values and endpoints `(1,0)` and `(n,0)`, and sorts by V. Each positive summand
must be smaller than its result and the integer sum must be exact. The compiled
index certificate is independently replayed by `check_certificate.py` and its
values compared with the sorted allocation. External expected exponent and
addition count must match the document; the checker does not trust metadata
to select the statement being checked.

The intended general argument, **not yet formalised as an allocation theorem**,
has the following Lean obligations:

1. Define the finite family F from the source and caps. Prove it duplicate-free,
   with positive first coordinates and `|F| = (r+1)+(n-1) = n+r`.
2. Prove all `(a,0)` source bases are present. For an allocated positive shift,
   its predecessor shift is present. At a source step `v=a+b`, prior membership
   supplies `(b,0)` and the proved shift-demand bound supplies `(a,b)`.
3. Use `shiftedMersenne_succ` and `shiftedMersenne_base_sum` for the local sums,
   `shiftedMersenne_pos` for strict predecessor inequalities, and
   `shiftedMersenne_nodup` for distinct numerical values.
4. Show the endpoint envelope: marked shifts satisfy `a+k <= nextMark <= n`;
   unmarked values have shift zero. Thus `V(a,k)=2^(a+k)-2^k <= 2^n-1`.
   The seed and final base are present. Sort and derive successful replay with
   exactly `|F|-1 = n-1+r` additions.

These obligations fit the existing upstream `IsAdditionChain` definition:
head 1, strict increasing order, and an internal sum decomposition for every
other value. Sorting plus positivity makes the summands earlier. Reinspected
the pinned formal-conjectures definition and Scholz statement; the open target
remains an uncompiled reference. No Lean source, licence or dependency changed.

The allocation order must not be treated as numerical order. For example,
`V(8,1)=510 < V(9,0)=511 < V(8,2)=1020`; a whole block for exponent 8 cannot
be appended before all later source bases. Both saved nontrivial allocations
have this interleaving. This reconfirms the previously documented limitation
of sequential star blocks; it is not a new failed mathematical hypothesis.

## Exact results

| Source | Source steps | Nodes | Shift nodes | Base-sum nodes | Additions |
| --- | ---: | ---: | ---: | ---: | ---: |
| Singleton `[1]` | 0 | 1 | 0 | 0 | 0 |
| Clift interleaving 29 | 7 | 36 | 28 | 7 | 35 |
| OEIS 12509 | 17 | 12526 | 12508 | 17 | 12525 |
| Clift 12509 | 17 | 12526 | 12508 | 17 | 12525 |

All four allocations pass closure/count/endpoint and exact sorted replay.
Reversing every node list leaves the resulting certificate unchanged. The
OEIS 12509 replay agrees pair-for-pair with the saved 21 September certificate.
Both saved labelled objects regenerate identically and are fully read back.
The 12509 graph contains 25050 dependency edges, counting repeated summands.

Exhaustive regression covers **1051** increasing source chains of at most
six additions and endpoint at most 32, **30582** marking masks and all **5248**
accepted underlinings. The independent mask oracle determines accepted cases;
the new checker validates each generated allocation, and the compiled pairs
are compared with the existing integer lift. All seven non-Hansen sources
in this bounded family are rejected. This is construction testing, not a
minimum-length search or a proof for all Hansen sources.

Both normal Python and `python3 -O` pass **40** damaged-document cases,
**12** invalid generator cases and **14** budget/expected-statement cases.
Cases include missing/duplicate nodes, self-dependencies, wrong base summands,
huge or negative labels, boolean integers, invalid marks, stale caps, omitted
fields and changed endpoints/counts. Exact budget boundaries pass. CLI tests
check generation/readback, overwrite refusal with bytes preserved, and no
output file after budget or non-Hansen rejection. The three deliberately
rejected CLI invocations exit nonzero; those are successful rejection tests.

Defaults cap the exponent at **16384**, nodes at **20000**, and CLI input at
**4000000 bytes**. Bounds precede Mersenne evaluation. This run uses no
randomness, heuristic search or larger non-Hansen input.

## Sources and reproduction

Rechecked on **30 September 2026**:

- [Clift's primary exposition](https://www.additionchains.com/ScholzBrauer.html):
  underlining, edge labels and the source chains for 29 and 12509. The web tool
  returned restricted-URL errors; HTTPS curl retrieved the page successfully.
  Its SHA-256 is `d8a9482f19403d42110b52462f88aee41bf291e2a908a203fb9efb8320bd9eef`,
  matching the 21 September retrieval. No immutable page revision is known.
- [OEIS A349044](https://oeis.org/A349044): rechecked both published 12509 lists.
  The entry's optimality assertions are not premises of the allocation checks.

Dated source metadata is in `data/2026-09-30-hansen-allocation-sources.json`.
Hansen's original article and the larger non-Hansen data have not been
independently checked. No current frontier or literature novelty is asserted.

From the repository root, use fresh output paths:

```sh
python3 scripts/hansen_allocation.py data/12509-hansen.json results/allocation-local.json
python3 scripts/check_hansen_allocation.py results/allocation-local.json --exponent 12509 --additions 12525
python3 scripts/verify_hansen_allocation.py --output results/allocation-checks-local.json
python3 -O scripts/verify_hansen_allocation.py --output results/allocation-optimized-local.json
python3 scripts/verify_integration.py --output results/integration-local.json
```

Saved normal and optimised verifier runs took **1.873857 s** and **1.864655 s**.
Python **3.9.6**, standard library only, exact integers, no seed. Full integration
started **08:07:07 AEST** and passed in **54.070592 s**. It records 52 matching
input hashes, five vendor hashes, both exhaustive 1345873-prefix exclusions,
portable exclusion replay, all existing checks, and both new verifier modes.
Pinned Lean **4.27.0** build passed **754 jobs** in **5.213070 s**; the
**69-theorem** audit passed in **7.951427 s**, using only standard axioms.
Every integration subprocess exited zero; no timeout occurred. Lake ran in
`lean/`, with existing dependency pins unchanged.

Saved allocation SHA-256:

- 29: `e83628e1cbbc179cbd15e84ed0b38e69b5b6e12d0710e65fd7b27be2c806d391`
- 12509: `d002aa8bb8eb40ab783f96603b2cafbe159e69e901ab243b4686b3f2aa1ef9b1`

## Conclusion and next

The new artifact exposes an independently checked allocation/dependency
interface for the next formal step. It adds no optimum evidence by itself.
Existing integration reconfirms computational `ell(12509)=17` and
`ell(2^12509-1) <= 12525`, hence Scholz at 12509. The minimum Mersenne length
is unknown here. Lean retains source bounds `[14,17]`, Mersenne upper bound
12526 and Hansen allocation budget 12525. The general Hansen allocation and
sorted replay are still unformalised.

Next: define F in Lean and prove both summands are allocated for every node;
then derive sorted replay. Exclusion-checker soundness remains a separate task.
Larger non-Hansen cases remain deferred until that infrastructure is ready.
