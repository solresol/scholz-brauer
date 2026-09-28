# 2026-09-29 — Tuesday — distinct shifted Hansen nodes in Lean

Australia/Sydney. One formal increment: the shifted value of a positive
source exponent uniquely determines that exponent and its shift. No new
numerical bound, source optimum, general conjecture proof or novelty claim.

## Mathematical result

`lean/ScholzBrauer/HansenNodes.lean` defines
`shiftedMersenne a k = 2^k * (2^a-1)` and proves, for arbitrary natural shifts:

```
0 < a → 0 < b →
  (shiftedMersenne a k = shiftedMersenne b l ↔ a = b ∧ k = l)
```

For positive a, the Mersenne factor has remainder 1 modulo 2. A separate
lemma proves uniqueness of `2^k*u` for odd natural u by induction on k:
cancel common factors of two; unequal remaining shifts contradict parity.
Equality of the odd factors then gives equality of the exponents by the
pinned mathlib `Nat.pow_right_injective` lemma.

The seven audited general theorems establish odd remainder, odd-part
uniqueness, shifted-value injectivity, positivity, the doubling equation,
the base-node sum equation, and preservation of duplicate-free labels when
mapped to numerical values. The sum equation reuses `mersenne_block_identity`;
the list theorem reuses `List.Nodup.map_on`.

Six checked examples cover exponent zero (where distinct shifts collide),
`a=1` at shifts 0 and 8, both interleaving windows from the saved 29 fixture,
and separation of the 12 and 13 families for arbitrary shifts in the 12509
source. Five examples are closed kernel evaluations; the last applies the
general theorem. These supplement an unbounded proof, not a finite search.
Positivity is necessary: every `(0,k)` has numerical value zero.

The node-list theorem explicitly assumes duplicate-free labels and positive
source exponents. We have not yet defined the entire allocated label family
in Lean or proved its membership, cardinality, endpoint or sorted replay.
Neither the local addition equations nor injectivity alone imply that all
summands required by the allocation exist. The previously proved shift budget
12525 is still a count identity, not a Lean Mersenne-chain bound.

## Sources and reuse

Reinspected the formal-conjectures addition-chain definitions, Scholz statement
and Apache-2.0 licence at revision
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`. The upstream open Scholz statement
remains an uncompiled reference. The new module imports our existing
`BrauerBlock` API; no target conjecture is imported or assumed.

Inspected the reused mathlib natural power-injectivity and list `Nodup.map_on`
source and Apache-2.0 licence at pinned revision
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Lean remains **4.27.0**;
all dependency pins and the manifest are unchanged.

Rechecked on **29 September 2026**:

- [Clift's primary exposition](https://www.additionchains.com/ScholzBrauer.html):
  existing 12509 and `[1,2,4,8,9,12,17,29]` source lists and Hansen construction.
- [OEIS A349044](https://oeis.org/A349044): existing ordinary 17-step and
  star 18-step 12509 source lists match the saved fixtures.

These live pages have no immutable revision recorded. Source metadata is in
`data/2026-09-29-hansen-nodes-sources.json`. Their optimality/frontier claims
are not premises of today's proof. Hansen's original article and larger
non-Hansen data were not inspected or imported.

## Reproduction and verification

From `lean/`, run `lake build` and `lake env lean Audit.lean`.
From the repository root, with a fresh output path, run:

```sh
python3 scripts/verify_integration.py --output results/integration-local.json
```

The saved `results/2026-09-29-integration-checks.json` starts at
**08:05:49 AEST**, Tuesday, and records **56.332228 seconds**, Python **3.9.6**,
46 input hashes, five matching vendored hashes and all exact command outputs.
The run passed:

- Lean build, **754 jobs**, **4.770335 s** with the new module already compiled;
- **69** named theorem axiom audit, **7.275747 s**, only `propext`,
  `Quot.sound` and `Classical.choice`; no sorry or custom axiom;
- both exhaustive <=16-step 12509 exclusions, each visiting 1,345,873 prefixes;
- portable exclusion replay, independent exact 12525-step Hansen certificate
  replay, the existing star/Hansen/search/export oracles and corruption checks.

The earlier pinned build compiled the new module in 3.9 s, then completed
all 754 jobs. Two development checks initially failed on proof elaboration
and a natural-number rewrite; both were corrected before this successful
build and full integration. No failed check is counted as proof evidence.
All successful Lean commands ran with cwd `lean/`. No random seed or heuristic
search was used. Compiled local sources contain no sorry, admit, custom axiom,
native_decide or unsafe declaration.

## Conclusion and next work

Positive shifted-node collisions are ruled out by Lean. The general Hansen
allocation and sorted replay remain unformalised. Computationally,
`ell(12509)=17` and the 12525-step Mersenne witness still establish Scholz at
12509. Lean retains source bounds `[14,17]` and Mersenne upper bound **12526**;
no Lean optimum or improved 12525 bound is claimed.

Next computational increment: expose labelled allocation/summand dependencies
for 29 and 12509 with an independent closure/count/endpoint checker, within
explicit budgets. Next Lean increment: prove allocated summand membership,
then use positivity, the two sum identities and distinctness for sorted replay.
Portable exclusion soundness remains separate; larger non-Hansen cases are
deferred. No mathematical hypothesis was refuted today; the zero-exponent
collision documents a necessary theorem precondition.
