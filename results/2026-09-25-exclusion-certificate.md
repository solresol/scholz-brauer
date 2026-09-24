# Portable exclusion certificate for 12509

25 September 2026, Friday, Australia/Sydney. This increment packages the
already established computational exclusion into independently checkable data.
It gives no new numerical bound and is not a Lean proof.

## Result and format

`2026-09-25-12509-exclusion-certificate.json` excludes all increasing addition
chains for 12509 with at most 16 additions. It contains 29,437 distinct proof
nodes, is 2,464,503 bytes, and has SHA-256
`516a54800a296da300cc15da318c40b06b08a18270c93b8467f3f843a8b074e9`.
Full checking visits 1,345,873 contextual occurrences: 481,259 gap rules and
864,614 splits (including empty splits); this instance needs no bound leaf.
The node count measures shared syntax, not distinct search states.

The JSON object has exactly `format`, `target`, `max_steps`, `nodes` and `root`.
Format is `addition-chain-exclusion-v1`. Nodes are indexed from zero; the root
is the final node and every child reference is strictly smaller than its parent.
All nodes must be reachable. The checker pins the expected target and step limit
separately; changing the statement in the file cannot silently change the claim.

Each node has one of three forms, interpreted at a current valid prefix `c`
ending at `m`, with `r` additions remaining and target `n`:

- `["bound"]`: require `m * 2^r < n`.
- `["gap"]`: require `r = 1` and no pair of entries of `c` sums to `n`.
- `["split", [[v_0, child_0], ...]]`: require `r > 0` and the labels are
  exactly the sorted, distinct earlier-pair sums `v` satisfying
  `m < v <= n` and `v * 2^(r-1) >= n`. Check every child in context
  `c ++ [v]`, with `r-1` remaining additions.

Every rule first rejects a context that has already reached `n`. Thus the
semantics cover **at most** the allowed number of additions, including zero.
The root context is `[1]` with the stated step limit. A split with no feasible
values is a valid leaf. Duplicate summand decompositions do not create different
value-chain continuations, so only next values are deduplicated.

## Soundness argument and Lean interface still to prove

For any positive increasing prefix, an addition of two stored entries is at
most twice its maximum. Induction bounds the maximum after at most `r` more
additions by `m * 2^r`. This proves the bound rule and justifies dropping
next values that cannot reach the target even with all remaining doublings.
The gap rule excludes the only possible final step; stopping immediately was
already rejected. For a split, any extension to the target either stops now
or has a next value. The first case is rejected. In the second, that value is
a sum of earlier entries, exceeds the current maximum, cannot exceed the
endpoint of an increasing chain, and satisfies the necessary doubling bound.
It therefore appears in the checked list of children. Induction on the remaining
step count excludes its continuation. The empty list case excludes all choices.

The future Lean theorem should express: acceptance at a valid prefix `c`
implies there is no suffix `s` of length at most `r` for which `c ++ s` is an
`IsAdditionChain` ending at `n`. Reuse the adapted upstream definition and
`one_le_of_mem`; its nonlocal summand-membership formulation is compatible
because positive summands are strictly smaller than their sum and hence occur
earlier in the sorted list. Prove the extension doubling lemma, split coverage,
and rule soundness, then instantiate the root. To turn exclusion into a bound
on `additionChainLength`, use a known witness to establish nonemptiness and
`Nat.sInf_mem`. No version of this checker theorem is assumed or compiled today.

Sharing a node does **not** allow reuse of its truth across different prefixes.
The checker traverses every contextual occurrence, with no cache of conclusions
by node id. A deliberate false certificate for 15 at limit 5 exposes this:
the shared gap node is valid at `[1,2,3,4,8]`, but invalid at `[1,2,3,5,10]`
because `15 = 5+10`. The checker rejects it. This is a regression against an
unsound optimisation, not a counterexample to Scholz or a new mathematical claim.

## Construction, bounds and verification

The generator performs exact exhaustive search, interning identical proof
syntax after child construction. It uses ordered-pair sets and a one-step
complement test. The standalone checker imports no generator or search code;
it reconstructs triangular-pair sets and checks gap rules by testing every pair.
Both use Python integers, with accepted targets 1..2^30 and limits 0..32.
They default to 2,000,000 contextual visits. A stopped generator returns
`budget` and writes no certificate; a witness also produces no exclusion file.
A stopped checker raises an error and makes no exclusion claim. This generator
does not checkpoint partial proofs; the older exact search still supports
restartable frontiers. The complete 12509 certificate is the durable result.

Commands run from the repository root:

```sh
python3 scripts/exclusion_certificate.py 12509 16 --output results/2026-09-25-12509-exclusion-certificate.json
python3 scripts/check_exclusion.py results/2026-09-25-12509-exclusion-certificate.json --target 12509 --max-steps 16
python3 scripts/verify_exclusion.py --regenerate --output results/2026-09-25-exclusion-checks.json
python3 scripts/verify_integration.py --output results/2026-09-25-integration-checks.json
```

Use fresh output paths when reproducing; existing reports/certificates are
refused. Python 3.9.6, standard library only for the new code, exact arithmetic,
no random seed. Final regeneration took 12.572508s and matched the saved JSON
object exactly. Independent checking took 13.591166s; the dedicated verifier
took 26.833186s. The input hashes in both final reports match the current files.

All 576 decisions for targets 1..64 and limits 0..8 match unpruned enumeration
of 78,758 prefixes: 374 checked exclusions and 202 checked witnesses. There are
32 rejection cases, seven invalid generator requests, zero/insufficient/exact
budget tests, no-file-on-budget/witness tests and existing-file preservation.
The checker also accepts a valid certificate and rejects a false one under
Python `-O`: soundness checks do not depend on assertions. The verification
harness itself refuses `-O`.

Full integration passed in 51.246500s, including both previous exhaustive
12509 searches, the star/Hansen lifts, saved certificates, five vendor hashes,
the pinned Lean 4.27.0 build (5.761380s) and 43-theorem axiom audit (8.709397s).
Only standard axioms were reported. No Lean source, dependency pin or theorem
changed. The first successful dedicated test run preceded two additional
budget/input tests; its report was replaced by the final-source run above.
No failed mathematical hypothesis or new counterexample resulted.

## Source checks and limits

On 25 September AEST, re-opened [Clift's account](https://www.additionchains.com/ScholzBrauer.html),
matched its 17-step chain to the local fixture and recorded unchanged HTML hash
`d8a9482f19403d42110b52462f88aee41bf291e2a908a203fb9efb8320bd9eef`.
Re-opened [OEIS A349044](https://oeis.org/A349044) through the web tool and
matched both its 17-step non-star and 18-step star lists; direct HTTP returned
403, so no raw OEIS hash is asserted. Its erroneous non-star index gloss is
not used. Re-read [Knuth's ACHAIN-ALL source](https://www-cs-faculty.stanford.edu/~knuth/programs/achain-all.w):
that program consumes precomputed minimum lengths and enumerates canonical
optimal chains. This implementation imports neither its code nor its data or
pruning assumptions. URLs, live-source versions, retrieval times and available
hashes are in `data/2026-09-25-exclusion-sources.json`.

The local conclusion remains `ell(12509)=17` computationally and, with the
already checked 12,525-step Hansen witness, the Scholz inequality at 12509.
Lean source bounds remain `[14,17]`, and its Mersenne upper bound remains 12526.
There is no Lean exclusion or Hansen lift theorem, no Mersenne optimum, no
universal proof and no novelty or updated literature-frontier claim.

Next: formalise checker soundness and a small case such as exclusion of 7 at
limit 3 before attempting kernel evaluation of the large DAG. Saturday's Hansen
work still starts with maximum stored shifts and their telescoping sum; the
underlining invariant is already proved. Larger non-Hansen cases stay deferred.
