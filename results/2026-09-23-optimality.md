# 2026-09-23 — Wednesday — computational optimality at 12509

## Result and scope

Two independently implemented exact traversals exhaust all increasing addition
chains for **12509 with at most 16 additions**. Both visit 1,345,873 prefixes
and terminate normally without a witness. The C++ traversal has no pending
subtree. Combining this exclusion with the previously checked 17-step chain
establishes **ell(12509)=17 computationally**. Replaying the saved Hansen
certificate then establishes

```
ell(2^12509 - 1) <= 12525 = 12509 - 1 + ell(12509).
```

Thus the repository now computationally verifies this instance of Scholz.
Its optimal checked source has a Hansen underlining, so 12509 is also a Hansen
number by the definition used here. No novelty is claimed: this reproduces a
published example and closes a gap in this repository's evidence.

This is a finite exhaustive computational proof, with an explicit completeness
argument below and two executable implementations. It is **not a Lean proof**
or a standalone exclusion certificate whose checker has been proved sound.
The C++ compiler, Python interpreter and search implementations are trusted.
The two traversals share the elementary doubling argument, so their agreement
is not independent validation of that argument. Their small-family oracle is
unpruned. The formal Lean source bounds remain [14,17], and its Mersenne bound
remains 12526. The star optimum 18 and absence of optimal star chains have not
been independently established here. Neither the minimum Mersenne length nor
the universal Scholz conjecture follows from this increment.

## Rechecked sources and methodology

Access date: **2026-09-23, Australia/Sydney**. Retrieval hashes and failures are
in `data/2026-09-23-optimality-sources.json`. These are live pages, without an
immutable version; the hashes identify the actual retrieved bytes.

- [Clift's calculation notes](https://additionchains.com/Calculating.html)
  describe exact search, position bounds and stronger dual-based pruning, with
  links to source and the 2021 Thurber–Clift paper. They include 12509 in their
  bound examples. We inspected the account, but did not adopt those stronger
  pruning rules or rely on the linked program's results.
- [Knuth's ACHAIN0 source](https://www-cs-faculty.stanford.edu/~knuth/programs/achain0.w)
  describes a reconstruction of his 1969 search. Inspected its introduction,
  pruning explanation and backtracking loop. It fills summands backwards and
  may use supplied lower bounds. Today's implementation is independently
  written, searches forward and uses no table or imported code. Knuth's program
  was not compiled or run; no licence-dependent source was vendored.
- [Flammenkamp's data page](https://wwwhomes.uni-bielefeld.de/achim/addition_chain.html)
  describes published exhaustive results, downloadable packed lengths and
  decoders. Such tables record answers rather than independently checkable
  exclusions. No bulk table was downloaded or trusted by our search.
- [Clift's Scholz notes](https://www.additionchains.com/ScholzBrauer.html)
  were retrieved directly. The entire 17-step list matches the existing Clift
  fixture; the page hash is unchanged from Monday.
- [OEIS A349044](https://oeis.org/A349044) was reopened with the web tool and
  both lists in its EXAMPLE were matched against the existing 17-step and
  18-step fixtures. Direct Python HTTP access returned 403. The page's
  non-star index gloss remains inaccurate; the value 24 after 13 is the
  relevant step. The [A003313 table](https://oeis.org/A003313/b003313.txt)
  opened through the web tool, but retrieving the exact 12509 row failed;
  direct HTTP also returned 403. No table row is used as evidence.

The current source review motivates reproducible exclusion rather than importing
an optimality flag. It is not a literature-frontier survey; no frontier or
new-theorem claim is made.

## Search completeness and arithmetic

For a valid increasing prefix `a_0=1,...,a_d=m` and a total step limit `r`,
let `k=r-d` be the number of available additions.

1. If `m=n`, return the prefix as a witness, even when `d<r`. Thus this searches
   **at most** r additions; it does not assume that shorter chains can be padded.
2. If `k=0` and `m!=n`, there is no extension within the limit. If `m*2^k<n`,
   reject: each future sum is at most twice the current maximum, so even k
   doublings cannot reach n.
3. Every possible next value is some `a_i+a_j` with `0<=j<=i<=d`. Enumerate
   all these sums, including sums that do not use m. Retain only `m<s<=n`
   and `s*2^(k-1)>=n`. The first condition is required by increasing chains;
   the second is the same necessary doubling bound after taking this step.
4. Deduplicate equal sums for the **same prefix**. Future valid additions
   depend on the list of available values, not how a repeated sum was formed.
   Distinct value prefixes are never merged. Visit every remaining child.

Induction on k shows that a complete unsuccessful traversal excludes every
valid extension of its initial prefix. Starting at `[1]` therefore excludes
all chains in scope. The imported Lean predicate also uses strictly increasing
positive chains; no search restriction beyond that mathematical model is added.
The local lower bound then combines with the existing 17-step witness.

C++ uses unsigned 64-bit integers, validates `1<=n<=2^30`, `0<=r<=32` and every
supplied prefix before search. A sum is at most `2^31`; shifts are applied only
to values at most n and never exceed 32 positions, so they are at most `2^62`.
There is no floating-point pruning or overflow in the admitted domain. Python
uses arbitrary-precision integers, an independently written ordered traversal
of sets of pair sums, and a complement-membership test for the last addition.
The C++ traversal visits candidates in descending order; Python uses ascending.
No random seed, external optimum, star restriction or heuristic is involved.

The node budget is tested before processing a prefix. On reaching it, C++ saves
that entire untouched subtree and every unvisited sibling while unwinding.
These incomparable prefixes partition all remaining possibilities. `budget`
never means exclusion. A prefix can be restarted by passing its entries after
the same target, total step limit and a new node budget. A nontrivial-prefix
`exhausted` result applies only to that subtree, not to all chains for n.
Python likewise reports `budget` if its cap is reached; the research verifier
refuses to emit a successful report unless both traversals exhaust their trees.
External termination is an error, never an exclusion result. Today's production
search completed, so there is no unfinished checkpoint to resume.

## Reproduction and verification

From the repository root:

```sh
python3 scripts/verify_search.py --research --output results/optimality-local.json
python3 scripts/verify_integration.py --output results/integration-local.json
```

Use new output paths: both refuse existing reports. The first command compiles
with `c++ -std=c++17 -O3 -Wall -Wextra -Werror` into a temporary directory.
The second additionally runs all prior lift checks, the pinned Lean build and
axiom audit. Exact commands, outputs, compiler version and input hashes are in
the dated JSON reports. To run or resume an individual subtree:

```sh
c++ -std=c++17 -O3 -Wall -Wextra -Werror scripts/search_chain.cpp -o .git/search_chain
.git/search_chain 12509 16 10000000
# Example branch invocation; this result alone cannot exclude the whole tree:
.git/search_chain 12509 16 10000000 1 2 3
```

Recorded standalone verification: **16.561875 seconds**, Python **3.11.6**,
Apple clang **21.0.0**, standard libraries only. The C++ exclusion took
**0.152061s**, cap 10,000,000 nodes; Python took **12.714011s**, cap 2,000,000.
Both completed after **1,345,873** visited prefixes. Tests also include:

- Unpruned enumeration of **78,758** prefixes, at most eight steps and endpoint
  at most 64. Both search decisions match the oracle for every target 1..64 and
  every limit 0..8: **576** comparisons per implementation.
- All **132** seven-step value chains for 29 are covered exactly once by saved
  pending subtrees at node caps 0,1,2,4,7. Every saved subtree is restarted and
  its existence result compared with the oracle. Pairwise incomparability and
  prefix validity are checked. Terminal and exact-budget cases are covered.
- **10** malformed/out-of-domain C++ requests rejected with exit code 2 and no
  result. A zero-budget Python search returns incomplete status.
- Search from `[1,2,4,6,12,13]` with total limit 17 rediscovers the published
  witness after 361,214 prefixes, including its non-star step in the searched
  suffix. Its values are independently checked by `check_chain`.
- The complete 12,525-step Hansen certificate is independently replayed with
  exact integers and the expected endpoint.

The first development checkpoint test incorrectly expected an eight-node cap
to stop before a witness of eight entries. It correctly returned a witness;
the incomplete-status fixture was corrected to seven. This was a test boundary
error, not a failed mathematical hypothesis or evidence against the conjecture.
No hypothesis is retired beyond the already-recorded parent-index assumption.

Full integration passed in **30.853803s**, including the repeated exclusions,
all previous star/Hansen checks, the pinned Lean build, **28** theorem axiom
audits and **five** vendor hashes. All recorded source hashes match final
bytes. The existing-output refusal was checked and preserved the report bytes.
The verifier rejects Python `-O` before running because its assertions must be
enabled; this rejection was tested. Final review added an explicit C++ standard
header and that guard, then both verification commands passed again.

## Next step

Thursday: formalise the Hansen underlining certificate and latest-anchor
invariant. The numerical 12509 gap is now closed computationally. An additional
Lean-checkable exclusion proof is needed to close its formal optimality gap;
keep this separate from the constructive lift. Larger non-Hansen cases remain
deferred until the formal construction and exclusion infrastructure are ready.
