# 2026-09-21 — Monday — checked Hansen lift for 12509

## Result and boundary

The repository now has a reproducible **12,525-addition certificate** for
`2^12509 - 1`, improving its previous checked upper bound by one addition.
Every summand index, strict increase, final integer and addition count passes
the existing independent checker. The full certificate is stored in
`2026-09-21-12509-hansen-certificate.json`.

This establishes the numerical witness bound `ell(2^12509-1) <= 12525`.
It does **not** establish optimality of either chain, the Scholz inequality
for 12509 from local results, or a new Lean theorem. Locally we still have only
`14 <= ell(12509) <= 17`. The right side `12508+ell(12509)` lies in
`[12522,12525]`; a lower bound of 17, or another sufficient argument, is still
needed. A checked Hansen source chain is not evidence that it is a minimum
chain. No novelty or current-frontier claim is made.

## Sources and exact inputs

Access date: **2026-09-21, Australia/Sydney**.

- [Neill Clift, Scholz–Brauer notes](https://www.additionchains.com/ScholzBrauer.html),
  live page, no immutable version. Direct retrieval now works. Used the
  underlining criterion and the labelled-graph construction in its Hansen
  discussion. The definition requires every step to use the largest earlier
  underlined entry as a summand, with the final entry underlined. We also
  underline the initial 1, which is forced by the first step.
- Re-fetched [OEIS A349044](https://oeis.org/A349044), live page, and matched
  its complete 17-step list against the existing Lean witness. Also matched
  Clift's different complete 17-step list. Both lists and hashes of the
  retrieved page bytes are in `data/12509-hansen.json`; exact parent discovery
  independently checked each list. No source minimality assertion is used.
- Hansen's original article is *Zum Scholz-Brauerschen Problem*, J. reine
  angew. Math. **202** (1959), 129–136,
  [DOI 10.1515/crll.1959.202.129](https://doi.org/10.1515/crll.1959.202.129).
  The publisher metadata was retrieved. The
  [EuDML record](https://eudml.org/doc/150404) returned 403 and the
  [GDZ scan resolver](https://gdz.sub.uni-goettingen.de/dms/resolveppn/?PPN=GDZPPN002178354)
  was inaccessible through the web tool. We did not inspect the original
  article's proof. This implementation follows Clift's primary exposition
  with the explicit construction argument below.

Clift also lists larger non-Hansen examples. Those datasets and minimality
claims were not investigated in this increment.

## Executable specification and construction argument

Let the increasing source be `a_0=1,...,a_r=n`, with a valid underlining.
For each `i>0`, let `k` be the greatest underlined index below `i`, and choose
the unique earlier `j` satisfying `a_i=a_k+a_j`. Orient this pair as `(k,j)`.
This specifies the summands existentially from source **values**; a preselected
parent pair is not imposed.

Write `M_a=2^a-1`. The implementation creates these nodes:

1. One base node `M_(a_i)` for every source entry.
2. For each `k`, let `m_k` be the maximum `a_j` over the oriented pairs `(k,j)`,
   or zero if there are none. Create every shifted node
   `2^s M_(a_k)` for `1 <= s <= m_k`, each as the double of its predecessor.
3. Construct base node `M_(a_i)` from
   `2^(a_j) M_(a_k) + M_(a_j)`. Both operands have been included explicitly.

These additions are exact because
`2^b(2^a-1)+(2^b-1)=2^(a+b)-1`.
Each positive operand is smaller than its sum. Sorting all nodes by their
integer values therefore produces a valid increasing addition chain, including
cases where an intermediate doubling must be interleaved with another base
node. Distinct Mersenne bases are distinct odd numbers, so their shifted
families have no collisions. The certificate records ordinary summand indices;
replay needs neither the underlining nor this construction argument.

For consecutive underlined indices `k<h`, all steps `k<i<=h` use anchor `k`.
Their shifts are `a_i-a_k`, with maximum `a_h-a_k`. Non-underlined indices
have no shifted outgoing operands. Thus
`sum(m_k)=sum(a_h-a_k)=n-1` by telescoping. All generated nodes before `h`
are at most `M_(a_h)`, so the largest node is `M_n`. There are `r+1` base
nodes and `n-1` shifted nodes, hence **`n-1+r` additions**. The source `[1]`
gives no additions. This is a mathematical justification, not a Lean proof.

`find_underlining` uses dynamic programming. Its state is the largest
underlined index; each compatible source step branches on marking or not
marking the new entry. Histories reaching the same index are interchangeable
for future steps because the whole source prefix remains available. Retaining
one history per state is therefore complete for the given source values.
At most the source length many states survive each step. `None` means no
valid marking for those values; it makes no statement about other chains
with the same endpoint.

The generator checks its addition budget before constructing large integers
(default 100,000; this run needs 12,525). It refuses existing output paths.
No heuristic search, randomness, optimum search or timeout inference is used.

For the OEIS source, the selected underlined **values** are

```
1,2,6,12,24,48,96,192,384,768,781,1562,3124,6248,12496,12509
```

In particular, 13 stays available as an unshifted Mersenne value without
becoming an anchor. The maximum shifts, in source-entry order, are

```
1,4,0,6,12,0,24,48,96,192,384,13,781,1562,3124,6248,13,0
```

Their sum is 12,508, plus 17 base-node additions, giving 12,525.

## Verification and reproduction

Python **3.9.6**, standard library only; exact integer arithmetic, no seed.
Commands run from the repository root:

```sh
python3 scripts/hansen_lift.py data/12509-hansen.json results/2026-09-21-12509-hansen-certificate.json
python3 scripts/check_certificate.py results/2026-09-21-12509-hansen-certificate.json --exponent 12509 --additions 12525
python3 scripts/verify_hansen_lift.py --output results/2026-09-21-hansen-checks.json
python3 scripts/verify_integration.py --output results/2026-09-21-integration-checks.json
```

Use fresh output filenames on reruns: the checked-in reports/certificate
already exist. The verifier compares regenerated pairs to the saved certificate.

- Exhaustively enumerated **1,051** distinct addition-chain prefixes with at
  most **six additions** and endpoint at most **32**. For each, independently
  tested every marking mask using all possible parent pairs discovered from
  values: **30,582 masks**, **5,248 accepted underlinings**, **7 source chains
  with none**. These seven are not non-Hansen *numbers*.
- The DP agreed with the mask oracle for every source. For **every accepted
  underlining**, generated a lift, independently replayed it, and rediscovered
  all valid summand pairs from its resulting values.
- For all **842 star sources** in this family, underlining every entry gave
  exactly the same lifted values as the existing Brauer generator.
- Additional length-seven source regressions at endpoint 29 distinguish
  `[1,2,4,8,9,12,17,29]` (Hansen) from `[1,2,4,8,9,13,16,29]` (not Hansen).
  Each checks all 64 masks. The positive source also lifts to 35 additions.
  These confirm known structural examples, not a failed new hypothesis.
- Both published 17-step sources for **12509** yield independently replayed
  12,525-addition certificates. The OEIS certificate is persisted in full.
  Replaying it without any provenance fields also passes.
- **21 negative checks** cover malformed inputs, invalid markings, a non-Hansen
  source, a too-small budget, false endpoint/count and a damaged certificate.
  Both new CLIs refused pre-existing output and preserved its exact bytes.
- Standalone Hansen verification: **1.864757 s**. Combined integration:
  **16.384824 s**, starting **2026-09-21T08:06:00.889872+10:00**.
  All previous witness/star regressions passed too. Each integration subprocess
  has a 180-second timeout; no timeout occurred.
- Pinned **Lean 4.27.0** build passed (749 jobs; **5.695999 s**), and all
  **15** named theorem axiom audits passed (**7.757748 s**). Five upstream
  source hashes matched. No Lean source, toolchain or dependency changed;
  these checks do not formalise the new Python lift.

Complete input hashes, outputs and timings are in the two JSON reports.
The complete Mersenne certificate SHA-256 is
`3662884e8f514fb682c6407ebe3593d724471183c9d21d09aa11e37342fe0c11`.
Reviewed the full source/documentation diff and the structured reports;
every pair in the compact certificate was independently replayed.

## Next

Tuesday: finish the whole-star Lean invariant and telescoping proof from the
already proved Brauer block. Next computational increment: obtain auditable
optimality evidence for 12509, keeping published claims and local exclusions
separate. The new Hansen construction supplies a subsequent formalisation
target. Larger non-Hansen searches remain deferred.
