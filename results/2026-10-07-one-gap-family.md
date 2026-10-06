# An infinite one-gap family and Scholz at 29

7 October 2026, Wednesday, Australia/Sydney (AEDT). Milestone 3.
Milestones 1 and 2 were complete at c883604 and were not reopened.

## Completed mathematical obligations

Put `A=2^a`, `B=2^b`, `D=A+B+1`, `n=3*A+B+1`, with `1≤b<a`.
The source is

```
1,2,4,...,A,A+1,D,2*A,n.
```

`OneGapLift.lean` proves that this source is an addition chain with exactly
`r=a+4` additions and that there exists a successful summand-value replay
ending at `2^n-1` with exactly `n-1+r` additions. Its source is non-Hansen for
**every `a≥3`**, regardless of all marking choices and alternative summands.
This is an infinite-family theorem, not extrapolation from bounded tests.

The unqualified hypothesis that every proposed source is non-Hansen is false.
At `(a,b)=(2,1)`, the source is `[1,2,4,5,7,8,15]`. The alternative sum `8=7+1`
allows a marking; `boundary_is_hansen` checks one in the kernel. The bounded
experiment finds both endpoint-fixed markings. The lift still works and has
20 additions; no claim of source or Mersenne optimality follows from that count.

The existing exclusion checker now kernel-checks all 59 contextual occurrences
of a 22-node certificate excluding every source chain for 29 with at most six
additions. The checked seven-addition source supplies the upper bound, proving
`length29_eq_seven`. `scholz29` combines this with **the new family theorem** at
`a=3,b=2`, giving `ell(2^29-1) ≤ 35 = 28+ell(29)`.
The source lower bound is a Lean theorem, not just a Python search result.

## Construction and why the proof strategy changed

Write `M(t)=2^t-1`. The powers-of-two spine reaches `M(A)` in `A-1+a`
additions and retains `2*M(B)`. The latter invariant is proved by induction:
each spine block retains its first doubling as well as every earlier value.
The repair then performs:

1. `B+1` doublings of `M(A)`, reaching `X=2^(B+1)*M(A)`.
2. Insert `E=X+1`, then `E+2*M(B)=M(D)` using the previously proved local identity.
3. Resume from stored `X` for `A-B-1` doublings, reaching `2^A*M(A)`.
4. Add stored `M(A)` to reach `M(2*A)`.
5. Double `D` times and add stored `M(D)`, reaching `M(n)`.

The proved window is `X < E < M(D) < 2*X`. Thus the first resumed doubling
exceeds the inserted nodes; ordinary doubling preserves the order thereafter.
Every required summand is retained, and strict growth proves distinctness.
The suffix adds `A+D+4=2*A+B+5` entries, so the total is exactly
`n-1+(a+4)` additions. No sorting, collision test or empirical uniqueness is
assumed in this proof. Existing `additionChain_exists_replay` realises the
resulting strictly increasing chain with a summand-value certificate.

This resolves the earlier allocation/count obligations by a simpler explicit
order. A new labelled allocator or general exceptional-odd-part injectivity
framework was unnecessary. The proof does not claim extensional equivalence
between a Lean executable generator and the Python allocation.

`repair_chain` is more general: any valid prefix ending at `M(A)` and already
containing `2*M(B)` works when `B≥1` and `B+2≤A`. The additional
`hansen_prefix_repair_certificate` corollary uses the completed Hansen lift and
its labelled interface: the explicit hypothesis `(B,1) ∈ hansenLabels 1 steps`
supplies that summand and gives the exact extended count. No claim is made that
every Hansen prefix or every arbitrary source satisfies this hypothesis.

The marking obstruction examines a prefix ending at `H=A/2`. Its entries
are at most H and are either 1 or even. The next doubling forces the carried
anchor to H; the A+1 step forces A to be marked. The D step then forces A+1 to
be marked. Neither possible next anchor, A+1 or D, can supply 2*A with an
available summand. The inequality H≥4 excludes the boundary exception.
`family_marked_source` identifies the arbitrary Boolean-marked list with the
actual source family. This concerns chosen **source chains**, not a claim that
these integers have no alternative Hansen source.

## Exact experiment and provenance

`scripts/experiment_one_gap_family.py` checks every one of the 36 integer pairs
`2≤a≤9`, `1≤b<a`. This covers source endpoints 15 through 1793 (a sparse family,
not every integer in that interval). It compares the direct insertion order
with a separately constructed, numerically sorted labelled allocation, verifies
all local sums and absence of carries/collisions, then invokes the existing
independent summand-index checker. All caps sum to `n-1`; all addition counts
are `n-1+(a+4)`. Maximum witness length: 1805 additions at `(9,8)`.

All 57,376 endpoint-fixed source markings in this domain are exhausted and
compared with the existing underlining detector. Every possible unordered
source summand pair is checked; only the boundary member has an alternative
parent pair. This is not a search over all source chains or lift labellings.
The infinite classification is separately proved in Lean.

The same experiment regenerates the source-29 exclusion with a 1000-prefix
budget, independently checks it, and compares every node and the root with
the Lean data. It finishes after 59 prefixes; no timeout or budget exhaustion
is treated as exclusion. The existing generator/checker and Lean exclusion
format are reused unchanged. The kernel evaluates the full candidate data and
uses the already proved general exclusion soundness theorem.

Final saved experiment: Python 3.11.6, standard library, exact integers, no random
seed, **0.155038 seconds**. Output: `2026-10-07-one-gap-checks.json`.
The integration report records a separate final-source rerun and input hashes.

[Clift's primary notes](https://www.additionchains.com/ScholzBrauer.html), live
undated page, accessed 7 October 2026, were re-read before using the motivating
29 source and its displayed lifted prefix/endpoints. They match the previously
saved source data. The parametric family is our proof construction; it is not
attributed to a claim on that page. No novelty, priority or new numerical bound
is asserted. Larger published graphs and their optimality claims are not used.

The inspected formal-conjectures addition-chain definition and Scholz statement
remain at `40e7c98697de6f66b8cbdbf641749ab39ed9c152`, with Apache-2.0 attribution.
The open statement is uncompiled and supplies no axiom or assumed target.
Lean 4.27.0 and mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900` remain pinned.

## Verification and retained limits

Commands, run from the repository root except the indicated Lean command:

```
python3 scripts/experiment_one_gap_family.py --output results/2026-10-07-one-gap-checks.json
# From lean/:
lake env lean ScholzBrauer/OneGapLift.lean
# From the repository root:
python3 scripts/verify_integration.py --output results/2026-10-07-integration-checks.json
```

**Integration.** Full integration passed in **169.977119 seconds**. The pinned
Lean 4.27.0 build passed all 782 jobs in 25.424390s; the 162 named theorem audits
passed in 18.058938s. Dependencies are only `propext`, `Quot.sound` and
`Classical.choice`; the source scan found no prohibited proof tokens. All five
vendored hashes and all 90 integration input hashes matched. The final experiment
rerun is recorded alongside every command/output in the integration JSON.
No new dependency, checker format, exporter or approval boundary was introduced.
Reviewed the full source/document diff, generated result rows and certificate,
command outputs and hashes before committing. Remote CI for this commit is
separate from these successful local checks.

During development, the first file write used an extra `lean/` component from
inside lean/ and failed without creating a file. Early proofs needed explicit
endpoint arguments and simplification of Boolean conditionals before arithmetic;
normalising powers/products fixed the remaining equality obligations. These
were proof elaboration issues, not counterexamples. The non-Hansen boundary
exception is a mathematical correction and is retained in the theorem statements.

The full family source optimum and Mersenne optimum remain unproved here.
`scholz_of_optimal_family` makes the former an explicit hypothesis. Only the
motivating 29 source optimum is closed in this run. The repaired-block theorem
is a sufficient construction, not a universal extension beyond Hansen.

Next: reconstruct and validate Clift's small reduced 109 graph from its primary
diagram, then test a precisely stated carry-free labelling/critical-path
hypothesis or prove its structural obstruction. Do not move to 5,784,689 or
repeat the completed 29 labelling search without a new mathematical reason.
