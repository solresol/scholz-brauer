# Weekly literature review — 24 October 2026 (Australia/Sydney)

First weekly baseline: no earlier completed weekly human-research handoff was
found. Read the actual roadmap, current declarations/reports and existing source
records before searching. All sources below were accessed **24 October 2026
Australia/Sydney** (23 October UTC). Dates are submission/revision/publication
dates, not search-engine crawl dates. Autonomous-agent activity is not counted
as external mathematical progress.

## Exact target and internal baseline

The target is `ell(2^n-1) <= n-1+ell(n)` for every positive integer n, where
`ell` minimizes additions over unrestricted addition chains, not only star
chains or chains with a selected parent rule. At
`4ff74d328ee47397f7217d3c7e50f5cb5ad967d8`, Hansen lifting and the complete Lean
12509 instance are finished. The active work is the non-Hansen extension:
reduce the selected 109 graph's normalized interval configurations using the
fifteen necessary critical-tail families, orientations and zero constraints,
then kernel-check exclusion; formalize the 5,784,689 loss/halving reductions.

The 109 minimum and exclusions for the sixteen 5,784,689 graphs remain
computational results. The fifteen families are necessary conditions, not
fifteen feasible cases or a complete Lean exclusion. These are already-known
internal results, not new literature findings or a general Scholz proof.

## New to this baseline: quantitative distribution, with limited local use

Jean-Marie De Koninck, Nicolas Doyon and William Verreault,
[*On the distribution of the minimal length of addition chains*](https://arxiv.org/abs/2609.28374v1),
v1 **23 September 2026**, no later version displayed. Read the
[definitions, Theorems 1–2 and step classification](https://arxiv.org/html/2609.28374v1).
They use the same unrestricted increasing-chain definition. For
`F(m,r)=#{n in [2^m,2^(m+1)):ell(n)<=m+r}`, Theorem 2 claims bounds
`K1^r m^r <= F(m,r) <= K2^r m^r`, for sufficiently large m and
`m^0.9 < r <= c m/log m`, with fixed `0<c<log 2`; its upper bound extends to
`r>m^0.9`. Theorem 1 counts distinct length-(m+r) chains, with bounds of scale
`K^r (m²/r)^r` when m,r are sufficiently large and `m^0.9<r<m`.

Classification: **preprint theorem/proof, not independently audited here**.
These are asymptotic counting results, not pointwise optimality certificates,
a general Mersenne lift, or an interval classification for our fixed graphs.
Full reading is worthwhile for future search-count/pruning ideas, but the
displayed range does not justify pruning our small fixed excess or deleting
certificate branches. No immediate change to the current kernel reduction.

## Conditional structural lead: inspect its hypotheses before reuse

Theophilus Agama,
[*An extended structural Scholz result on addition chains*](https://www.researchgate.net/publication/410825971_AN_EXTENDED_STRUCTURAL_SCHOLZ_RESULT_ON_ADDITION_CHAINS),
author-uploaded full text dated **26 July 2026**,
[DOI 10.13140/RG.2.2.14935.23207](https://doi.org/10.13140/RG.2.2.14935.23207).
Read the definitions and Theorem 4.1. For an **optimal** chain with fixed
decomposition `s_i=s_(sigma(i))+s_(tau(i))`, `i>sigma(i)>=tau(i)>=0`, let B be
the indices with `sigma(i)=i-1`, and NB the others. Its claimed Scholz corollary
requires both:

1. For adjacent NB indices `(i-1,i)`, `3<=i<=h-1`,
   `sigma(i-1)<=sigma(i)`; if strict, the difference is 1 and `sigma(i)` is in B.
2. A tau-track index j which never appears as a sigma-track index has j or j+1
   in B.

Classification: **conditional preprint claim with a specific gap in the inspected
proof**. The beginning of the proof of Theorem 4.1 infers that sigma is
nondecreasing, using Proposition 3.2, which itself assumes that property.
Our check of an existing source below shows the inference does not follow from
the two printed hypotheses. Do not reuse the theorem as established progress
without a repair of this step and the remaining construction. The selected 109
graph is also not a supplied optimal-source premise. Full construction reading
is worth revisiting if the missing condition is repaired. The author labels
the copy CC BY-NC-ND 4.0; no text/code was imported.
The [HAL v1 lead](https://hal.science/hal-05756234v1) returned an access-denied
challenge, and the author-copy PDF download returned 404; the author-uploaded
HTML full text was accessible. Identity with the inaccessible HAL file and any
later HAL revision remain unverified.

### Direct check on the existing optimal 29-source

This is this review's source-scope check, not a new chain search or Lean theorem.
The [existing source](../lean/ScholzBrauer/NonHansen29.lean) is
`[1,2,4,8,9,13,16,29]`; `OneGapLift.length29_eq_seven` already proves its
optimal length. Use the summands `2=1+1`, `4=2+2`, `8=4+4`, `9=8+1`,
`13=9+4`, `16=8+8`, `29=16+13`. In the paper's zero-based vertex indices:

```
sigma(1..7) = [0,1,2,3,4,3,6]
tau(1..7)   = [0,1,2,0,2,3,5]
B           = {1,2,3,4,5,7}
NB          = {6}
```

There are no adjacent NB pairs, so condition 1 is vacuous. The only tau index
absent from the sigma image (including sigma(0)=0) is 5, which is in B, so
condition 2 holds. Nevertheless `sigma(5)=4 > sigma(6)=3`: the dominant values
drop from 9 to 8. A deterministic Python integer calculation checked all seven
parent sums, index inequalities, both predicates and this decrease. No files or
dependencies were added for that calculation. This rejects the stated
**monotonicity inference**, not the Scholz inequality at 29, which is already
proved in this repository. It is not a claim that every possible repair fails.

## A general-proof claim screened out at the stated argument

Xiao-Wei Li, [*The Proof of the Scholz-Brower Conjecture*](https://airaxiv.com/papers/view/2609.0042/),
AiraXiv **2609.0042 v1, 24 September 2026** (not an arXiv identifier).
Read the four-page linked PDF, whose title spells Brauer correctly.
Page 2 represents every successive operation as
`x^(m_(i+1)) = x^(m_i) * x^(m_j)` with `j<=i`, then calls this an optimal
unrestricted path. This is a **star-chain restriction**: it always consumes the
last value. The subsequent telescoping count does not justify that restriction
for an unrestricted optimum. This is the missing assumption identified by this
review, not an independent audit of every later line.

Classification: **unsupported general-proof claim at the inspected step**.
Do not retire the target on this basis. The primary Clift source below already
distinguishes unrestricted and optimal-star chains and identifies 12509 as a
case with no optimal star chain. No further reading is needed to reject this
argument as a supplied proof of our exact unrestricted statement; no author
contact was made.

## Revised/background sources, not newly established progress

| Source and exact date/version | Scope checked; implication | Reading decision |
| --- | --- | --- |
| Agama, [arXiv:2108.07720v12](https://arxiv.org/abs/2108.07720v12), revised 28 March 2026 (v1 8 August 2021) | Read §7's carry definition and Theorems 7.3–7.8. The displayed bounds retain explicit carry-degree hypotheses; Theorem 7.8 is not the unconditional `n-1+ell(n)` bound. These remain preprint claims, not a checked replacement for the current graph reductions. | Defer full audit unless a concrete current source satisfies the hypotheses and the claimed bound improves the required budget. |
| Clift, [Scholz–Brauer notes](https://www.additionchains.com/ScholzBrauer.html), undated live author page | Rechecked underlining, the chosen 109 parent graph, and the sixteen 5,784,689 sources. The first non-Hansen/computational range statements remain author-reported computations, not newly proved Lean facts. Choice of parents matters; the same values need not define the same graph. | Continue using attributed graph/source data, with our independent certificate and kernel boundaries retained. |
| Clift, [*Calculating optimal addition chains*, Computing 91 (2011), 265–284](https://doi.org/10.1007/s00607-010-0118-8) | Publisher describes exact-search algorithms and finite computations, not a universal Scholz proof. | Established algorithmic background; no rerun warranted by this review. |

The September distribution paper's predecessor was also located through
[arXiv:2504.07332v1](https://arxiv.org/abs/2504.07332v1) (9 April 2025) and the
[Functiones et Approximatio publisher DOI](https://doi.org/10.7169/facm/241106-7-4).
The publisher rendered only an iframe here; no inaccessible journal-text change
is asserted. It is not needed to certify the current finite targets.

## Decision and search checkpoint

No validated general resolution or source that discharges the current interval
classification was located. This is a scoped result, not a proof that no outside
progress exists or a novelty claim. Continue the fifteen-family interval
reduction and the nine-component loss/halving formalization. The sigma/tau
construction requires a repaired monotonicity argument before reuse; optimality
and source-specific predicates would still have to be checked. Do not rerun the
completed enumerations.

Baseline new/revised search used the [arXiv API](https://export.arxiv.org/api/query)
with `sortBy=lastUpdatedDate`, descending, across all indexed dates:

- `ti:"addition chain" OR ti:"addition chains" OR ti:Scholz`: 32 results,
  all retrieved; unrelated Scholze/Langlands matches excluded.
- `all:"addition chains" OR all:"Scholz-Brauer"`: 36 results, all retrieved.
- Supplementary searches used non-Hansen, carry, Scholz/Brauer, optimal and
  distribution terms across author sources, HAL, Computing/Springer, SIAM,
  Journal of Algorithms/Elsevier and Functiones et Approximatio/Project Euclid.
  The AiraXiv claim was checked at its primary PDF, not inferred from its title.

Next review should use this checkpoint with a seven-day overlap beginning
**17 October 2026 UTC**, and recheck versions, withdrawals and accessible author
copies. The review does not claim exhaustive coverage of unpublished or
differently named work. Source-access restrictions above are limitations, not
empty search results. No proof, dependency, environment, schedule, machine or
author outreach changed. Prepared-runtime `check.py` passed; documentation
validation and the push-triggered verification workflow are the relevant checks.
