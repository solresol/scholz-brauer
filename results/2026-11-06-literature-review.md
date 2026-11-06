# Weekly human-literature checkpoint — 6 November 2026 UTC

Scheduled 23:00 UTC / 7 November Sydney. Sources accessed **6 November UTC**;
previous successful review [30 October](2026-10-30-literature-review.md).
Search overlap starts **23 October UTC**, including revised records.

**No usable new source was located for the unrestricted Scholz bound or the
selected-109 exclusion.** The new journal item screened below has a different
probabilistic objective. This is a bounded conclusion, not a universal claim
about outside progress.

## Exact formulation and research implication

Read README, TODO, research log, the prior review and the 6 November sparse
domain record on fetched main `a4d5db03e8a622b8a7b46848b64f80b3f302ce94`.
The general target is `ell(2^n−1)<=n−1+ell(n)` for unrestricted increasing
addition chains. For Clift's selected graph, the exact minimum 109 doublings
is computational; Lean exclusion of all 108-doubling labellings is unfinished.
The necessary domain is now **344 ordered pairs**, not the stale 646.
Actual exceptional positions, interval/cap constraints, dissociation, both
odd-run restrictions, twelve families and 64 orientations must still be joined.
Neither feasibility nor `min(u,d1)=1` follows. Completed Hansen, 12509 and
one-gap-family results should not be repeated.

No external result checked changes that plan or warrants larger enumeration.

## Primary-source rechecks and one journal screen

- De Koninck–Doyon–Verreault,
  [2609.28374](https://arxiv.org/abs/2609.28374), remains **v1, 23 September
  2026**. Re-read [Theorems 1–2](https://arxiv.org/html/2609.28374v1).
  Counting bounds require sufficiently large parameters, with
  `m^0.9<r<m` for chain counts and `m^0.9<r<=c*m/log(m)`, `0<c<log(2)`,
  for the two-sided endpoint count. This is a supplied mathematical proof,
  not a pointwise fixed-graph exclusion. Retain the earlier optional full
  reading for counting ideas; it is not the current classification shortcut.
- Agama's [2108.07720](https://arxiv.org/abs/2108.07720) remains **v12,
  28 March 2026**. The
  [viXra multi-step record](https://vixra.org/abs/2608.0060) still lists only
  **v1, 16 August 2026**, and
  [Li's AiraXiv record](https://airaxiv.com/papers/view/2609.0042/) still
  lists **v1, 24 September**. No new revision was displayed. Retain the
  30 October version-specific hypothesis objections; they were not re-proved
  or promoted to new discoveries. The
  [HAL copy](https://hal.science/hal-05756234v1) was again inaccessible, so
  no repair in that text is verified. Further full reading is useful only
  after a source supplies the missing hypotheses.
- [Clift's own account](https://www.additionchains.com/ScholzBrauer.html)
  still shows the selected 109 parent choice and sixteen 5,784,689 chains.
  This is the primary computational account, not a universal proof. No
  unrelated automated activity was counted.
- Bonner, [*On the moments of the Ulam–Kac adder*](https://doi.org/10.1017/jpr.2026.10136),
  published online **4 November 2026**, was screened at the publisher
  abstract. Its sequence is `X_(n+1)=X_n+X_U(n)`, with independent uniform
  `U(n)` in `0..n`; the result concerns fixed-moment asymptotics. That
  random star-chain process does not give an unrestricted minimum or the
  108-budget interval classification. Direct publisher full-text access was
  unavailable; no full-paper audit is claimed or needed for this exclusion.
  Full reading is not a current priority.

## Search and access checkpoint

[arXiv API](https://export.arxiv.org/api/query), `lastUpdatedDate` descending,
`start=0`, `max_results=100`: `ti:"addition chain" OR ti:"addition chains" OR
ti:Scholz` returned **33/33** records; `all:"addition chains" OR
all:"Scholz-Brauer"` returned **36/36**. All dates/titles were screened.
The title query's sole overlap record was unrelated Fargues–Scholze work;
the broader query had no update since 23 October.

Supplementary searches included Cambridge, Springer/Computing/Annals of
Combinatorics, Elsevier, SIAM, Project Euclid and primary author/preprint
sources. No applicable new theorem was located. The HAL and journal full-text
limits above prevent exhaustive claims but do not change the current choice.
Next overlap starts **30 October UTC**.

Documentation only. The shared startup check failed at missing
`/workspace/shared/theorem-provers/scholz-ready.json`; no project Lean build,
preparation, new enumeration, pin/environment/schedule change or Raksasa
access was attempted.
