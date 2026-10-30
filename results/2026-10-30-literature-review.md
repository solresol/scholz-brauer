# Weekly literature checkpoint — 30 October 2026 UTC

Previous successful review: [24 October Sydney / 23 October UTC](2026-10-24-literature-review.md).
Sources below were accessed **30 October 2026 UTC**. Searched new papers and
revisions with overlap beginning **17 October UTC**, and checked older primary
claims newly surfaced by the broader search. No relevant new/revised arXiv
result or verified result discharging the current target was located. This is
a bounded search conclusion, not a claim that no outside progress exists.

## Current target and consequence

Read `README.md`, `TODO.md`, the research log and current reports at
`3065d4dca7ecddfe8d823d4078ffa473a75ad53e`. The target remains
`ell(2^n-1) <= n-1+ell(n)` for unrestricted increasing addition chains.
The active selected-109 obligation is now a **twelve-family** interval/cap
classification, using the proved exact halvings and both odd-run restrictions
(each count is 1, 3, 5 or 7). The full exclusion remains computational.
The nine-component loss/halving formalization for the sixteen 5,784,689 graphs
is also pending. These are internal status checks, not external literature
findings. Do not repeat completed enumeration or assume `min(u,d1)=1`.

## Older general-proof claim: a version-specific failure to preserve a hypothesis

Theophilus Agama, *The Scholz Conjecture Via a Multi-Step Optimization*:

- [viXra:2608.0060v1 PDF](https://vixra.org/pdf/2608.0060v1.pdf),
  [record](https://vixra.org/abs/2608.0060): submitted **16 August 2026,
  20:17:20**, 15 pages; paper dated 16 August. Only v1 is listed.
- [Author-uploaded full text](https://www.researchgate.net/publication/412298449_THE_SCHOLZ_CONJECTURE_VIA_A_MULTI-STEP_OPTIMIZATION),
  [DOI 10.13140/RG.2.2.32864.24322/2](https://doi.org/10.13140/RG.2.2.32864.24322/2):
  upload and paper date **17 August 2026**. The `/2` identifier is not an
  arXiv revision, and these two texts have materially different hypotheses.

Read definitions, Lemma 4.2 and Theorem 5.1 in both copies. In viXra v1,
Lemma 4.2 claims a nonpositive dominant-multiplicity correction for every
irreducible chain. This is false on the already-known optimal 29-source
`[1,2,4,8,9,13,16,29]`: its unique parent choices give dominant indices
`[0,1,2,3,4,3,6]`, multiplicities `[1,1,1,2,1,0,1]`, and correction
`sum((1-m_t)*s_t, t=1..6) = -8+13 = 5 > 0`.
Every nonterminal term is consumed, so it is irreducible in the paper's sense.
A direct integer check enumerated all earlier parent pairs, confirmed their
uniqueness and consumption, and obtained lower-summand sum 33 rather than 28;
no search or code artifact was added. Source optimality is already proved in
`OneGapLift.length29_eq_seven`.

In the August 17 `/2` copy, Lemma 4.2 assumes a **Brauer** chain. The final
step of Theorem 5.1 nevertheless invokes it after obtaining only irreducibility
of minimum-length unrestricted chains. The missing Brauer premise is not
supplied. Classification: **unsupported universal-proof claim at the inspected
step**, not a refutation of Scholz or of the minimum over all optimal chains.
This is an additional screened source absent from the previous baseline,
not new October mathematical progress. No full-paper audit is claimed.
Further full reading is useful only if that step is repaired; it does not
justify retiring the current non-Hansen programme. No author contact occurred.

## Rechecks and reading decisions

- [De Koninck–Doyon–Verreault, arXiv:2609.28374](https://arxiv.org/abs/2609.28374)
  still lists only **v1, 23 September 2026**. Its counting bounds require
  sufficiently large `m` and `m^0.9 < r <= c*m/log(m)`, `0<c<log(2)`;
  no pointwise fixed-graph exclusion follows. The prior full-reading
  recommendation for future counting ideas stands, with no current shortcut.
- [Agama, arXiv:2108.07720](https://arxiv.org/abs/2108.07720) remains
  **v12, 28 March 2026**. The displayed carry-degree hypotheses remain;
  no newly revised unconditional theorem was found. The July 26
  [structural author copy](https://www.researchgate.net/publication/410825971_AN_EXTENDED_STRUCTURAL_SCHOLZ_RESULT_ON_ADDITION_CHAINS)
  retains the already-recorded nondecreasing-sigma inference. Do not treat it
  as repaired. The [HAL record](https://hal.science/hal-05756234v1) was
  inaccessible through the browsing tool, so later HAL text remains unverified.
- [Li's AiraXiv record](https://airaxiv.com/papers/view/2609.0042/) still shows
  **v1, 24 September 2026**. No new revision was displayed; the prior
  star-chain restriction objection remains the recorded assessment.
- [Clift's live Scholz–Brauer account](https://www.additionchains.com/ScholzBrauer.html)
  retains the selected 109 parent choice and sixteen 5,784,689 sources.
  Its finite computational claims are not universal proofs. Agent-attributed
  activity on other live pages was not counted as human-research progress.

## Search and access checkpoint

The [arXiv API](https://export.arxiv.org/api/query), ordered by
`lastUpdatedDate` descending, returned all **33** records for
`ti:"addition chain" OR ti:"addition chains" OR ti:Scholz`, and all **36** for
`all:"addition chains" OR all:"Scholz-Brauer"` (`max_results=100` each).
The only title-query addition since the baseline is an unrelated
Fargues–Scholze paper; no relevant result in either complete list was updated
within the overlap window. This checks revisions as well as submissions.

Supplementary discovery used addition-chain, non-Hansen, structural-Scholz,
optimal-chain and October-2026 terms, including Springer/Computing/Annals of
Combinatorics, Elsevier, SIAM, Project Euclid and author sources. Publisher
hits on random Brauer-chain decompression (Wallner,
[version of record 25 April 2026](https://doi.org/10.1007/s00026-026-00816-y))
and matrix-polynomial evaluation were screened out as older work without a
current interval-classification consequence. They are not new progress for
this target. The [Functiones publisher DOI](https://doi.org/10.7169/facm/241106-7-4)
still rendered an iframe only; no journal-text revision is verified.

No access gap blocks the present research choice. Continue the current proved
reductions and preserve the prior claim boundaries. Next review should overlap
from **23 October 2026 UTC** and recheck versions and the two distinct August
copies. Documentation only: no proof, experiments, pins, runtime, schedules or
remote-machine work changed; no Lean build was needed.
