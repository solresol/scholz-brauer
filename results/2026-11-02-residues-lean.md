# Residue restriction for the selected 109 graph — 2 November 2026

Monday, Australia/Sydney. Active milestone 3; milestones 1 and 2 remain
complete. Clean main at e4ebd0e, correct origin, fetch/ff-only current; no
competing research process. Continued the archived 28 October argument rather
than repeating completed enumerations.

## Mathematical reduction

Combine each 32-pair box factorization with the corresponding nineteen-pair
remainder factorization. The full interval is thus A + (A+d) + E, where A has
51 weights and E has seven. Mapping weights modulo d makes both copies of A
identical. For each residue their contributions are even, so the interval's
odd residue classes equal exactly those occurring oddly in E. In particular
there are at most seven. Nonempty A inside [0,108] forces d<109.

Checking all positive integer d<109 restricts each of u and d1 to:

```
1 2 3 4 5 6 7 8 9 11 13 14 17 18 19 26 27 28 29
51 52 53 54 55 56 57 58
```

The final theorem transports both finite domains and both exact residue
fingerprints to every hypothetical budget-108 labelling of the selected graph.
These are necessary conditions, not feasible configurations. They do not prove
min(u,d1)=1, classification of the interval configurations, cap infeasibility,
the full 109 exclusion, or an unrestricted Scholz theorem.

## Representation and verification

The archived attempt stalled before the finite check. Profiling isolated
kernel reduction of the 27-element nested-insert Finset. A duplicate-free
list with a checked Nodup proof supplies the same Finset without that repeated
reduction. Monolithic domain evaluation exceeded the default recursion limit;
a probe with depth 4096 was stopped after memory reached about 4 GB. Splitting
into the 109 Fin cases avoids that monolithic evaluation. The split proof
hit the default 200000 heartbeat budget (28.55 seconds); the final finite
check has a local 2000000 heartbeat allowance. Other proof repairs were
explicit List-to-Multiset coercion, removal of an unused simp argument and
an explicit natural positivity goal instead of unavailable Int.toNat_pos.
No solver, exporter, dependency or certificate format was added.

An independent Python 3.9 exact check over d=1..108 compared Counter counts
of i%d for i=0..108 with the quotient/remainder formula: if floor(109/d) is
even the odd count is 109%d, otherwise it is d-109%d. Both gave the same
27 values in 0.0012 seconds. Reproduce with:

```python
from collections import Counter
counted = [d for d in range(1,109)
           if sum(v % 2 for v in Counter(i % d for i in range(109)).values()) <= 7]
formula = [d for d in range(1,109)
           if (109 % d if (109 // d) % 2 == 0 else d - 109 % d) <= 7]
assert counted == formula
assert len(counted) == 27
```

This is a deterministic exhaustive finite-domain
check, with no seed, and is separate from the Lean proof.

Validation passed:

- Standalone: from `lean/`, `/usr/bin/time -p lake env lean
  ScholzBrauer/Clift109Residues.lean`, 116.36 seconds, no warnings.
- Required integration once: `python3 scripts/verify_integration.py --output
  results/2026-11-02-integration-residues.json`, 391.511694 seconds, 30 commands.
- Full pinned build: 1132 jobs, 132.153547 seconds; residue module 122 seconds.
- Axiom audit: 307 theorems, 12.673040 seconds, only `propext`,
  `Classical.choice`, `Quot.sound`; no sorry or assumed target.
- Independently recomputed all 125 recorded input hashes; all match. Five
  vendored hashes checked. Compared the structured report with 27 October:
  mathematical summaries unchanged; differences are Python 3.9.6 versus 3.11.6,
  dates, timings, temporary paths/diagnostics and expected source/build/audit data.
- Complete source/docs diff, structured report, whitespace and proof-token
  scans reviewed. Original archived source SHA-256 unchanged. Remote CI not checked.

## Sources and next obligation

Read the 30 October weekly literature checkpoint. Rechecked the live primary
[Clift account](https://www.additionchains.com/ScholzBrauer.html) and
[diagram](https://www.additionchains.com/LargeNonHansen.png); both SHA-256 hashes
match 28 October. Access time/version identification is in
`data/2026-11-02-residue-source-recheck.json`. Only the selected parent graph
is used; no new literature theorem or novelty claim is made.

Inspected the adapted addition-chain definitions, upstream Scholz statement,
Apache-2.0 attribution and pinned revision
40e7c98697de6f66b8cbdbf641749ab39ed9c152. The upstream open target remains
unimported. Lean 4.27.0 and the pinned mathlib dependency are unchanged.

Next combine the 27-by-27 necessary step domain and exact fingerprints with
both odd-run restrictions, twelve critical families and 64 orientations.
The remaining interval/cap classification is the blocker to full exclusion;
repeating the existing large computational search does not discharge it.
