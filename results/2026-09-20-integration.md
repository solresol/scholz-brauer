# 2026-09-20 — Sunday — evidence integration

## Increment

Added `scripts/verify_integration.py`, a single bounded command combining the
existing independent Python checks, Lean build, theorem axiom audit, toolchain
version check and five vendored source hashes. It records the actual inputs by
SHA-256, all command outputs and runtimes, and the current claim limits. It
refuses existing output files and writes a report only after all checks pass.
Each subprocess has a 180-second timeout; none timed out today. A successful
build is an incremental Lake build, not a clean rebuild of mathlib.

Fixed a provenance bug: `verify_star_lift.py` hard-coded 2026-09-18 even on
later runs. It now records the actual Australia/Sydney date and timestamp.
Earlier dated reports and the saved full certificate are unchanged.

## Evidence map

| Claim | Evidence | Remaining limit |
| --- | --- | --- |
| 14 <= ell(12509) <= 17 | Audited Lean lower-bound and witness theorems; independent Python witness check | No optimum 17 proof |
| An 18-step star source reaches 12509 | Published list rechecked from values | No star optimum 18 proof |
| ell(2^12509-1) <= 12526 | All 12,526 index pairs replayed with exact integers; value-only star check | Neither optimality nor Scholz at 12509 |
| One Brauer block is correct | General Lean replay, endpoint, length and retention theorems | Whole-source invariant and telescoping not formalised |
| Small lift regression family passes | All 842 prefixes, <=6 additions and endpoint <=32; binary exponents 1..256 | Not an exhaustive minimum-chain search |

The local results imply

```
12522 <= 12508 + ell(12509) <= 12525.
```

The checked 12526 witness exceeds every right side allowed by these bounds.
This says nothing about whether the conjecture is false: the minimum Mersenne
length may be smaller. A future 12525 witness alone also would not close the
local proof; it needs ell(12509)>=17 or another argument relating its length
to ell(12509). A witness of at most 12522 would suffice using the existing
lower bound, but no such witness is claimed or made a search target here.
The interval calculation is elementary arithmetic from audited results, not
a new Lean theorem or a new numerical chain bound.

## Source reconciliation

Reopened [OEIS A349044](https://oeis.org/A349044), EXAMPLE, on 2026-09-20
(Australia/Sydney; live entry, no immutable revision). Both complete published
lists match the local fixtures. Independently checked all summands again.
Its parenthetical index explanation is inconsistent with its displayed list:
with zero-based indices the non-star step is **a_6=24=a_4+a_4**, following
a_5=13. Use the local list and computed parents, not the source's index gloss.
The entry's optimum/first-number claims remain literature claims here.

Read the existing pinned formal-conjectures definitions, Scholz statement and
Apache-2.0 licence; all five snapshot hashes match provenance. No upstream
update or new chain dataset was imported. The upstream open statement remains
uncompiled and unimported. No new novelty or frontier claim is made.

The failed assumption from Friday's test design remains retired: non-star
chosen parents do not imply non-star chain values. In [1,2,3,5,6], the chosen
decomposition 6=3+3 has a star alternative 6=5+1. The positive regression for
this case passed again. This is not a failed mathematical research conjecture;
there are no such failures or counterexamples to report this week.

## Verification

From the repository root:

```sh
python3 scripts/verify_integration.py --output results/2026-09-20-integration-checks.json
```

Started **2026-09-20T08:02:36.260618+10:00**, Sunday. Total **14.365812 s**.
Python **3.9.6**, standard library only; Lean **4.27.0**; existing mathlib and
transitive dependency pins unchanged. Deterministic exact arithmetic, no seed,
heuristic search or optimality enumeration. Full outputs, the 15 audited theorem
names, input hashes and commands are in `2026-09-20-integration-checks.json`.
The temporary small-check file is deleted; its complete content is embedded
in that report, so reproducing its temporary absolute pathname is unnecessary.

- 17-step witness and seven negative fixtures passed (command: 0.028508 s).
- Full 12526-step certificate passed (command: 0.074864 s), SHA-256
  `23579925c4d136e24311c57f7ccc33ef8873ae96463d815b0e386821d6f4bf1b`.
- All 842 star prefixes, binary exponents 1..256, independent all-parent checks
  for binary exponents 1..16, and 23 negative fixtures passed (0.218729 s).
  Prefix digest remains
  `0fa36c67173ea9136775ee1f10541a40226ac48297eed56db61ca0a25c73168d`.
- `lake build`: **749 jobs**, **5.411261 s**; axiom audit: **7.704705 s**.
  All 15 entries use only propext, Quot.sound and/or Classical.choice; the
  direct 12509 check uses no axioms. No local compiled source contains sorry,
  custom axioms or native_decide. The audit covers its named declarations,
  not every theorem in mathlib. No new Lean sources or proofs were added today.
- Exercised `check_axioms` with missing and wrong theorem names, sorryAx and
  a custom axiom: all four rejected; empty dependencies and the three standard
  axioms both accepted. Existing-output refusal was checked without changing
  the saved report.

## Next

Monday: retrieve Hansen's original definition and construction; specify and
check its stored-value requirements before attempting the 12525 certificate.
Tuesday: compose the proved Brauer blocks, maintain all earlier Mersenne
endpoints, and telescope n-1+r, including the singleton source. Optimality
evidence remains a separate obligation; larger non-Hansen cases stay deferred.
