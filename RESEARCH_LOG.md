# Research log

## 2026-09-21 — Monday — Hansen certificate improves 12509 bound

Australia/Sydney, approximately 08:01–08:09 AEST. Read automation memory,
README, TODO, recent evidence/log and actual Python/Lean sources. No applicable
on-disk AGENTS.md; followed supplied instructions. Clean main, correct origin,
no competing process or run lock; acquired the exclusive `.git` lock, fetched
and fast-forward-only merged (already up to date at 13cd889).

**Increment.** Retrieved Clift's primary exposition of Hansen underlining and
edge labelling. Implemented a complete detector over source values and a lift
that explicitly stores all required shifted Mersenne values, then sorts them
into an ordinary summand-index certificate. Re-fetched and matched both the
OEIS and Clift 17-step lists for 12509. Both yield **12,525 additions**; saved
the full OEIS-based certificate. Extended the integrated verifier and updated
the roadmap. Hansen's original article scan remained inaccessible; no claim
to have inspected its proof. Full construction, source details and limits:
`results/2026-09-21-hansen-lift.md`.

**Checks.** Exhaustive small family: 1,051 sources (<=6 steps, endpoint<=32),
30,582 masks, all 5,248 accepted markings lifted and independently checked.
DP matched the brute-force oracle; 842 all-marked star lifts matched the old
generator. Seven sources had no underlining, which says nothing about their
endpoint's optimal-chain classification. Two known structural examples at 29,
21 negative checks, both 12509 witnesses and exact stored-certificate replay
passed. Standalone verifier: 1.864757s. Integration: 16.384824s, including the
previous checks, pinned Lean build (749 jobs), 15-theorem axiom audit and five
vendor hashes. No Lean changes or new formal theorem. Both new CLIs refused
existing output without changing bytes. Complete input hashes and command
outputs are saved in the dated JSON reports.

**Conclusion and limits.** Improved checked numerical bound:
`ell(2^12509-1) <= 12525`. Still no local proof of `ell(12509)=17` or of the
Scholz bound at 12509: the locally bounded RHS is [12522,12525]. No novelty,
minimum Mersenne length, non-Hansen number or conjecture counterexample claim.
No failed new hypothesis; structural regressions confirm documented examples.

**Next.** Tuesday: whole-star Lean induction and length telescoping. Next
computational day: auditable optimality evidence for 12509, with bounded
exclusion searches only if needed. Hansen formalisation follows the star
proof; larger cases remain deferred. Complete diff reviewed before commit.

## 2026-09-20 — Sunday — integrate evidence and tighten claim limits

Australia/Sydney, approximately 08:00–08:06 AEST. Read prior automation memory,
README, TODO, dated results/log and actual Python/Lean sources, upstream
definition/statement snapshots and licence. No applicable on-disk AGENTS.md;
followed the supplied instructions. Clean main, correct solresol origin, no
competing process or lock. Fetch and ff-only merge were already up to date at
1678d95; acquired `.git/scholz-brauer-research.lock` before editing.

**Increment.** Added one reproducible integration command with input hashes,
five vendored hash checks, three Python checks, pinned Lean build/version and
15-theorem axiom audit. It rejects missing/unapproved axiom entries and refuses
existing report paths. Fixed the small verifier's hard-coded 18 September date.
Reconciled the README and roadmap against current evidence; dated historical
reports and the complete Mersenne certificate were preserved.

**Checks.** Integration passed in 14.365812 seconds: 842 bounded star prefixes,
binary exponents 1..256, seven witness negatives and 23 lift negatives, exact
12526-pair replay and value-only star check; Lean build passed 749 jobs in
5.411261 seconds and the axiom audit in 7.704705 seconds. Python 3.9.6 and
Lean 4.27.0; dependency pins unchanged. Four bad audit fixtures rejected, two
valid audit fixtures accepted; existing-output refusal preserved report bytes.
No source inputs changed during integration. Reopened OEIS A349044 and matched
both published lists, noting its erroneous non-star-step index gloss. See
`results/2026-09-20-integration.md` and the accompanying full JSON evidence.

**Conclusion and limits.** No new chain bound or Lean theorem. Locally,
12508+ell(12509) is in [12522,12525]. Even the planned 12525 witness needs
ell(12509)>=17 or another sufficient argument before it proves Scholz at 12509.
The current 12526 witness does not decide that inequality. Explicitly retained
Friday's rejected test-design assumption about chosen parents versus alternative
star decompositions; no failed research conjecture or counterexample occurred.
Hansen classification, optimality and the whole-star Lean lift remain open
tasks here, with no claim about the current literature frontier.

**Next.** Monday: primary Hansen construction and checked stored-value
requirements. Tuesday: compose blocks and prove the whole-star invariant and
telescoping length. Reviewed the full source, report and documentation diff
before committing; no larger non-Hansen work scheduled yet.

## 2026-09-19 — Saturday — Lean certificate for one Brauer block

Australia/Sydney, approximately 08:01–08:07 AEST. Read the automation memory,
README, TODO, prior logs/results, Lean/Python sources and vendored upstream
implementation, statement and licence. No on-disk AGENTS.md was found; followed
the supplied instructions. Verified clean `main`, correct solresol origin and
no competing research process, acquired the exclusive `.git` run lock, fetched
origin and fast-forward-only merged (already up to date at `df17939`).

**Increment.** Added `BrauerBlock.lean`: executable doubling certificates,
replay composition, and a conditional constructive block theorem. From a valid
chain ending at `2^a-1` and containing `2^b-1`, it proves successful replay to
`2^(a+b)-1`, exactly `b+1` new additions, and retention of all old values.
The corresponding numerical upper-bound corollary is also proved. Reused the
upstream addition-chain API and local certificate proofs. Toolchain and
dependency pins are unchanged; extended `Audit.lean` to cover the new theorems.

**Verification.** Final `lake build`: 749 jobs, 11.97 seconds. Axiom audit:
11.44 seconds; only standard Lean axioms, with no `sorry`, custom axiom,
`native_decide`, or assumed Scholz statement. Five kernel-evaluated examples
cover successful, empty-doubling and rejected blocks. Reran the two independent
Python checks for the 17-step 12509 witness and the stored 12526-step Mersenne
certificate; both passed, including seven invalid fixtures and value-only star
validation. Rechecked all upstream snapshot hashes and reopened the pinned
primary source definitions and statement. Development path/elaboration errors
and final evidence are recorded in `results/2026-09-19-brauer-block.md`.

**Conclusion and limits.** One general Brauer block is now formalised. Whole
star-chain induction, its telescoping length, and the formal 12509 Mersenne
instance remain unproved. No equivalence between Python index certificates and
Lean summand-value certificates, new 12509 bound, optimality, Hansen result,
counterexample or novelty is claimed. No failed mathematical hypothesis arose.

**Next.** Sunday integration; then compose blocks over checked star-source
steps and prove the `n-1+r` total. Hansen primary-source retrieval and the
12525 certificate remain the next computational target. Reviewed the complete
staged source, evidence and documentation diff before committing.

## 2026-09-18 — Friday — explicit star/Brauer lift certificate

Australia/Sydney, approximately 11:05–11:15 AEST. Read the prior run memory,
README, TODO, research log, dated evidence and actual Python/Lean sources.
No applicable on-disk AGENTS.md was found; followed the supplied instructions.
Verified origin `git@github.com:solresol/scholz-brauer.git` and clean `main` at
`9208036`. Fetch and fast-forward-only merge reported already up to date.
No competing research process or run lock was found; acquired a temporary
exclusive lock in `.git` before editing.

**Increment.** Added a star-chain Mersenne lift generator and a separate generic
summand-index replay checker, plus a value-only star checker and deterministic
bounded verifier. Rechecked the OEIS 18-step star witness for 12509 and Brauer's
original 1939 construction. Saved the complete 12,526-pair certificate and
source fixture. The generator accepts `[1]` and rejects non-star input before
emitting pairs. See `results/2026-09-18-star-lift.md` for the construction,
source URLs/access dates, certificate format, commands and SHA-256.

**Checks.** Python 3.9.6, standard library only, exact integers, no random seed.
`python3 scripts/verify_star_lift.py --output results/2026-09-18-star-lift-checks.json`
passed in 0.318886 seconds: all 842 star prefixes with at most six steps and
endpoint at most 32; binary lifts for 1..256; the saved 12509 certificate;
23 negative checks. Standalone certificate replay and value-only checking
verified exactly 12,526 additions and endpoint `2^12509-1`. Reran the existing
`python3 scripts/check_12509.py`; the 17-step witness and seven negative checks
passed. No Lean files changed and no Lean build was run today.

The first verifier run caught an incorrect negative fixture: a chosen non-star
summand pair can have a star alternative (`6=3+3=5+1`). Corrected the fixture
and retained the alternative-decomposition case as a positive regression.
No failed mathematical hypothesis or conjecture counterexample was found.

**Conclusion and limits.** Checked witness: `ell(2^12509-1) <= 12526`.
This is neither an optimum nor the Scholz bound for 12509. The length-12525
target and Hansen construction remain work to do. Enumeration was exhaustive
only within the stated star-prefix test family, not an optimality search.
No novelty or current-frontier claim is made. Direct retrieval of Clift's
page failed again; search-index text was not used to certify larger cases.

**Next.** Saturday: prove the doubling-block endpoint and length in Lean,
using `append_sum`. Next computational step: retrieve Hansen's primary
construction and attempt the 12525 certificate. Reviewed the full code/document
diff and replayed every pair of the generated certificate before committing.

## 2026-09-17 — Thursday — Lean certificate foundation

Started about 08:01 AEST (Australia/Sydney). This is the first daily run.
Origin was verified as `git@github.com:solresol/scholz-brauer.git`; the checkout
was clean on `main` at `e062e09`. `git fetch origin` followed by
`git merge --ff-only origin/main` reported already up to date. No competing
research/Lean process or run lock was present. A temporary lock in `.git`
protected this run.

**Reconciliation.** Only README.md existed. No advertised `src/`, experiments,
results, tests or Lean code existed. Corrected the README's claim that a checked
Brauer lift already existed, and separated literature leads from local results.

**Increment.** Adapted the inspected Apache-2.0 formal-conjectures addition-chain
API at a pinned commit. Added executable summand-pair replay and proved append
correctness, replay correctness, exact step count and the induced upper bound
on minimum chain length. Added the published 12509 witness, direct kernel
validation independent of replay, and a Python check which reconstructs all
possible parent pairs from the list. Pinned Lean, mathlib and the dependency
manifest. Source provenance and licence files are retained.

**Checks and evidence.**

- `cd lean && lake update`, then `lake update mathlib` after replacing the tag
  with its resolved commit, installed the locked dependencies using the cache.
  An initial `lake update` in the repository root lacked a Lake configuration
  and failed; elan selected/downloaded 4.34.0 there. All project builds use the
  explicit `lean/lean-toolchain` pin to **4.27.0**, not that default toolchain.
- The first actual build exposed the upstream Nat lattice module rename;
  adapting its import to the 4.27.0 path fixed it. The first successful build
  took 40.99 seconds. The final build after the attribution comment change,
  `/usr/bin/time -p lake build`, passed all 748 jobs in **16.07 seconds**;
  output is in `results/2026-09-17-lean-build.txt`.
- `lake env lean Audit.lean` passed. Key theorems use only standard Lean
  axioms (`propext`, `Quot.sound`, and for infimum-based bounds,
  `Classical.choice`). The direct 12509 predicate check has no axioms.
  See `results/2026-09-17-lean-axioms.txt`. No compiled local proof contains
  `sorry`, a custom axiom, `native_decide`, or an assumed target conjecture.
  The upstream open statement is stored outside the compiled library.
- `python3 scripts/check_12509.py` (Python **3.9.6**) passed for the one
  18-entry chain and seven invalid fixtures. It reports 17 additions and the
  sole non-star step at index 6, `24=12+12`, immediately after 13. Exact output,
  parent indices and measured sub-millisecond runtime are in
  `results/2026-09-17-python-check.json`. This is deterministic checking, not
  exhaustive chain search; no random seed was used.
- Rechecked all five upstream snapshot hashes and compared the complete
  adapted source against the original after the documented compatibility
  transformations. Reviewed the complete staged diff and ran
  `git diff --cached --check` before committing.

**Conclusion and limits.** Formally proved `14 ≤ ℓ(12509) ≤ 17`. The replay
method works for general strictly increasing certificates, including non-star
steps. This does not prove the optimum 17, any Hansen classification, or the
Scholz bound for 12509. No chain for `2^12509-1` was generated. No new
counterexample or novel mathematical theorem is claimed.

**Next.** Build an explicit star/Brauer Mersenne lift with independent checks,
then formalise its endpoint and step count. Retrieve the primary Hansen
construction before attempting the missing step for 12509. See TODO.md.
