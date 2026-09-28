# Research log

## 2026-09-29 — Tuesday — positive shifted-node injectivity in Lean

Australia/Sydney, starting about 08:02 AEST. Read applicable instructions,
automation memory, roadmap/log, recent evidence and actual sources. Clean
main at 97a558a, correct origin and no competing research process or lock.
Acquired exclusive run lock; fetch/ff-only reported already current.
Reinspected upstream definitions/Scholz statement/licences and rechecked
Clift/OEIS published witnesses, keeping source metadata.

**Increment.** Added `HansenNodes.lean` with seven general theorems: odd
Mersenne remainder, unique power-of-two/odd-part decomposition, injectivity
of `(a,k) ↦ 2^k*(2^a-1)` for positive a, positivity, doubling/base-sum
identities and duplicate-free value conversion. Six examples cover essential
boundaries, the 29 interleaving windows and arbitrary shifts of the 12/13
families in the 12509 source. Reused mathlib and the existing Brauer identity;
no dependency changes or assumed conjecture. Updated integration's audited
imports and explicit claim boundaries, README and roadmap.

**Checks.** Full integration passed in 56.332228s: 754 build jobs, 69
standard-axiom theorem audits, 46 input and five vendor hashes, both
1345873-prefix exclusions, portable exclusion replay and independent Hansen
replay, all small oracles and negative checks. Lean4.27.0/Python3.9.6, exact
arithmetic, no seed. Initial proof elaboration/rewrite errors were repaired;
final source has no proof placeholders. Full diffs and evidence reviewed.
Details and commands: `results/2026-09-29-hansen-nodes-lean.md`.

**Conclusion and next.** Positive shifted values are formally collision-free.
The allocated family, summand membership and sorted replay remain to be
formalised. Computational optimum17 and Scholz at12509 are reconfirmed;
Lean source[14,17], Mersenne12526 and Hansen budget12525 are unchanged.
No novelty or counterexample claim. Wednesday: labelled allocation/dependency
certificate for29/12509; next Lean step is summand availability and sorted
replay. Exclusion soundness and larger non-Hansen work remain deferred.

## 2026-09-28 — Monday — bounded export to Lean replay fixtures

Australia/Sydney, starting about 08:01 AEST. Read applicable instructions,
automation memory, current roadmap/log, recent results and actual sources.
Clean main at 597643f, correct origin, no competing research process or run
lock. Acquired exclusive lock, fetched and fast-forward-only merged (already
current). Rechecked Clift/OEIS sources and vendored upstream definitions/licence.

**Increment.** Added bounded Python-index to Lean-value export, with independent
integer validation before output. Saved singleton and interleaving-29 fixtures;
eight named kernel-checked replay/count/validity/bound theorems give the finite
35-step bound for `2^29-1`. Independent readback checks all 5248 accepted small
underlinings (1051 sources, 30582 masks), plus 28 negative cases, normally and
under Python -O. CLI output compiled; overwriting was refused; corrupting an
emitted summand was independently rejected by Lean. General equivalence and
Hansen generator correctness are not proved by these finite examples.

**Checks.** Full integration 43.108120s: 753 build jobs, 62 standard-axiom audits,
five vendor hashes, 44 input hashes, both 1345873-prefix exhaustive exclusions,
portable proof replay and all small regressions. Exact arithmetic, no seed,
Python3.9.6, Lean4.27.0 and unchanged dependency pins. A mistaken preliminary
root-directory Lake invocation began an unpinned toolchain download/install;
it was terminated with exit143 and supplies no build evidence. Every successful
Lean check used the pinned lean/ directory. Complete diffs and evidence reviewed.
See `results/2026-09-28-hansen-export.md` for commands, timings and limitations.

**Conclusion and next.** Finite Lean Mersenne bound at29 is35; no optimum claim.
Computational ell(12509)=17 and Scholz at12509 are reconfirmed. Lean source
interval[14,17], Mersenne bound12526 and Hansen count budget12525 are unchanged.
No new counterexample, failed mathematical hypothesis or novelty claim.
Tuesday: shifted-node injectivity, then summand availability and sorted replay;
do not repeat completed fixture work. Exclusion soundness and larger cases deferred.

## 2026-09-27 — Sunday — checked composition of weekly evidence

Australia/Sydney, starting 08:02 AEST. Clean main at ea78286, correct
solresol/scholz-brauer origin, no competing research process or lock. Read
prior run memory, current instructions, source, roadmap and dated results;
fetch/ff-only was already current. Acquired the exclusive run lock.

**Increment.** Reconciled the week's computational and Lean claims in
`results/2026-09-27-weekly-integration.md`. Integration now explicitly matches
the witness, both exhaustive search statements, full search root/frontier,
portable exclusion and standalone Hansen replay before composing its numerical
conclusion. Hashes bind the Hansen replays to the saved input. Added 26 altered
and eight missing-field report cases, checked normally and under Python -O.
No previous numerical claim needed withdrawing; this closes an integration
consistency gap, not a mathematical or checker-soundness gap.

**Checks.** Full integration passed in 55.145647s: both 1345873-visit exhaustive
12509 exclusions, portable proof replay, small lift/search oracles, 752-job Lean
build, 54 standard-axiom audits and five vendor hashes. Python3.9.6,
Lean4.27.0, pinned dependencies unchanged, exact integers and no seed. All 39
input hashes match. Rechecked published chain lists on Clift/OEIS with dated
source metadata. Reviewed complete source/docs diff and structured evidence.

**Conclusion and next.** Computational ell(12509)=17 and the 12525-step
Mersenne witness still establish Scholz at 12509. Lean source bounds remain
[14,17], actual Mersenne bound 12526, Hansen allocation budget 12525. No new
bound or theorem. Retired parent-choice/value-star and shared-node-context
shortcuts explicitly; no failed mathematical hypothesis. Monday: bounded
Python-index to Lean-value replay fixtures. Tuesday: shifted-node injectivity;
then sorted replay. Exclusion soundness remains separate, larger cases deferred.

## 2026-09-26 — Saturday — Hansen shift accounting in Lean

Australia/Sydney, starting 08:02 AEST. Read automation memory, repository
instructions, current roadmap/log, source and recent evidence. Clean main at
742db0e, correct origin, no competing research process. Fetched and ff-only
merged (already current), then acquired the exclusive run lock. Rechecked
Clift's construction and published chain fixtures, retaining retrieval metadata.

**Increment.** Added executable shift demands/maxima and per-mark caps, with
eight general Lean theorems: prefix bound by next mark, maximum equal to the
marked gap, demand bounds, cap/mark alignment and telescoping to n-1. Three
12509 specialisations prove the cap list, shift sum 12508 and allocation budget
12525. Eight kernel examples cover the empty source extension, retained anchors,
Clift's 29 example and an invalid decreasing request. Updated the Hansen verifier
to compare interval maxima with all 5248 accepted small underlinings and match
the concrete Lean source/marks/caps to the saved JSON.

**Checks.** Full integration passed in 47.006420s: all 752 Lean build jobs,
54 standard-axiom theorem audits, five vendor hashes, all lift regressions,
both exhaustive <=16-step 12509 exclusions and the portable exclusion checker.
Python3.9.6; Lean4.27.0 and dependency pins unchanged; exact integers, no seed.
No forbidden proof placeholders or custom axioms in compiled sources. Final
input hashes match; full code/docs diffs and evidence inspected before commit.
See `results/2026-09-26-hansen-shift-lean.md` and the dated integration JSON.

**Limits and next.** The formal budget does not yet supply distinct lifted nodes
or sorted replay. Lean bounds remain source [14,17] and Mersenne <=12526;
computational optimum17 and Scholz at12509 are reconfirmed. No new numerical
bound, novelty or counterexample claim. Next prove shifted-node distinctness
using odd parts, then summand availability and replay. Exclusion soundness and
7/3 remain a separate next formal task; larger non-Hansen cases stay deferred.

## 2026-09-25 — Friday — portable exclusion proof object

Australia/Sydney, approximately 08:02–08:16 AEST. Read automation memory,
repository instructions, README, TODO, recent evidence/log and actual search
and Lean certificate sources. Clean main at c003e36, correct solresol origin,
no competing process or run lock. Acquired the exclusive run lock, fetched and
ff-only merged (already current). Rechecked Clift, OEIS chain lists and Knuth's
primary search source; no published minimum-length table was imported.

**Increment.** Added an exhaustive exclusion-certificate generator, independent
checker and regression suite. Saved the 12509/16 proof object: 29,437 shared
nodes, 2,464,503 bytes, covering 1,345,873 contextual occurrences. Rules are
an exact doubling bound, missing last-step summands and complete next-value
splits. Sharing syntax never bypasses checking each chain context. Documented
rule soundness and the remaining Lean interface in
`results/2026-09-25-exclusion-certificate.md`; integrated saved-proof checking.

**Checks.** All 576 small decisions match 78,758 unpruned prefixes: 374
exclusions, 202 witnesses. All 32 rejection cases, seven invalid generator
inputs, exact/insufficient budgets, no-file-on-witness/budget and overwrite
protection passed. An adversarial shared-node proof for 15 is correctly
rejected. Standalone checker checks survive Python -O. Final deterministic
regeneration matched the saved object in 12.572508s; checking took 13.591166s;
the dedicated verifier took 26.833186s. Full integration passed in 51.246500s,
including both prior 12509 exclusions, all lift regressions, five vendor hashes,
pinned Lean build and 43 standard-axiom audits. Python 3.9.6; exact integers,
no seed, unchanged Lean pins. All final input hashes matched. Reviewed full
source/document diffs and structured proof/report data before commit.

**Conclusion and limits.** The existing computational optimum 17 and Scholz
instance at 12509 now have portable exclusion evidence. No new numerical bound
or Lean theorem. Lean source bounds remain [14,17], Mersenne bound 12526.
No conjecture counterexample or novelty claim. The regression retires the
possible implementation shortcut of caching proof truth solely by shared node
id; it is not a failed mathematical hypothesis about addition chains.

**Next.** Prove the three exclusion rules and context-sensitive checker soundness
against upstream IsAdditionChain, then kernel-check 7/3 before scaling to 12509.
Saturday's Hansen shift maximum and telescoping count remain scheduled; the
underlining invariant is complete and larger non-Hansen work stays deferred.

## 2026-09-24 — Thursday — Hansen marking and anchor invariant in Lean

Australia/Sydney, approximately 08:00–08:12 AEST. Read automation memory,
supplied AGENTS instructions, README, TODO, recent logs/results and actual
source, including upstream definitions, Scholz statement and licence. No
applicable on-disk AGENTS.md. Clean main at f598388, correct solresol origin,
no competing process or lock. Acquired the exclusive run lock, fetched and
ff-only merged (already current). Rechecked Clift's criterion and both
published 17-step source lists; no original Hansen scan or larger data used.

**Increment.** Added a decidable Hansen marking checker, source replay and
length proofs, latest-marked-anchor identity, stored-mark maximum, continuation
at arbitrary source cuts and explicit final-mark theorem. Checked the 12509
marking, source replay and 17-step count in Lean. The marking and all oriented
parent indices match the saved Python certificate. Ten general and five
concrete theorems are new. See `results/2026-09-24-hansen-underlining-lean.md`.

**Checks.** Final build completed 751 jobs. Combined integration passed in
29.925100s, including 43 theorem axiom audits (standard axioms only), five
vendor hashes, all prior lift tests and both independent <=16-step exclusions.
Nine new kernel-evaluated examples cover valid and invalid markings. The
fixture match took 0.003964s. Python3.11.6; Lean4.27.0/mathlib pins unchanged;
exact arithmetic, no seed. All final source hashes and commands are retained.
Development corrected syntax/normalisation and HTML-whitespace checks; no
mathematical hypothesis failed. Reviewed the complete code/document diff and
structured evidence before commit.

**Limits and next.** Underlining is formalised; the Hansen Mersenne lift,
its shift count and source optimality are not. Lean bounds remain [14,17]
and Mersenne <=12526; computational ell(12509)=17 and Scholz at 12509 were
rechecked. Next prove each marked interval's maximum shift, then telescope
the count to n-1 and construct sorted shifted nodes. For computational work,
prepare Lean-checkable exclusion evidence. Larger non-Hansen cases stay deferred.

## 2026-09-23 — Wednesday — exact exclusion closes the 12509 gap

Australia/Sydney, starting 08:00 AEST. Read automation memory, supplied AGENTS
instructions, README, TODO, dated evidence/log and actual source. No applicable
on-disk AGENTS.md; clean main at 50a8f57, correct solresol origin, no competing
research process. Acquired the exclusive `.git` run lock; fetched and ff-only
merged (already current). Rechecked Clift's primary account and chain, Knuth's
search source, Flammenkamp's methodology/data page and OEIS's witness lists.
Direct OEIS HTTP requests failed; no inaccessible optimality table was trusted.

**Increment.** Added a bounded C++17 exhaustive value-chain search, independently
written Python decision procedure, unpruned small oracle and checkpoint tests.
Both traversals exclude **every chain of at most 16 additions for 12509**,
completing after **1,345,873 prefixes**. Combining this with the checked
17-step source and saved Hansen certificate establishes ell(12509)=17 and
`ell(2^12509-1)<=12525=12508+ell(12509)` computationally. The optimal marked
source now also establishes the Hansen-number classification locally.
See `results/2026-09-23-optimality.md` for the completeness argument and limits.

**Checks.** Standalone verification passed in 16.561875s (C++ exclusion
0.152061s; Python exclusion 12.714011s). Python 3.11.6, Apple clang 21.0.0,
standard libraries, exact integers, no seed or imported optimum. Both engines
match all 576 target/limit decisions against 78,758 unpruned prefixes. All
132 optimal chains for 29 are partitioned by checkpoint frontiers at five
caps; every pending subtree is restarted and checked. Ten invalid requests,
zero/exact-budget boundaries, a non-star searched suffix, and full Mersenne
certificate replay pass. Development corrected a test that wrongly expected
a budget stop when the eighth visited node already held an eight-entry witness.
Source hashes and exact commands/outputs are retained in the dated reports.
Full integration passed in 30.853803s, including repeated exclusions, prior
lift checks, the pinned Lean build, 28 axiom audits and five vendor hashes.
Existing-report refusal preserved bytes; all recorded source hashes match.
Final review added an explicit C++ header and a tested Python -O rejection guard;
verification was rerun on the final source bytes. Full source/document diff and
all generated command records were reviewed before commit.

**Limits and next.** This is computational exhaustion, not a new Lean theorem
or novelty claim. Lean source bounds remain [14,17]; its Mersenne bound remains
12526. The star optimum 18 is still a literature claim. No universal Scholz
proof, minimum Mersenne length or counterexample is claimed. Thursday's Hansen
underlining invariant remains next, followed by formalising exclusion evidence.
Larger non-Hansen cases remain deferred. Prior dated evidence is preserved.

## 2026-09-22 — Tuesday — whole-star constructive Lean proof

Australia/Sydney, approximately 08:00–08:09 AEST. Read automation memory,
README, TODO, recent reports/log and the actual sources, including upstream
definitions, Scholz statement and Apache-2.0 licence. No on-disk AGENTS.md;
followed supplied instructions. Clean main at c9c2c49, correct origin, no
competing process; acquired exclusive `.git` run lock, fetched and ff-only
merged (already up to date).

**Increment.** Added checked star-source increments and explicit whole-lift
certificates in `StarLift.lean`. Proved source validity, endpoint and length,
successful lift replay, stored Mersenne membership and exactly `n-1+r`
additions, including `[1]`. Proved the conditional Scholz corollary when the
source is optimal. Rechecked OEIS's 18-step 12509 list and instantiated the
general proof to obtain the formal bound `ell(2^12509-1) <= 12526`.
Expanded the axiom audit and corrected stale formalisation metadata in the
Python-only verifier. Full account: `results/2026-09-22-star-lift-lean.md`.

**Checks.** New Lean module and instance compiled (750 jobs). Final integration
passed in 12.915720 seconds: cached build 2.416202s, all 28 theorem axiom
audits 7.024810s, previous Python star/Hansen enumerations, both saved large
certificates and five vendor hashes. No `sorry`, custom axiom or `native_decide`
in compiled local sources; only standard axioms in the audit. Seven new small
examples cover the singleton, complete replay and invalid increments. Source
and increment lists match the existing JSON fixture exactly. Dependency pins
unchanged; complete command outputs and input hashes retained. Development
normalisation errors were fixed without weakening the claims. Full diff reviewed.

**Conclusion and limits.** Complete star construction is now formalised, with
a numerical Lean bound at 12509. Monday's 12525 Python Hansen bound is stronger
and still not formalised. Neither optimality nor Scholz at 12509 is established;
local source bounds remain [14,17]. No novelty, new best numerical bound,
counterexample or failed mathematical hypothesis is claimed.

**Next.** Wednesday: primary optimality data and methodology. Thursday: checked
Hansen underlining and its anchor invariant. The whole-star invariant is done;
larger non-Hansen cases remain deferred.

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
