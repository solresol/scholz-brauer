# Exclusion soundness and the first kernel-checked lower bound

2 October 2026, Friday, Australia/Sydney. Milestone 1 was already complete;
this run advances milestone 2. It closes general exclusion soundness and the
required small instance. It does **not** prove the 12509 lower bound in Lean.

## Mathematical result

`lean/ScholzBrauer/Exclusion.lean` proves the following obligations:

- `ChainReach` represents at most r increasing additions from a prefix. A
  stopped chain remains reachable with unused budget. Its proved monotonicity,
  endpoint ordering and extension doubling bound cover the pruning rules.
- `additionChain_reaches` reuses the existing theorem that every upstream
  addition chain admits summand-value replay. The separate
  `additionChain_extension_reaches` proves completeness for arbitrary valid
  prefixes directly: positivity makes both summands smaller than their sum,
  and strict ordering places them in the preceding prefix.
- `checkExclusion_sound` proves acceptance implies non-reachability, by induction
  on the remaining budget. A bound leaf contradicts extension doubling; a gap
  leaf excludes the last sum; a split covers every necessary next value and
  checks every supplied child in its actual context.
- `checkExclusion_excludes_extension` states the result using the upstream
  predicate: no suffix of at most r entries can extend an accepted prefix to n.
  `checkExclusion_lower_bound` transports root acceptance to `r < ell(n)` using
  `Nat.sInf_mem` and a known witness for nonemptiness.
- `exclusionSeven_checked` evaluates the entire three-node certificate for 7
  at limit 3 with kernel `decide`. `length_seven_eq_four` combines it with the
  witness `[1,2,3,4,7]`, proving **ell(7)=4**.

The small DAG is exactly `[gap, split[(4,0)], split[(2,1)]]`, root 2. The existing
Python generator and independent checker agree. At prefix `[1,2]`, the omitted
choice 3 cannot reach 7 with one doubling; the retained choice 4 has no final
summand pair for 7. This is a completed lower-bound proof, not merely replay
of a short witness.

The Lean checker consumes the existing bound/gap/split syntax. It relaxes two
unnecessary format restrictions: extra child edges are allowed (and checked),
and references need not point backwards because the step budget decreases.
Invalid references reject. It does not assert equivalence with the stricter
Python parser/checker. No conclusion is cached by node identity. Eight concrete
kernel checks exercise the rule boundaries, including the gap node accepted at
`[1,2,3,4,8]` but rejected at `[1,2,3,5,10]` for target 15.

## Large-certificate experiment and precise remaining obstacle

The saved 12509 JSON is unchanged, SHA-256
`516a54800a296da300cc15da318c40b06b08a18270c93b8467f3f843a8b074e9`.
It has 29,437 nodes and 195,745 edges. The only new experimental plumbing,
`scripts/probe_lean_exclusion.py`, transports this exact, hash-pinned data into
230 typed array declarations of at most 128 nodes each. A typed Lean input was
missing; without it the new soundness theorem could not be applied to this DAG.
The probe supplies that input without creating a new certificate format or search.
It uses temporary files under this repository's `.git` and preserves reports.

Two bounded attempts were made:

1. Full raw-literal input plus `by decide`: timed out after **120.021501 s**.
   The initial version also included an informational `#eval IO.println` before
   the theorem. No output or completed theorem was returned. Its generated
   source was 2,419,904 bytes; exact hash and invocation are in
   `2026-10-02-exclusion-kernel-probe.json`.
2. Isolated declarations, with no exclusion theorem: timed out after
   **60.081456 s**. Source was 2,419,744 bytes. See
   `2026-10-02-exclusion-data-probe.json`. This establishes that even preparation
   of the raw typed table exceeds this smaller budget. It does not establish
   where the full 120-second attempt spent its time.

Both used one Lean worker, `-M 2048`, maxRecDepth 65536, and maxHeartbeats
2000000. The memory flag is Lean's allocation limit, not a measured RSS ceiling.
The final harness kills the process group on timeout. No probe processes remain.
Neither timeout is an exclusion proof or evidence that kernel evaluation is
impossible. No generated large theorem is compiled into the library.

**Next strategy:** separate and time data preparation and theorem evaluation;
replace the large surface-syntax input with directly constructed, kernel-checked
data expressions or separately compiled chunks. Then measure contextual checking
and, if needed, prove bounded subtree exclusions and compose them. Retain the
existing soundness theorem and certificate. Do not rerun the same unprofiled
raw-literal experiment with successively larger limits, or re-prove soundness.
Truth must still be checked for each prefix, regardless of shared syntax.

## Checks, dependencies and reproduction

Initial `lake build` passed with the new soundness and small-instance proofs.
After the final cyclic-reference example, full existing integration ran once:

```sh
python3 scripts/probe_lean_exclusion.py --output results/new-kernel-probe.json
python3 scripts/probe_lean_exclusion.py --data-only --timeout 60 --output results/new-data-probe.json
python3 scripts/verify_integration.py --output results/new-integration.json
```

Choose fresh output paths. The probe requires the library to have been built
from `lean/`. The final harness separates data-only and full modes; therefore
its full source omits the initial diagnostic print used by attempt 1.

`2026-10-02-integration-checks.json` records **50.340364 s**, 57 input hashes,
five vendor hashes, 757 successful Lean build jobs (4.289616 s), and 106 audited
theorems (3.530171 s). All top-level commands exited zero. Dependencies remain
Lean 4.27.0 and pinned mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`; Python 3.9.6, exact integers, no seed.
The integration's existing two exhaustive 12509 searches, portable certificate
checker and lift checks passed. These are regression evidence, not today's
research advance. The new results are the general theorems and the small optimum.

All 12 new named theorems are audited. Dependencies are only `propext`,
`Classical.choice`, and `Quot.sound`; `exclusionSeven_checked` uses only
`propext`. No `sorry`, custom axiom, `unsafe`, `native_decide`, or assumed Scholz
statement occurs in the new proof. Proof development needed ordinary elaboration
fixes (constructor parameters, explicit small-witness indices, and unfolding the
recursive checker once instead of recursive simp); no mathematical hypothesis
was refuted.

Reinspected the pinned formal-conjectures addition-chain definition, Scholz
statement and Apache-2.0 licence at
[revision 40e7c986](https://github.com/google-deepmind/formal-conjectures/tree/40e7c98697de6f66b8cbdbf641749ab39ed9c152).
The unproved upstream Scholz theorem remains an uncompiled reference. No new
published chain data, current-frontier or novelty assertion is used. Existing
source fixtures were rechecked by integration; no fresh literature retrieval
was needed for these self-contained soundness proofs.

## Claim boundary

Milestone 2's soundness and small-instance obligations are complete. Lean still
has `14 <= ell(12509) <= 17` and `ell(2^12509-1) <= 12525`. The exact source
optimum 17 and the full Scholz instance at 12509 remain computational results
until the large exclusion is kernel checked. No Mersenne optimum or universal
Scholz proof is claimed. Milestone 3 remains deferred.
