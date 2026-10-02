# 3 October 2026 — formal lower bound 16 for 12509

Saturday, Australia/Sydney. Active milestone: the end-to-end Lean Scholz
instance at 12509. Milestone 1 was already complete and was not reopened.

## Mathematical result

`ScholzBrauer.sixteen_le_length12509` proves

```
16 ≤ additionChainLength 12509
```

Together with the existing 17-addition witness, the formal source interval is
now **[16,17]**, improved from [14,17]. This is a substantive closed exclusion
obligation: every increasing addition chain with at most 15 additions is ruled
out. It includes arbitrary earlier summands, not just star chains.

It does **not** prove the optimum 17. The existing Hansen theorem still proves
`ell(2^12509-1) ≤ 12525`; the formal right side `12508 + ell(12509)` lies in
[12524,12525], so the end-to-end Scholz instance remains incomplete. The saved
16-addition exclusion and the optimum 17 remain computational evidence.
No Mersenne optimum, general conjecture, novelty or literature frontier is claimed.

## Proof and the capability that was missing

Yesterday's large typed-literal declaration could not even finish preparation
within its bound. Today's reification emits constructor expressions directly,
then the kernel type-checks them. Bounded array chunks prepared successfully;
monolithic evaluation encountered stack and memory failures. Lean's array
representation is list-backed in kernel reduction, motivating balanced lookup.
The exact causes of each low-level stack failure were not separately instrumented.

`checkExclusionWith` generalises only the node lookup interface. Its proved
soundness accepts *any* `Nat → ExclusionNode`; the old array interface remains an
abbreviation. Boolean `List.all`/`List.any` checks replace bounded propositional
decision procedures. Soundness is reproved for these exact definitions; no
unproved equivalence to the former checker or Python is assumed.

`ExclusionTree.lean` contains balanced lookup and a data-only elaborator. It emits
constructor expressions, not proofs or checker acceptance. JSON is embedded in
the generated Lean source, avoiding an untracked runtime file dependency.
Ordering or array/tree equivalence is unnecessary for the soundness theorem.

The remaining evaluation blocker was memory for a monolithic proof. The new
`checkExclusionWith_split` theorem composes local coverage with already checked
children. Each child retains its full actual prefix. The exporter caches only
syntactic subtree sizes; it never caches exclusion truth by node ID.

`Exclusion12509Lower.lean` contains 403 context-specific declarations. Leaf
fragments check at most 100 rule occurrences with `decide +kernel`; parent
fragments prove local coverage and invoke the composition theorem. Sequential
elaboration (`Elab.async false`) bounds queued proof state. The final acceptance
and lower-bound theorems are included in the normal library and transitive axiom
audit. No native evaluator, assumed target or custom axiom proves acceptance.

## Exact inputs and reproduction

The unchanged exact generator was run for target 12509, limits 14 and 15, with
its default 2,000,000-prefix budget. No randomness or seed. It reported 14 and
7544 visited prefixes respectively, in 0.000094 and 0.069295 seconds. The 14-step
certificate was an intermediate successful probe; the stronger 15-step result is
retained in the library.

The retained certificate is `results/2026-10-03-12509-limit15-exclusion.json`:
475 shared nodes, 7544 contextual rule occurrences (5731 splits, 1813 gaps),
root 474. SHA256:
`1342d0804442d7645d56e56d4a2a05e9cc2007555d3357191a135a512443415e`.
The independent existing checker checks every occurrence and all possible
summand pairs. The JSON is transport data; Lean acceptance is separately proved.

From the repository root:

```sh
python3 scripts/exclusion_certificate.py 12509 15 --output /tmp/12509-15.json
python3 scripts/check_exclusion.py results/2026-10-03-12509-limit15-exclusion.json --target 12509 --max-steps 15
python3 scripts/export_lean_exclusion.py --output /tmp/Exclusion12509Lower.lean
```

Use fresh output paths. Compare the emitted Lean file with the committed fixture.
From `lean/`, run `lake build` and `lake env lean Audit.lean`. The normal
`scripts/verify_integration.py --output <fresh-path>` includes independent replay,
exact regeneration comparison, build, pinned dependency checks and axiom audit.

Pins are unchanged: Lean 4.27.0, mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`, adapted formal-conjectures
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`. Python 3.9.6, standard library,
exact integers. Reinspected the upstream definition, statement and Apache-2.0
licence. The upstream open target remains outside the compiled library. No new
published chain data or current-literature claim was used; the existing source
witness is independently rechecked by integration.

## Failed approaches and resource evidence

`2026-10-03-exclusion-evaluation-probes.json` records commands, timestamps,
resource bounds, outputs and timings. Probes used one Lean worker per process,
a 2048 MB Lean allocation limit, recursion depth 65536 and 2,000,000 heartbeats.
Some exploratory processes overlapped (at most three); timings are not controlled
performance comparisons. Wall-clock limits were 45–180 seconds. Final compiled
source is the authoritative result.

- One directly reified list of 29,437 nodes overflowed the stack. Chunking
  avoided that preparation failure. Suppressing data code generation reduced
  preparation to 19.23 seconds in its recorded run.
- Reified full arrays still overflowed during monolithic checking (50.20 seconds
  without data code generation; 110.29 seconds with it).
- The old propositional checker with balanced lookup timed out at 180 seconds
  for limit 16 and 120 seconds for limit 15.
- Boolean checks alone did not solve memory use. The limit-15 monolithic probe
  failed at the 2 GB allocation bound. A data-only balanced-table probe passed
  in 6.62 seconds and an isolated subtree passed in 2.61 seconds.
- Asynchronously elaborating 403 fragments failed with excessive memory.
  Sequential elaboration completed the same composition in **131.44 seconds**.
- An explicit `Nat.rec` variant still failed a monolithic check with kernel
  excessive memory at 107.92 seconds. Its error-recovery output mentioned
  `sorryAx`; that failed declaration was not accepted or retained. The variant
  was discarded. The final proof uses the verified sequential composition.
- A development `simp` unfolded recursive checker equations repeatedly. Replacing
  that step with one `rw` fixed the composition lemma; no increased proof limit
  was used to hide the issue.

## Final validation and next obligation

The final normal build passed all 759 jobs in **136.47 seconds**; the new
lower-bound module took about 128 seconds. The final integration passed in **50.726068 seconds**, including 111 audited
theorems, 61 input hashes, five vendor hashes, exact source regeneration and all
existing independent checks. Only standard axioms occur (`propext`, `Quot.sound`,
`Classical.choice`); no `sorryAx`, custom axiom or native acceptance oracle.
Results are recorded in `2026-10-03-integration-checks.json`.

Next exclude every chain through **16** additions using the existing 29,437-node
DAG, then prove `ell(12509)=17` and combine it with the Hansen theorem. The full
DAG has 1,345,873 contextual occurrences, versus 7544 in today's proof. A blind
whole-DAG expansion is not justified by the smaller result's runtime. Profile a
representative bounded slice, reduce repeated local coverage work, and partition
compilation if needed. Never share proof truth across different prefix contexts.
Milestone 3 remains deferred.
