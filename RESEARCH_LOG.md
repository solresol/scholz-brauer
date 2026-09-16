# Research log

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
