# 2026-09-19 — Saturday — Lean Brauer block

## Verified increment

`lean/ScholzBrauer/BrauerBlock.lean` constructs explicit summand-value
certificates and proves them correct through the existing replay checker.
For any valid addition chain `c` ending at `M_a = 2^a-1` and containing
`M_b = 2^b-1`, `brauerBlock a b` successfully extends it to a valid chain `d`
with:

- endpoint `M_(a+b)`;
- exactly `b+1` new entries (and therefore additions);
- every old value still present.

The certificate consists of `b` doublings followed by adding the stored `M_b`.
Its endpoint identity is proved with exact natural-number arithmetic, including
the subtraction boundaries. No independent positivity assumption is needed:
valid chain membership implies `M_b >= 1`, excluding `b=0` automatically.
The doubling lemma also handles zero doublings. `replayFrom_append` proves
composition of arbitrary partial replays, including failure propagation.
If `c` has `r` additions, `brauerBlock_upper_bound` proves
`additionChainLength (2^(a+b)-1) <= r+b+1`.

These are kernel-checked proofs for arbitrary parameters satisfying the stated
hypotheses, not a finite search or a conjecture assumption. Five `decide`
examples check zero doublings; the blocks `1 -> 2` and `2 -> 3`; rejection when
`M_b` is absent; and rejection of the zero stored value. The second valid block
uses a stored value different from the current endpoint.

## Scope and remaining gap

This increment proves one block. It does not yet define a general star-source
predicate, maintain stored Mersenne endpoints across a whole source chain,
or telescope the total length to `n-1+r`. It proves the resulting block is an
addition chain; no separate Lean star-chain predicate has been introduced.
The Lean certificate uses summand values, while the Python format uses indices;
no equivalence theorem between these generators is claimed.

There is no new bound or optimality result at 12509. The old 17-addition
witness for 12509 and 12526-addition witness for `2^12509-1` still check.
Neither establishes optimality, the 12525 Hansen target, or the Scholz bound
at 12509. No novelty, current-frontier or counterexample claim is made.

## Sources and dependencies

Read the existing upstream addition-chain implementation, Scholz statement,
Apache-2.0 licence and provenance. Reopened the two pinned primary source files
on 2026-09-19 (Australia/Sydney):

- [AdditionChain.lean](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/NumberTheory/AdditionChain.lean).
- [ScholzConjecture.lean](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/Wikipedia/ScholzConjecture.lean).

Version: formal-conjectures commit `40e7c98697de6f66b8cbdbf641749ab39ed9c152`.
All five vendored snapshot hashes still match `provenance.json`. Reused the
adapted `IsAdditionChain`, `additionChainLength`, endpoint positivity and upper
bound API, and the local `append_sum`/replay proofs. The upstream open theorem
remains uncompiled and unimported. The construction follows the Brauer source
already rechecked on 2026-09-18; no new published chain data was imported today.

Pins unchanged: Lean 4.27.0, mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`, and the existing dependency manifest.
Python 3.9.6, standard library only. Deterministic proofs and certificate checks;
no seed, exhaustive optimality search, heuristic or timeout.

## Commands and evidence

From `lean/`:

```sh
/usr/bin/time -p lake build
/usr/bin/time -p lake env lean Audit.lean
lake env lean --version
```

Final build passed **749 jobs in 11.97 seconds**. Axiom audit passed in
**11.44 seconds**. New constructive theorems depend only on `propext` and
`Quot.sound` (the length lemma uses only `propext`); the infimum upper-bound
corollary also uses `Classical.choice`. No local compiled source contains
`sorry`, a custom axiom or `native_decide`. Raw outputs are in
`2026-09-19-lean-build.txt` and `2026-09-19-lean-axioms.txt`.

During development an initial path probe and one Lean invocation used the wrong
working directory and failed before checking the intended source. Subsequent
commands used `lean/` and the pinned toolchain. Early proof checks found two
elaboration issues for conditional hypotheses and a distributivity normalisation
mismatch; these were fixed before the successful build. No mathematical
hypothesis was abandoned or weakened to repair these errors.

From the repository root:

```sh
python3 scripts/check_12509.py
python3 scripts/check_certificate.py results/2026-09-18-12509-star-certificate.json --exponent 12509 --additions 12526 --require-star
```

Both passed, including the former's seven negative fixtures and the latter's
independent value-only star check. Command wall times were 0.034337 and
0.087833 seconds. Exact results are in `2026-09-19-regression-checks.json`.
The full index certificate retains SHA-256
`23579925c4d136e24311c57f7ccc33ef8873ae96463d815b0e386821d6f4bf1b`.
Python code and certificates were unchanged, so the broader bounded enumeration
was not repeated today.

## Next

Sunday: integrate the week's evidence and rerun the small checks. Next Lean
increment: define star-source certificates, compose these blocks while retaining
every source Mersenne value, telescope the length, and instantiate at the
18-step 12509 source. Next computational increment: retrieve Hansen's primary
construction and seek the independently checkable 12525-step certificate.
