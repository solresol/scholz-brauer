# 2026-09-28 — Monday — bounded Hansen certificate export

Australia/Sydney. A computational interface increment toward the general
Hansen lift, with two finite kernel-checked replay witnesses. No new optimum,
conjecture counterexample, literature frontier or mathematical novelty is claimed.

## Construction and mathematical boundary

`scripts/export_lean_certificate.py` accepts an index certificate and explicit
exponent/addition expectations. It enforces exponent 1–64 and addition count
0–128 before integer replay, checks every earlier index and strict increase
using the independent checker, and translates each pair to summand values.
It emits numerical Lean literals, replay/count/validity theorems and an upper
bound using the existing `certificate_upper_bound`. A restricted fixture name
prevents emitted Lean commands from being supplied through the name field.
Source-chain provenance is not used to justify a witness. Existing output
files are refused. Export success alone is not a Lean build or proof.

The saved module `lean/ScholzBrauer/HansenReplayFixtures.lean` contains:

- source `[1]`: zero additions, endpoint 1;
- source `[1,2,4,8,9,12,17,29]`, marks at indices `[0,1,2,3,6,7]`:
  28 shifts plus seven source additions, endpoint `2^29-1 = 536870911`.

The latter interleaves `[510,511,1020]` and `[4080,4095,8160]`: unshifted
Mersenne values for 9 and 12 occur within the doubling family based on 255.
This exercises the ordering absent from sequential whole-star blocks. All
35 emitted pairs are checked by Lean's existing replay, giving the formal
numerical upper bound `ell(2^29-1) <= 35`. This does not assert source optimum,
Mersenne optimum, general generator correctness or arbitrary index/value
format equivalence. Only these two fixtures were compiled in Lean; the full
small family below was checked in Python.

The 12509 conclusions are unchanged and freshly rechecked: computationally
`ell(12509)=17` and `ell(2^12509-1)<=12525` establish Scholz at 12509.
Lean still proves source interval `[14,17]` and Mersenne bound 12526. Its
Hansen allocation budget 12525 is not yet a successful general lift replay.

## Primary sources and reused definitions

Accessed **28 September 2026**, using web open:

- [Clift's Scholz–Brauer exposition](https://www.additionchains.com/ScholzBrauer.html):
  rechecked the 29 source, underlining and labelled-edge construction. The page
  computes 28 doublings for this marking; its separate non-Hansen 29 source
  `[1,2,4,8,9,13,16,29]` is not used as an accepted Hansen fixture.
- [OEIS A349044](https://oeis.org/A349044): rechecked existing 17-step ordinary
  and 18-step star witnesses; Clift's separate 17-step 12509 witness also matches.

These are live pages without immutable revisions; metadata is retained in
`data/2026-09-28-hansen-export-sources.json`. Hansen's original article was not
inspected. No larger dataset or optimality table was imported.

Reinspected the vendored formal-conjectures definitions, Scholz statement and
Apache-2.0 provenance at revision `40e7c98697de6f66b8cbdbf641749ab39ed9c152`.
The generated module uses the already adapted `IsAdditionChain` and
`additionChainLength` via the proved certificate API. The upstream open Scholz
statement stays outside the compiled library. Dependency pins are unchanged.

## Reproduction and evidence

```sh
python3 scripts/verify_lean_export.py --output results/export-local.json --emit-fixtures results/export-local.lean
python3 scripts/verify_integration.py --output results/integration-local.json
```

Use fresh output paths. For a single index certificate:

```sh
python3 scripts/export_lean_certificate.py INPUT.json OUTPUT.lean --name example29 --exponent 29 --additions 35
cd lean
lake env lean /absolute/path/to/OUTPUT.lean
```

Python **3.9.6**, standard library, exact integers, no seed. The export verifier
enumerates all 1051 increasing source chains with at most six additions and
endpoint at most 32, checks 30582 marking masks using the independent oracle,
and exports all 5248 accepted underlinings. A separate readback parses the
emitted numerals and checks summand membership, strict growth, endpoint, count
and the numerical theorem statement without using summand indices. This is
exhaustive only within the specified finite test family, not an optimal-chain
search or proof of the general format conversion. The emitted-family SHA-256 is
`4df72ab94bfcdc74f7cf4a1521a4d057dfbd3cd3234b04c00710a14ffed49a4b`.

All 28 negative checks pass, covering unavailable, negative and malformed
indices, wrong declarations/counts, corrupted output, unsafe names and caps
(including refusing the 12509/12525 request). Removing source provenance leaves
the export unchanged. Tests pass normally and under Python `-O`.

`results/2026-09-28-integration-checks.json` records a **43.108120 s** complete
run, starting **08:05:10 AEST**, all 44 input hashes and exact command outputs:

- both exhaustive <=16-step 12509 exclusions: 1345873 visited prefixes each;
- independent portable exclusion replay and standalone 12525-step Hansen replay;
- existing star, Hansen, search, checkpoint and composition checks;
- all 753 Lean build jobs, **0.989526 s** with the new module already built;
- **62** named theorem axiom audit, **4.577134 s**, only standard axioms;
- Lean **4.27.0**, pinned mathlib/transitive inputs and all five vendor hashes.

The initial pinned build compiled the new fixture module in 9.6 s. A separate
CLI export of the 29 fixture compiled successfully in **10.996370 s**. Reusing
its output path failed and preserved its bytes. Deliberately changing the first
emitted pair from `(1,1)` to unavailable `(1,2)` caused Lean `decide` to reject
the replay as false, in **1.997486 s**. This checks the independent kernel
boundary, including a defect after Python validation. Commands and errors are
in `results/2026-09-28-export-cli-checks.json`; temporary inputs were removed.
The standalone small-family result is in `results/2026-09-28-lean-export-checks.json`.

One preliminary `lake build` was mistakenly launched from the repository root,
which has no toolchain pin; elan started fetching/installing its default 4.34.1.
That process was terminated (exit 143), with no claimed build result. All
successful builds and audits above ran from `lean/` under the verified 4.27.0
pin. Compiled local sources contain no sorry, admit, custom axiom, unsafe or
native_decide; the intentionally corrupted fixture failed as expected.

## Next informative work

Tuesday: prove shifted-node injectivity for positive source exponents using
unique odd parts, then summand availability and sorted replay. The exporter
and finite fixtures are complete; do not count them as the general lift.
Portable exclusion soundness and the small 7/3 kernel instance remain separate
work. Larger non-Hansen cases stay deferred until the lift infrastructure is ready.
