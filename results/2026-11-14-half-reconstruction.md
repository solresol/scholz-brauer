# Prescribed sink-half reconstruction — 14 November 2026 UTC

Authorized run: 14 November, 21:00 UTC / Sunday 15 November Sydney.
Active obligation: Lean exclusion of every 108-doubling labelling of Clift's
selected 109 graph. Its exact minimum 109 remains computational.

**Thirteen new Lean theorems recover the prescribed sink-half coordinates
and bound its moment-compatible anchors by two.** This advances the missing
nineteen-weight shape classification. The full exclusion remains open; the
necessary pair domains remain 278 kernel-checked and 246 computational.

## Checked reduction

Write the actual sink exception positions as
`r=A1+p`, `s=A2+p`, `z=A3+p`, and let `H` be the exact recovered sink half.
For any coordinate tuple, the prescribed half has first moment

```
sum(sinkHalf c) = 12 A1 + 4 A2 + 3 A3 + 8 u + 6 v + 7 d2 + 5 q.
```

Consequently, after choosing the anchor `a=A3`,

```
p  = z-a
A1 = r-z+a
A2 = s-z+a
q  = (sum(H)-12r-4s+16z-19a-8u-6v-7d2) / 5.
```

The numerator is divisible by five for every actual tuple. In particular,
the first moment restricts the anchor to one residue class modulo five.
`reconstructSink_eq` and `sink_coordinates_unique` prove exact reconstruction
and uniqueness for a fixed anchor, rather than substituting arbitrary halves.
`interval_sink_reconstruction` connects this to the existing exact `halve`:
every interval tuple recovers its prescribed nineteen distinct weights,
with `A3` among them and `0 <= x`, `x+d1 < 109` for every half-weight.
`sink_reconstruction_of_budget` transports this statement to the original
natural edge labelling with its existing seed, graph, cap and endpoint hypotheses.

There is a stronger bound before testing the full prescribed shape. Once
the box roles and actual exception positions are fixed, the sink half is
`(K+a) + (P+a+q)` for fixed multisets K and P of cardinalities fourteen
and five. Let `SK=sum(K)`, `SP=sum(P)`,
`C=sum(H)-SK-SP`, and
`D=sum(x^2 for x in H)-sum(x^2 for x in K)-sum(x^2 for x in P)`.
Its first two moments imply

```
266 a^2 + (10 SK - 28 SP - 28 C) a + C^2 + 2 SP C - 5 D = 0.
```

The leading coefficient is nonzero, so any three passing anchors contain
an equal pair. `fourteen_five_moments_at_most_two` proves this generally
for integer multisets, retaining signed weights and multiplicities.
`sink_moments_at_most_two_anchors` applies it to reconstructed coordinates;
`sink_moments_of_prescribed_half` proves the test necessary for every actual
tuple. Thus each fixed reconstruction has at most two moment-compatible
anchors and each fixes at most one tuple. This bounds candidate recovery;
it does not prove completeness of the outer box/exception enumeration.

The full nineteen-weight equality must still be checked, followed by the
other interval and cap constraints. No sufficient moment test, pair removal,
`min(u,d1)=1` theorem, cap feasibility, or new Scholz instance is asserted.

## Bounded fixture check

The saved 216 interval fixtures are read, without repeating their enumeration.
For each, the existing independent least-weight halving implementation recovers
the nineteen weights from the interval minus its box and actual sink exceptions.
The new check recovers the original coordinates exactly, scans those nineteen
anchors by direct first/second moments, and compares with integer roots of
the quadratic using an exact discriminant and integer square root.

Both calculations agree for every fixture and retain **exactly one anchor
in each of the 216 fixtures**. This fixture-level uniqueness is computational;
the general Lean theorem gives at most two. All 432 controls reject the intended
corruption: changing q changes the first moment, while moving the two extreme
half-weights outwards preserves the first moment and changes the second.

Reproduce from the repository root with an unused output path:

```bash
python3 scripts/experiment_clift109_half_reconstruction.py --output /tmp/half-reconstruction.json
```

Python 3.12.14, standard library and existing project modules only, no random
seed. The 60-second bound contains 216 fixtures with nineteen scanned anchors
each. Runtime: **0.102 seconds**. The JSON records commands, dependencies,
input/source hashes, per-fixture anchors and scope. Neither this check nor
the polynomial solver certifies completeness of the saved fixtures or any
unvisited box/exception choice.

## Build, audit, sources and repository safety

The full published startup gate passes for all three projects before Lean
work. Read `/workspace/shared/theorem-provers/START.md`; no applicable AGENTS.md
is present. The clean `work` checkout, fetched `origin/main`, and live main
equal `e49500b296a35658d683b8c950dac3dd328498f8` at entry. Equal ancestry is
verified before the fast-forward-only update, which changes no source.
Origin is exactly `https://github.com/solresol/scholz-brauer.git`.
No competing research process or research marker is found; a local exclusive
marker is used. The failed 13 November launch is not counted as an increment.

The installed absolute Lean/Lake 4.27.0 binaries and
`prepare.env_for('scholz')` retain the exact toolchain/mathlib/manifest/Lake
pins, isolated archive cache, LEAN_NUM_THREADS=2, 2 GiB reserve and 12 GiB
process-group RSS guard. Both final commands use a stricter 300-second bound.
Full build: **1,177 jobs, 16.013 seconds**. Fail-closed axiom audit:
**442 entries, 27.027 seconds**, including all thirteen new theorems and their
transitive dependencies. Only propext, Quot.sound and Classical.choice occur.
No placeholder, project axiom, native acceptance or target assumption is added.
The only final warning is the pre-existing generated unused-simp warning.
An optional tactic import lacked a cached object during a direct probe; it
was removed and the algebra proved with the already available ring tactic.
No dependency installation, pin update or shared-environment repair occurs.

The current 13 November weekly handoff is read and is one UTC day old;
its HAL and publisher access limits remain. No outside theorem is used or
broad literature search repeated. Clift's [primary account](https://www.additionchains.com/ScholzBrauer.html)
and [selected diagram](https://www.additionchains.com/LargeNonHansen.png)
are accessed 14 November UTC. Their hashes match previous access. The diagram
is visually rechecked, all eleven selected parent sums check, and all sixteen
published 5,784,689 chains match the archived ordered lists and pass fresh
increasing-chain/27-addition witness checks. No published optimality or
exclusion result is assumed. URLs, access timestamp, content versions and
hashes are recorded in `data/2026-11-14-half-reconstruction-sources.json`.

Build/audit logs and the verification JSON are saved beside this report.
Only the authorized checkout changes; published environment, sibling sources,
configuration, credentials and schedules are unchanged. No whole-integration
or remote-CI result is claimed.

## Next obligation

Use the at-most-two moment-compatible anchors and exact q recovery in a
sound finite interval classifier. Retain the full prescribed sink/source
halves, common box, actual exceptions, 278-pair kernel domain, both odd-run
restrictions, twelve critical families, 64 orientations and signed gauge/cap
constraints. The 32 computational common-box removals still need kernel
certification if used. Keep the top-pinned branch through 8 separate from
the branch missing 8, which visits 5,7,15.
