# Scholz–Brauer research

The programme studies

\[
  \ell(2^n-1) \le n-1+\ell(n) \qquad (n>0),
\]

where `ℓ(n)` is the minimum number of additions in an addition chain for `n`.
Computational claims must have independently checkable certificates; a short
witness, its optimality, and the Scholz upper bound are separate claims.

## Verified status — 18 September 2026

The first daily run found only the initial README. Its advertised Python
library, experiments, results and Lean infrastructure did not exist. The original
Brauer-lift claim was withdrawn then; the construction has now been implemented
and independently checked.

The repository now has a Lean certificate generator that starts at 1 and
replays explicit summand pairs, rejecting unavailable summands or non-increasing
steps. Kernel-checked theorems establish that successful replay gives an addition
chain, with exactly one addition per pair, and therefore an upper bound on `ℓ`.

The published chain

```text
1, 2, 4, 6, 12, 13, 24, 48, 96, 192, 384, 768, 781,
1562, 3124, 6248, 12496, 12509
```

has been checked by Lean replay, by direct evaluation of the upstream
addition-chain predicate, and independently using Python integers. It proves
`ℓ(12509) ≤ 17`. The reused doubling lemma also proves `14 ≤ ℓ(12509)`.
The step `24 = 12 + 12` after `13` makes this particular chain non-star.

The published **18-step star witness** now has an explicit Brauer lift, checked
by independent integer replay and a value-only star check. It establishes
`ℓ(2^12509-1) ≤ 12526`. The Python generator also passes all 842 star prefixes
with at most six steps and endpoint at most 32, binary lifts for exponents
1–256, and 23 negative checks. See the dated report in `results/`.

**Not established here:** `ℓ(12509)=17`, the shortest star length 18, a Hansen
classification, or the length-12525 Hansen lift. The checked 12526 upper bound
does not establish the Scholz bound for 12509. The lift is not yet formalised
in Lean.
The initial claim about 5,784,689 being the first non-Hansen number remains a
literature lead pending direct primary-source verification; it is not a local
result or a claim about the current research frontier.

## Reproduce

```sh
cd lean
lake build
lake env lean Audit.lean
cd ..
python3 scripts/check_12509.py
python3 scripts/check_certificate.py results/2026-09-18-12509-star-certificate.json --exponent 12509 --additions 12526 --require-star
python3 scripts/verify_star_lift.py --output results/2026-09-18-star-lift-checks.json
```

Lean 4.27.0, mathlib and transitive dependencies are pinned. See `lean/README.md`
for setup, licence attribution and the adaptation from Google DeepMind's
formal-conjectures implementation. Its open Scholz theorem is an uncompiled
reference and is not imported into the proofs.

## Files and next work

- `lean/ScholzBrauer/AdditionChain.lean`: adapted upstream definitions and lemmas.
- `lean/ScholzBrauer/Certificate.lean`: replay generator, soundness and length proofs.
- `lean/ScholzBrauer/Example12509.lean`: concrete witness and numerical bounds.
- `scripts/check_12509.py`: independent exact check, including invalid fixtures.
- `scripts/star_lift.py`: star/Brauer lift to explicit summand-index pairs.
- `scripts/check_certificate.py`: independent replay and value-only star checker.
- `scripts/verify_star_lift.py`: bounded exhaustive and regression checks.
- `data/12509-star.json`: published source chain and attribution.
- `results/`: dated verification evidence and source notes.
- `RESEARCH_LOG.md`: dated increments; `TODO.md`: ordered roadmap.

Next: formalise the checked star/Brauer lift, then construct the Hansen lift for 12509.
Only after these work should structural obstructions and larger documented
non-Hansen cases become computational targets. See `TODO.md` for the next
experiment and formal lemma.

## Sources

- [OEIS A349044](https://oeis.org/A349044): the explicit witness checked here;
  optimality statements remain separately sourced claims.
- [Flammenkamp, Shortest Addition Chains](https://wwwhomes.uni-bielefeld.de/achim/addition_chain.html).
- [Clift, Scholz–Brauer notes](https://www.additionchains.com/ScholzBrauer.html):
  retrieval failed on this run; revisit before relying on its detailed claims.
- [formal-conjectures, inspected revision](https://github.com/google-deepmind/formal-conjectures/tree/40e7c98697de6f66b8cbdbf641749ab39ed9c152).
