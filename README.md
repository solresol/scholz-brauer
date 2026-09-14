# Scholz–Brauer research

Computational and formal experiments around the Scholz–Brauer conjecture

\[
  \ell(2^n-1) \le n-1+\ell(n),
\]

where `ℓ(n)` is the minimum number of additions in an addition chain for `n`.

The research strategy is to keep computational claims certificate-based, use failed stronger statements to expose structure, and formalise the reusable parts in Lean.

## Current computational focus

The classical Brauer construction proves the bound whenever `n` has an optimal star/Brauer chain. The first number for which this route fails is `n = 12509`: published exhaustive data give `ℓ(12509)=17` but shortest star-chain length `ℓ*(12509)=18`. The code in this repository verifies explicit certificates and reproduces the corresponding one-step deficit: lifting a shortest star chain gives a chain for `2^12509-1` of length `12526`, whereas the Scholz target is `12525`.

This makes two structural frontiers especially useful:

1. **Hansen / non-star lifts.** Explain exactly how the known optimal Hansen chain for 12509 recovers the missing step, then implement that lift as a checked certificate generator.
2. **Beyond Hansen.** Neill Clift's computations report that all `n < 5,784,689` are Hansen numbers, while `5,784,689` is not. This is a natural first target for testing stronger structural classes.

## Formalisation status

Do not start addition chains from scratch in Lean. In 2026 the `google-deepmind/formal-conjectures` project added:

- `FormalConjecturesForMathlib/NumberTheory/AdditionChain.lean`, defining `IsAdditionChain`, `additionChainSteps`, `additionChainLength`, and basic upper/lower-bound lemmas;
- `FormalConjectures/Wikipedia/ScholzConjecture.lean`, stating the conjecture and proving the first values of `ℓ`.

Future Lean work here should reuse or adapt that implementation, then add star chains, Hansen-style witnesses, and constructive lifts.

## Repository layout

- `src/addition_chains.py` — exact certificate checking, small exhaustive search, and the Brauer lift.
- `experiments/` — reproducible computational runs.
- `results/` — dated results and literature notes.
- `lean/` — future Lean work.

## Sources / data landmarks

- Achim Flammenkamp, [Shortest Addition Chains](https://wwwhomes.uni-bielefeld.de/achim/addition_chain.html).
- Neill M. Clift, *Calculating optimal addition chains*, Computing 91 (2011), 265–284.
- [OEIS A349044](https://oeis.org/A349044), non-Brauer numbers and explicit 12509 certificates.
- Neill Clift, [Scholz-Brauer notes](https://www.additionchains.com/ScholzBrauer.html).
- Google DeepMind, [formal-conjectures issue #2217](https://github.com/google-deepmind/formal-conjectures/issues/2217).

## Immediate next experiments

- Implement a precise Hansen-chain witness/checker and its Mersenne lift; reproduce the length-12525 certificate symbolically for `n=12509`.
- Test structural classes (Hansen, quasi-closed/related variants) against exact optimal-chain data, prioritising the known non-Brauer numbers and then `n=5,784,689`.
- Separate three questions in all reporting: existence of *some* short chain, proof of optimality of a chain, and proof of the Scholz upper bound. A certificate establishes only the first unless an independent lower bound is supplied.
