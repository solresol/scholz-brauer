# Sparse residue refinement — 5 November 2026, Sydney

Scheduled trigger: 4 November 2026, 21:00 UTC (5 November, 08:00 Sydney).
Active obligation: Lean exclusion of a 108-doubling labelling for Clift's
selected 109 graph. Its arbitrary-label minimum of 109 is already an exact
computational result; this run does not repeat the full enumeration.

## Checked mathematical result

The previous run proves a necessary domain of 606 ordered halving-step pairs
(u,d1). It uses each individual residue fingerprint and the condition that
gcd(u,d1) divides 54 or 55. The seven exceptions have more structure than
their cardinality: each is three pairs at the *opposite* step plus a singleton.

On the source side the pair starts are A3, A3+d2 and A3+q, the step is d1,
and the singleton is A3+p. On the sink side the starts are A1+p,
A1+p+v and A2+p, the step is u, and the singleton is again A3+p.
`Clift109SparseResidues.lean` proves both multiset equalities and proves that
reducing each starting point modulo the tested modulus preserves every
residue multiplicity. Thus the previously proved interval fingerprints imply
both `threePairCompatible u d1` and `threePairCompatible d1 u`. These predicates
require four residues in the finite range 0..m-1 whose seven weights have
exactly the odd-residue set of the interval 0..108.

The theorem `three_pair_constraints_of_budget` transports these necessary
tests, together with membership in the 606-pair domain, to every original
labelling with seed 1, the selected production equations, outgoing cap bounds,
terminal value M109 and cap sum at most 108. Negative normalized coordinates,
repeated residues and cancellation modulo two are all allowed. There is no
carry-free assumption, distinct-residue premise, enumeration assumption,
project-defined axiom or assumed target.

## One bounded exact experiment

`scripts/experiment_clift109_sparse_residues.py` evaluates this exact finite
predicate on all 606 pairs, using Python 3.12.14 and the standard library only:

```sh
python3 scripts/experiment_clift109_sparse_residues.py \
  --output results/2026-11-05-sparse-residue-pairs.json
```

It has a hard 60-second bound, refuses to replace a report, uses no random
seed and completed in 0.290275 seconds. All input bounds, source hashes,
606 directional decisions and witnesses are recorded in that JSON. The two
complete methods are:

1. Work modulo two on residues. The three starting points have odd support
   of size one or three, including all possibilities with repeated starting
   points. Exhaust every such support and test whether adding its translate
   by the opposite step leaves exactly one singleton discrepancy from the
   target interval fingerprint.
2. Independently solve H(i)=T(i)+T(i-d) modulo two along each cyclic step-d
   orbit, for every possible singleton discrepancy. Check closure, retain
   both complementary solutions on every orbit, and use a short dynamic
   program to test total support size one or three. A quotient/remainder
   formula independently reconstructs the interval fingerprint.

The methods agree on every decision: 451 directional tests pass; requiring
both directions retains **344 ordered pairs**, removing **262** from 606.
For every successful test, both methods' witnesses are read back by direct
seven-term Counter multiplicities. All 216 previously saved interval
configurations retain their pairs, and their actual source/sink coordinates
pass the seven-term fingerprint checks. This is a positive control using
saved data, not a rerun or new assertion of enumeration completeness.
The existing independent checker also validates the saved 3,456 cost
certificates, exact minimum 109, replay and seven deliberately corrupted
reports:

```sh
python3 scripts/check_clift109_box.py \
  results/2026-10-18-clift109-box-exclusion.json
```

The **344-pair count is computational, not kernel checked**. The Lean
606-pair cardinality and the new implication to both finite sparse predicates
are kernel checked. These are necessary tests, not feasible configurations.
For example (3,14) and (5,13), with their reversals, are newly excluded by
the computation; (2,3) still passes. Neither min(u,d1)=1, interval/cap
feasibility, the full selected-109 Lean exclusion, a Mersenne-chain optimum
nor a new Scholz theorem follows.

## Runtime, source and verification gate

All research and Lean execution stayed in the selected theorem-provers
environment and only `/workspace/scholz-brauer` was edited. The published
startup instructions were read from `/workspace/shared/theorem-provers/START.md`.
No saved Start skill was present in the available skill catalog, and the
checkout had no `.agents/skills` or applicable AGENTS.md. The Start gate passed:

```sh
source /workspace/shared/theorem-provers/env.sh
python3 /workspace/shared/theorem-provers/check.py
```

Runtime status reported published configuration version
`f4c4ae6d-5a2c-43a6-a161-c34781e84e76~cecfgver_6aea433dd60c81a2acd44e4790f53979`,
as in the preceding verified run. No installation, dependency preparation,
cache retrieval, shared-runtime repair or configuration publication occurred.
The checkout was clean on branch `work` at
`fee607818c18f3a669e5a4451ddd124ed7897f2b`, equal to fetched and live main.
Both ancestry checks passed and `git merge --ff-only origin/main` was already
current. GitHub's primary repository API confirms ID 1368051643,
`solresol/scholz-brauer`, default branch main; its configured authorized origin
is `https://github.com/solresol/scholz-brauer.git`. No competing research
process or research lock was found; an exclusive `.git` run marker was held.
Sibling checkouts and published runtime files were read-only throughout.

Reviewed the [30 October weekly handoff](2026-10-30-literature-review.md), the
latest present in live main, six days old. No later handoff was available;
no fresh broad literature search or claim about broader current novelty was
made. No external theorem is needed for the new parity reduction. The live
primary [Clift account](https://www.additionchains.com/ScholzBrauer.html) and
[selected diagram](https://www.additionchains.com/LargeNonHansen.png) were
accessed 4 November UTC / 5 November Sydney; both hashes match the preceding
recheck. Versions, access times, URLs and hashes are in
`data/2026-11-05-sparse-residue-source-recheck.json`. Only the actual selected
graph and cap interpretation are used; the published exclusion is not assumed.
The adapted upstream addition-chain API, attribution and archived open target
were inspected; the open target is not imported.

Lean 4.27.0 and mathlib revision
`a3a10db0e9d66acbebf76c5e6a135066525ac900` are unchanged. Commands resolve
absolute Lean/Lake binaries through `prepare.m.installed_tools` and use
`prepare.env_for('scholz')`, the Scholz archive directory and
`LEAN_NUM_THREADS=2`. Costly commands use the published guarded runner,
unchanged at a 2 GiB disk reserve, 12 GiB process-group RSS and 1800 seconds.
The exact argv and hashes are in `2026-11-05-sparse-residue-verification.json`.

- Standalone `lake env lean ScholzBrauer/Clift109SparseResidues.lean` passed
  without warnings in 3.002 guarded seconds, default heartbeats.
- Full pinned `lake build` passed **1,136 jobs** in 4.002 guarded seconds.
- `lake env lean Audit.lean` passed **334 entries**, including the six new
  public theorems, in 16.008 guarded seconds. Only the permitted standard
  axioms propext, Quot.sound and Classical.choice appear. The full transcript
  is `2026-11-05-sparse-residue-lean-audit.txt`.
- Exact pin hashes match the published allowlist, all dependency HEADs match
  the manifest and tracked dependency sources are clean; five vendored
  upstream hashes match provenance. No placeholders or native decision
  shortcut occur in the new proof.

Full integration was **not rerun**: the preceding unchanged chain-9 evidence
checker timed out at its 180-second bound, and nothing here addresses that
failure. The prior attempt remains inconclusive; this run claims the direct
Lean build/audit and relevant saved-109 certificate check, not whole-project
integration success. No timeout or resource limit was increased. Complete
source/evidence/documentation diff and whitespace checks are reviewed before
commit; remote CI is not checked.

## Next obligation

Kernel-check an efficient evaluation of the sparse predicates or combine their
proved finite form directly with the existing interval restrictions. The
computational refinement leaves 344 pairs rather than 606, but its remaining
loose cases such as (2,3) need the actual exceptional positions, box
dissociation, both odd-run restrictions, twelve critical families and 64
orientations. Interval/cap classification and the full Lean exclusion remain
unfinished. No completed enumeration needs rerunning.
