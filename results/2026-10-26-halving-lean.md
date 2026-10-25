# Exact interval halving — 26 October 2026

Monday, Australia/Sydney. Milestone 3 advanced; milestones 1 and 2 remain
complete. Clean main at dbbc124, intended origin verified, fetch/ff-only
already current. Process cwd inspection found this run's runtime and an SSH
control master, no competing research process. No unrelated changes were present.

## Closed obligations

The existing interval searches remove a seven-weight exceptional component
and recover the rest by halving with translation u or d1. Their mathematical
completeness depended on this recovery being exact; the previous Lean files
proved the normalized interval but not this step. `Clift109Halving.lean` closes
that specific gap, without adding a solver, exporter or certificate format.

For a finite integer multiset S and positive d, the new theorem proves:

    halve d S = some A  iff  S = A + (A translated by d).

The proof is constructive. The least weight of a nonempty translated double
must belong to A: belonging only to its translate would exhibit a smaller
weight in S. Remove that occurrence and its partner; induction recovers the
rest. Each iteration removes one weight from A, so input cardinality supplies
sufficient fuel. Soundness restores both removed occurrences. Consequences:
the half is unique, and rejection excludes every half, not merely a bounded
attempt. Integer offsets and multiplicities are allowed; no positivity of
weights or disjointness is assumed for the general theorem.

For the 109 graph, the existing 45-weight remainder is proved to have both
factorizations used by the independent searches:

    remainder = sinkHalf + (sinkHalf translated by d1) + sinkExceptions
    remainder = sourceHalf + (sourceHalf translated by u) + (A3 + rem5)

Each half has nineteen weights, each exceptional component seven. These are
unconditional multiset identities. Under the exact interval equation all parts
are distinct and disjoint. `interval_halving` recovers both nineteen-weight
halves from interval-minus-box-minus-exceptions. `halving_of_budget` derives
positive u and d1 from box dissociation and applies both recoveries to every
hypothetical natural labelling of the selected graph with budget at most 108.
Four small kernel evaluations cover empty input, negative repeated weights,
overlapping translates and rejection. They check meaningful boundary behavior;
the general soundness/completeness proof does not rely on these examples.

## Mathematical limits and next obligation

This is a completed exact reduction, not the full interval enumeration or
109 exclusion. No equivalence with the C++ arithmetic/bit-mask implementation
or the Python simultaneous peeling implementation is claimed. Their shared
factorization and unique-half specifications are now Lean theorems. Odd-run
pruning, the 216-configuration classification and cap infeasibility still need
kernel proofs; the full minimum 109 remains computational. No new Scholz
instance, optimum, general lift or novelty is asserted.

Continue using the twelve critical families and oriented cap constraints.
Next justify the at-most-seven-odd-runs pruning condition before removing the
seven exceptions, or prove a stronger restriction such as min(u,d1)=1 under
the necessary interval hypotheses. The latter remains a proposed lemma, not a
result. Do not rerun the completed enumeration or build another certificate
layer. This run continued Lean on a computational day because the exact searches
were already complete and the active blocker was their formal reduction.
The representation remains productive; there is no repeated failed search to
justify a strategy reset.

## Sources and proof attempts

Read the 24 October weekly literature review before choosing work; its scoped
findings supply no checked replacement for the current reduction. Clift's live
page and diagram SHA-256 hashes match 25 October (URLs and access time in
`data/2026-10-26-halving-source-recheck.json`). Read the actual two enumeration
implementations. Inspected the adapted upstream addition-chain definitions,
pinned provenance/licence and separate uncompiled Scholz statement; the open
target is neither imported nor assumed. No dependency or toolchain changes.

Initial Lean errors were proof-script details: split_ifs had already removed
impossible branches, multiset cons order needed cons_swap, and the selected
minimum's local definition needed an explicit cons_erase proof. A first repair
command used a repository-relative path while in lean/ and changed nothing.
No mathematical hypothesis failed, no proof limit was raised, and the final
standalone compilation passed without warnings in 15.65 seconds at default
heartbeats. No new exhaustive or heuristic research search, input range or
random seed was used; the proofs quantify over every finite integer multiset.

Commands (the first from lean/, the second from repository root):

    /usr/bin/time -p lake env lean ScholzBrauer/Clift109Halving.lean
    uv run scripts/verify_integration.py --output results/2026-10-26-integration-halving.json

Required integration passed once in 437.335777 seconds: 30 commands,
Lean 4.27.0 full build and 287 audited theorems, with only the permitted standard
axioms propext, Classical.choice and Quot.sound. All 123 input SHA-256 hashes
were independently read back and matched; five vendor hashes were checked.
The existing bounded computational regressions ran within integration, not as
new research experiments. The complete source/documentation diff and structured
report were reviewed; git diff --check and the new-file proof-token scan passed.
Remote CI was not checked.
