# Changed-tail domains for the selected 109 graph

15 October 2026, Thursday, Australia/Sydney (AEDT). Active milestone 3;
milestones 1 and 2 remain complete. This run closes structural/domain proof
obligations, not a new enumeration or minimum-cost theorem.

## Result and decision impact

Write Mv=2^v-1. With only **B58=M58 and B109=M109 fixed**, arbitrary positive
bases satisfying Clift's selected graph necessarily have

    B51 = M51*2^k,  0 <= k < 8,
    B7  = M7 *2^l,  0 <= l < 44,
    k = 0 or l = 0.

Thus there are at most **51 candidate (B51,B7) pairs**: k=0,l=0..43,
and k=1..7,l=0. The other bases at 2,4,5,8,15,23,28 remain free. This
allows tail changes at 23,28,51; the old four-fixed-tail reduction was not used.
Lean also proves the precise shift constraints at 58 and 109. These are
necessary conditions; neither global feasibility of all 51 pairs nor the
minimum cap sum for this family has been established.

If instead **B51=M51** is fixed, the terminal equation has a complete local
domain for B58: **52 shifted-block forms and 57 separated-interval forms**.
Every listed form satisfies that local equation for some shifts; satisfying
the rest of the graph remains a separate obligation.

## General theorem and proof

For p,q>0, Lean proves the following iff, with arbitrary natural u,a,b:

    u*2^a + Mq*2^b = M(p+q)

holds precisely when either

- u=Mp*2^k, with (k+a=q,b=0) or (k+a=0,b=p); or
- a=0, 0<b<p, and u=M(p-b)*2^(q+b)+Mb.

The first case adjoins two binary blocks; the second is the pair of separated
intervals [0,b) and [q+b,p+q). `mersenne_complement_iff` proves necessity and
sufficiency. `mersenne_complement_domain` eliminates a,b and proves the finite
iff with k in 0..q and separated indices b in 1..p-1. No shift bound,
population-count theorem, carry-free assumption or computational checker is
assumed. The proof reuses `nonblock_mersenne_complement`, the Mersenne block
identity and `Clift109.mersenne_sum_shifts`.

`half_mersenne_complement` strengthens the earlier smallness criterion:
**2*u<M(p+q)** suffices to force a shifted Mp, even if u is not smaller than
Mq. In the separated case b<p, twice Mq*2^b is at most Mq*2^p, so the
complement exceeds half the full block. This contradicts the new bound.

## Applying the theorem to actual graph equations

`Clift109.fixed58_tail_rigid` uses positive summands and nonnegative shifts
on the selected edges to prove

    B7 < B15 <= B23 < B28,
    2*B7 < B51 < B58=M58.

The terminal equation with fixed M58 first forces B51=M51*2^k, k<8. The
production equation for M58 then has shifted M51 as one summand. The new
half-block lemma forces B7=M7*2^l. Two-block orientation yields, in the
repository's convention a=first-parent shift and b=second-parent shift:

    (k+a58=7 and l+b58=0) or (k+a58=0 and l+b58=51),
    (a109=51 and k+b109=0) or (a109=0 and k+b109=58).

The first disjunction forces l=0 or k=0. In the k=0 case, 2*B7<M51
forces l<44; this yields the stated 51-pair necessary domain. No seed
normalisation or budget hypothesis is needed for this theorem, so it applies
in particular to the intended seed-1 budget-108 problem.

`Clift109.fixed51_terminal_domain` specialises the general finite iff to
p=58,q=51. It is deliberately a terminal-equation theorem, without an
assertion that its solutions meet the earlier graph equations.

## Verification and provenance

All five theorems are in `lean/ScholzBrauer/MersenneComplement.lean`, with
entries in `lean/Audit.lean`. Toolchain and dependencies are unchanged:
Lean 4.27.0 and mathlib a3a10db0e9d66acbebf76c5e6a135066525ac900.
The adapted Google DeepMind addition-chain definitions and Apache-2.0 licence
were inspected, alongside its uncompiled Scholz reference. The unproved
upstream target is not imported or assumed. No new infrastructure was needed.

Direct development checks used, from lean/:

    /usr/bin/time -p lake env lean ScholzBrauer/MersenneComplement.lean

The general lemmas passed in 14.10s; the first graph application passed in
5.62s; tightening l<51 to l<44 passed in 3.75s. All exited zero. No failed
proof attempt, solver call or search timeout occurred. These are symbolic
kernel proofs with no random seeds or finite experimental input range.

The required integration command passed once:

    python3 scripts/verify_integration.py --output results/2026-10-15-integration-checks.json

Python 3.9.6; total **181.819215s**, all **25 commands** succeeded. Pinned Lean
build passed in **16.025987s**; the **191-theorem** axiom audit passed in
**6.914222s**, using only propext, Quot.sound and Classical.choice. All five
vendor hashes and 98 research input hashes matched, including a fresh readback
after completion. The compiled proof-source scan contains no sorry, admit,
custom axiom, native_decide or unsafe. The existing integration suite was
reused without additional experiments or validation layers. Its full structured
report was checked, and the complete source/document diff reviewed.

Re-fetched [Clift's primary account](https://www.additionchains.com/ScholzBrauer.html)
and [selected graph](https://www.additionchains.com/LargeNonHansen.png) on
15 October. Both hashes match the 8/14 October versions; URLs, access time
and version hashes are in `data/2026-10-15-clift109-source-recheck.json`.
The selected graph uses 8=4+4; the same values admit the previously checked
8=7+1 star/Hansen source. No new source optimality, Mersenne optimality,
Scholz instance, unrestricted-labelling exclusion or novelty is claimed.

## Next obligation

Determine the minimum cap sum with only B58 fixed. Reuse the existing exact
complement/production enumerator on the 51 candidate pairs, leaving all
seven other intermediate bases free, or prove stronger repeated-consumer
constraints first. Keep this enlarged search bounded and checkpointed.
The 109-form fixed-B51 domain is an alternative; it needs production/reuse
constraints before it becomes a whole-graph domain. Both terminal parents
varying simultaneously remains outside these reductions.
