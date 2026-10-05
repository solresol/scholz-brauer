# Lean certificate foundation

From this directory:

```sh
lake update                 # only needed for initial dependency installation
lake build
lake env lean Audit.lean
```

Lean is pinned to 4.27.0 and mathlib to
`a3a10db0e9d66acbebf76c5e6a135066525ac900` (v4.27.0).
`lake-manifest.json` pins the transitive dependencies. The inspected upstream revision
uses Lean/mathlib 4.33.1; this small adaptation uses the already
available 4.27.0 toolchain.

`ScholzBrauer/AdditionChain.lean` adapts the Apache-2.0 implementation from
Google DeepMind's formal-conjectures commit
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`.
The definitions and theorem statements are unchanged. Compatibility edits remove
`module`, `public`, and `@[expose] public section`, and replace the renamed
`Mathlib.Order.Lattice.Nat` import with `Mathlib.Data.Nat.Lattice`.
Original files, licence, exact URLs and SHA-256 hashes are in
`vendor/formal-conjectures/`.

The upstream `ScholzConjecture.lean` is retained **only as an uncompiled source
reference**. Its open statement contains `sorry`; it is not imported by this
library and supplies no hypothesis or theorem to our proofs. Our compiled files
contain no `sorry`, custom axiom, or `native_decide`. Concrete proofs use `decide`,
which Lean's kernel checks.

`Certificate.lean` provides:

- `replay`: generate a strictly increasing chain from explicit summand pairs,
  starting at `[1]`, or return `none` when a step is invalid;
- `append_sum`, `replay_sound`: prove every successful replay is an addition
  chain under the upstream definition;
- `replay_length`: prove exactly one addition per supplied pair;
- `replay_upper_bound`: turn successful replay and an endpoint check into an
  upper bound on the minimum addition-chain length.

`Example12509.lean` replays a published 17-step witness and also checks the list
directly against the upstream predicate. `Exclusion12509Optimal.lean` now proves
`additionChainLength 12509 = 17` and the end-to-end numerical Scholz instance,
using the complete kernel-checked exclusion through 16 additions and the general
Hansen bound 12525. The independent C++/Python searches remain computational
evidence; their results are not imported as axioms. `Audit.lean` checks the
transitive dependencies of the key theorems. The independent witness check is
`python3 ../scripts/check_12509.py`.

`BrauerBlock.lean` provides the next constructive layer:

- `doublingSteps`: an executable summand-value certificate; replay is proved
  to succeed from any valid endpoint, retain all old values, and end at `2^k*a`;
- `replayFrom_append`: composition of arbitrary certificate replays;
- `brauerBlock_replay`: given a valid chain ending at `2^a-1` and containing
  `2^b-1`, replay a block to `2^(a+b)-1` with exactly `b+1` new entries;
- `brauerBlock_upper_bound`: if the starting chain has `r` additions, the
  extended endpoint has minimum addition-chain length at most `r+b+1`.

Membership of the stored value is a hypothesis checked by replay, not an
assumed version of the conjecture. The Lean
certificate names summand values; no equivalence with the Python index-format
certificate generator has been proved. Five kernel-evaluated examples cover
zero doublings, two successful blocks, and absent/zero stored values.

`StarLift.lean` now proves the complete construction:

- `IsStarFrom source a bs` checks that each increment is already stored in
  the source prefix; `starSourceFrom` constructs the resulting source list.
  Source validity, endpoint `a+sum(bs)` and exact source length are proved.
- `starCertificateFrom` concatenates explicit Brauer blocks. Its length is
  `sum(bs)+length(bs)` for any inputs; correctness requires checked increments.
- `starCertificateFrom_replay` proves successful replay, chain validity,
  endpoint, exact length, retention of the initial target chain, and membership
  of every source Mersenne value throughout the completed lift.
- `starLift_certificate` and `starLift_upper_bound` specialise to `[1]`, giving
  exactly `n-1+r` additions and the resulting numerical bound. The empty
  increment list covers `n=1` without a separate exception.
- `scholz_of_optimal_star` proves the conjectured inequality under an explicit
  minimum-source-length hypothesis. No optimality theorem is assumed globally.

`Example12509.lean` also checks the published 18-step star source and applies
the general theorem to prove `additionChainLength (2^12509-1) ≤ 12526` and
successful replay of its explicit certificate. It does not expand the entire
large certificate for closed kernel evaluation. The stronger Hansen bound
12525 is now formalised by the general theorem below.
Seven small kernel-checked examples cover the singleton source, a complete
two-block replay, and zero, unavailable and future increments. `Audit.lean`
now covers 135 named theorems; standard axiom dependencies are checked by the
integration runner.

`Hansen.lean` checks a marking certificate given as `(value, Bool)` entries,
with initial value 1 marked implicitly. `IsHansenFrom` requires strict growth
and a decomposition using the latest marked value and any stored value.
Acceptance enforces a marked endpoint. It is decidable and does not assume
optimality. Its proved API includes:

- successful source replay via `hansenPairsFrom`, source validity under the
  upstream predicate, and exactly one addition per source entry;
- `hansenAnchorFrom_latest` and `hansen_latest_anchor_step`: at every cut the
  carried anchor is the latest actual mark, is stored, and is a summand of
  the next step;
- stored marked values bounded by the final anchor, splitting an accepted
  certificate, and an explicit theorem forcing the final flag to be true.

Nine kernel-evaluated boundary/regression examples accompany the general
proofs. Five new named 12509 theorems check its marking, source list, replay,
marked-value list and 17-step count. The marking matches the saved Python
Hansen certificate. No detector completeness theorem or Python/Lean format
isomorphism is claimed. The large Hansen Mersenne lift is now proved below;
source optimality
remains outside Lean. See `../results/2026-09-24-hansen-underlining-lean.md`.

`HansenShift.lean` proves the shift accounting independently of the future
Mersenne replay. `hansenShiftDemands` lists consumers of the current anchor
through the next mark, and `hansenShiftMax` computes their maximum. For any
valid source prefix and accepted continuation, that maximum is exactly the
next-mark gap. `hansenShiftCaps` gives one cap per marked value, ending in zero;
its head is the actual maximum and its sum plus the initial anchor equals the
final anchor. Starting at 1 gives sum `n-1`.

Eight general theorems, eight kernel-evaluated examples and three 12509
specialisations cover the count. The concrete cap list matches the saved
Python certificate at its marked indices, with zero at every unmarked index.
The sum 12508 and budget 12525 are proved. Shifted-node distinctness is now
proved in `HansenNodes.lean`; allocation and sorted replay are now proved
below. The numerical Lean bound is 12525 and the source optimum remains unformalised.

`HansenReplayFixtures.lean` is generated by the bounded Python exporter
`../scripts/export_lean_certificate.py`. It contains eight audited theorems:
replay, exact count, chain validity and a numerical upper bound for each of the
singleton and interleaving-29 lifts. The latter proves
`additionChainLength (2^29-1) ≤ 35` using closed kernel `decide` replay and the
existing soundness theorem. Neither source optimum nor Mersenne optimum is
asserted. This finite interface check does not prove correctness of the Hansen
generator or equivalence of arbitrary index and value certificates.

Regenerate a comparison file and check the whole bounded family from the repo root:

```sh
python3 scripts/verify_lean_export.py --output results/export-local.json --emit-fixtures results/export-local.lean
```

Both output paths must be fresh; saved fixture source must match exactly.
The script's Python checks do not run Lean. `lake build` here compiles both
saved fixtures, and `lake env lean Audit.lean` audits their proof dependencies.
The generic exporter accepts a checked index JSON and explicit `--name`,
`--exponent`, `--additions`; it refuses exponents above 64 or more than 128
additions before replay. Compiling its output is always a separate requirement.

`HansenNodes.lean` defines `shiftedMersenne a k = 2^k*(2^a-1)` and proves
seven general theorems: odd Mersenne remainder, unique power-of-two/odd-part
factorisation, injectivity for positive exponents, positivity, doubling,
base-node addition and preservation of duplicate-free labels under value
conversion. It reuses `Nat.pow_right_injective`, `List.Nodup.map_on` and the
existing `mersenne_block_identity`; no new dependency or toolchain change.

Six checked examples cover the essential zero-exponent failure, exponent 1,
zero and positive shifts, the two interleaving windows in the saved 29 fixture,
and separation of the 12 and 13 families for arbitrary shifts in the 12509
source. The general injectivity proof is unbounded. The list theorem assumes
duplicate-free labels and positive exponents; the allocation proof below
establishes these conditions before applying it.

`HansenAllocation.lean` completes the finite allocation proof. `hansenLabels`
contains one base per source value and every marked-anchor shift through the
next-mark gap. Its order groups labels by intervals and can differ from numerical
order. Theorems prove base membership, downward shift closure, positive exponents,
no duplicate labels, exact length `steps.length + caps.sum + 1`, and the endpoint
envelope. `hansenLabels_base_sums` carries an ambient allocation invariant so
previous bases remain available while unmarked steps retain their anchor.
`hansenLabels_closed` gives two allocated summands for every non-seed label.

`HansenLift.lean` completes milestone 1:

- `hansenLift` maps labels to exact Mersenne values and merge-sorts them.
- `hansenLift_chain` proves the upstream addition-chain predicate, endpoint
  `2^n-1`, and exactly `n-1+steps.length+1` entries.
- `additionChain_exists_replay` constructs an existential summand-value replay
  from any addition chain; positivity puts its summands in earlier prefixes.
- `hansenLift_certificate` gives successful sorted replay and exactly
  `n-1+steps.length` additions. This is a general kernel-checked existence
  theorem, not a new exported list of 12525 concrete pairs.
- `hansenLift_upper_bound` gives the numerical bound. `scholz_of_optimal_hansen`
  adds only the explicitly stated optimality hypothesis for this source.

`Example12509.lean` applies the general theorem to its already checked source,
proving `hansenLift12509_chain`, `hansenLift12509_certificate`, and
`mersenne12509_length_le_12525`. It does not expand or kernel-evaluate the
12526 large numerical nodes. No Python/Lean certificate-format equivalence,
source optimum or Mersenne optimum is claimed. Exclusion soundness is now proved
below; the remaining obligation is the kernel-checked lower bound 17.

`Exclusion.lean` advances milestone 2. `ChainReach` describes at most a given
number of increasing addition steps from a prefix; its doubling bound and
monotonicity are proved. Both whole chains and arbitrary valid extensions under
upstream `IsAdditionChain` map into this relation. Positivity places every
summand before its sum, so no star-chain restriction enters the proof.

`checkExclusion` implements the portable bound/gap/split rules over a node array.
It rejects a reached target and invalid references, checks every necessary
next value and every child, and decreases the remaining step budget. It allows
extra edges, which add proof obligations, and does not require backward references
for termination. These harmless relaxations mean that an isomorphism with the
Python checker is neither claimed nor required. Shared nodes are always evaluated
in their current prefix. `checkExclusion_sound` proves non-reachability;
`checkExclusion_excludes_extension` states it directly for upstream chains;
`checkExclusion_lower_bound` transports it to `additionChainLength`, given a
known witness for nonemptiness.

`exclusionSeven_checked` kernel-evaluates the existing generator's three-node
7/3 certificate. `length_seven_eq_four` combines it with `[1,2,3,4,7]`.
Eight kernel examples cover the essential accepting/rejecting rule boundaries,
including the same gap node in two different contexts. Early direct evaluation
of the large DAG failed within its bounds. The complete exclusion is now checked
using the sound abstract-context representation described below.

`Exclusion12509Lower.lean` now proves `sixteen_le_length12509`: all chains with
at most 15 additions are excluded. The deterministic exporter embeds the checked
475-node JSON as constructor data and emits 403 context-specific proof fragments.
Each leaf checks at most 100 rule occurrences with `decide +kernel`; parent
fragments use `checkExclusionWith_split`. `Elab.async false` prevents proof jobs
from accumulating. The final theorem audit includes all transitive dependencies.

`ExclusionTree.lean` provides balanced lookup and a data-only expression elaborator;
the elaborator does not run the checker or create proofs. `checkExclusionWith_sound`
is proved for arbitrary lookup functions, so no unproved array/tree equivalence
is needed. The existing array API remains available. Shared syntax never permits
sharing a conclusion across distinct prefixes. See the 3 October report for
resource failures and the historical `[16,17]` interval. The completed bit-set
certificate strengthens this to exact source length 17.

`ExclusionContext.lean` proves `ChainReach.enlarge` and sound exclusion on
explicit supersets of source prefixes. Each local check verifies the endpoint
envelope, viable next-value coverage and every child inclusion (as a sublist),
new-value membership, endpoint and decremented budget. The active-summand filter
is justified by the existing doubling bound. Soundness uses induction on the
remaining budget and assumes acceptance of every referenced state; it does not
cache truth by syntax node ID or assume a Python checker equivalent.

`ExclusionContextChecks.lean` validates 7/3 and five meaningful rejection cases.
`Exclusion12509ContextsData.lean` contains 29,865 abstract contexts, compiled as
constructor data. `Exclusion12509Part00.lean` kernel-checks the first 2,496 local
states. `Exclusion12509Partial.lean` aggregates that checked prefix and proves
`contexts12509_gap_excluded`: gap contexts in the prefix exclude their target.
It does not assume acceptance of the rest of that list-based table. Its historical
partial result is retained independently of the completed bit-set proof.

`ExclusionBits.lean` represents context and edge sets by exact natural-number
bit masks. `testBit_valueBits` characterises membership; `mem_of_bits_subset`
justifies the bitwise inclusion test. `checkBitContext_sound` proves exclusion
by induction on the remaining budget, checking every encoding before using it.
The data elaborator only emits candidate constructors and masks; every encoding
and every local condition must pass the kernel. There is no native proof acceptance.
`ExclusionBitsChecks.lean` validates 7/3 and six corrupt-certificate cases.

`Exclusion12509BitsData.lean` and twelve `Exclusion12509BitPart*.lean` modules
kernel-check all 29,865 states. `Exclusion12509Optimal.lean` composes the complete
acceptance, proves `seventeen_le_length12509`, then `length12509_eq_seventeen`
and `scholz12509`. The original upstream open target is not imported or assumed.

The exporter supports `--representation bits` with `--data-output`,
`--proof-output` and `--parts-output`. The default list representation and its
partial aggregate are unchanged. Export always reports `lean_proof: false`;
compilation and dependency auditing are separate requirements. Integration
regenerates both retained representations, compares their exact bytes, builds
the library and audits 135 theorems. Proof batches allow at most three workers.

See `../results/2026-10-05-scholz12509-lean.md` for the completed milestone,
bounded cost probes and build evidence. The 4 October full list-based timeouts
remain documented in that day's report; they no longer block this proof.

## Non-Hansen 29 experiment (6 October 2026)

`ScholzBrauer/NonHansen29.lean` kernel-checks that Clift's fixed source
`[1,2,4,8,9,13,16,29]` admits no Hansen marking, checks the minimum of the
standard-orientation cap function, and replays a 35-addition Mersenne witness
whose only non-Mersenne base is at source value 9. It also proves a general
local repair identity. The fixed-spine uniqueness search is separate exact
Python evidence, not a general Lean labelling theorem. Source and Mersenne
optimality are not asserted. See `../results/2026-10-06-non-hansen29.md`.
