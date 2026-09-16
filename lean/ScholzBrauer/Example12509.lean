import ScholzBrauer.Certificate

namespace ScholzBrauer

/-- Published witness from OEIS A349044, rechecked here; no optimality assumption. -/
def chain12509 : List ℕ :=
  [1, 2, 4, 6, 12, 13, 24, 48, 96, 192, 384, 768, 781, 1562, 3124, 6248, 12496, 12509]

def certificate12509 : List Step :=
  [(1, 1), (2, 2), (4, 2), (6, 6), (12, 1), (12, 12), (24, 24),
   (48, 48), (96, 96), (192, 192), (384, 384), (768, 13),
   (781, 781), (1562, 1562), (3124, 3124), (6248, 6248), (12496, 13)]

theorem replay_certificate12509 : replay certificate12509 = some chain12509 := by decide

theorem chain12509_valid : IsAdditionChain chain12509 :=
  replay_sound replay_certificate12509

/-- Independent direct check of the upstream predicate, bypassing replay. -/
theorem chain12509_direct : IsAdditionChain chain12509 := by decide

theorem length12509_le_seventeen : additionChainLength 12509 ≤ 17 :=
  certificate_upper_bound replay_certificate12509 (by decide) (by decide)

/-- The doubling bound only proves 14, not the published optimum 17. -/
theorem fourteen_le_length12509 : 14 ≤ additionChainLength 12509 := by
  have hne := additionChainSteps_nonempty (n := 12509) (r := 17)
    chain12509 chain12509_valid (by decide) (by decide)
  have h := lt_additionChainLength_of_two_pow_lt (r := 13) hne (by decide)
  omega

-- Invalid certificates must fail rather than introduce unavailable or repeated values.
example : replay [(1, 2)] = none := by decide
example : replay [(1, 1), (1, 1)] = none := by decide
example : replay [] = some [1] := by decide

end ScholzBrauer
