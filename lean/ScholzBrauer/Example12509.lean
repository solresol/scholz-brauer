import ScholzBrauer.StarLift

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

/-- The published 18-step star source from OEIS A349044, rechecked 2026-09-22.
This is a witness; no minimum star-length assertion is used. -/
def starChain12509 : List ℕ :=
  [1, 2, 3, 4, 7, 11, 18, 25, 43, 86, 172, 344, 688, 1376, 1401,
   2777, 5554, 6955, 12509]

def starIncrements12509 : List ℕ :=
  [1, 1, 1, 3, 4, 7, 7, 18, 43, 86, 172, 344, 688, 25, 1376, 2777, 1401, 5554]

theorem starIncrements12509_checked : IsStarFrom [1] 1 starIncrements12509 := by decide

theorem starSource12509_eq : starSourceFrom [1] 1 starIncrements12509 = starChain12509 :=
  by decide

theorem starChain12509_valid : IsAdditionChain starChain12509 := by
  rw [← starSource12509_eq]
  exact starSourceFrom_valid (by decide) (by decide) starIncrements12509_checked

/-- The general theorem checks the large certificate symbolically, without
expanding 12,526 additions or evaluating a huge closed replay in the kernel. -/
theorem starLift12509_certificate :
    ∃ d, replay (starCertificateFrom 1 starIncrements12509) = some d ∧
      IsAdditionChain d ∧ d.getLast? = some (2 ^ 12509 - 1) ∧
      d.length = 12527 := by
  obtain ⟨d, hd, hdc, hdlast, hdlen, _, _⟩ :=
    starLift_certificate (n := 12509) starIncrements12509_checked (by decide)
  exact ⟨d, hd, hdc, hdlast, hdlen⟩

/-- A formal numerical bound, weaker by one than the checked Python Hansen
witness. This does not prove the Scholz inequality at 12509. -/
theorem mersenne12509_length_le_12526 : additionChainLength (2 ^ 12509 - 1) ≤ 12526 :=
  starLift_upper_bound starIncrements12509_checked (by decide)

-- Invalid certificates must fail rather than introduce unavailable or repeated values.
example : replay [(1, 2)] = none := by decide
example : replay [(1, 1), (1, 1)] = none := by decide
example : replay [] = some [1] := by decide

end ScholzBrauer
