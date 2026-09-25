import ScholzBrauer.StarLift
import ScholzBrauer.HansenShift

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

/-- Marking from the independently checked Hansen certificate of 2026-09-21.
The OEIS source values were rechecked on 2026-09-24. Values 4 and 13 are
unmarked; in particular 24 uses the retained anchor 12 after the value 13. -/
def hansenSteps12509 : List MarkedStep :=
  [(2, true), (4, false), (6, true), (12, true), (13, false),
   (24, true), (48, true), (96, true), (192, true), (384, true),
   (768, true), (781, true), (1562, true), (3124, true), (6248, true),
   (12496, true), (12509, true)]

theorem hansen12509_checked : IsHansenFrom [1] 1 hansenSteps12509 := by decide

theorem hansenSource12509_eq : hansenSourceFrom [1] hansenSteps12509 = chain12509 :=
  by decide

/-- Another checked source replay, using the latest marked summand each time.
This is not a proof of the large Hansen lift or source optimality. -/
theorem hansen12509_source_replay :
    replay (hansenPairsFrom 1 hansenSteps12509) = some chain12509 := by
  simpa [replay, hansenSource12509_eq] using hansenPairsFrom_replay hansen12509_checked

theorem hansen12509_marks : hansenMarksFrom 1 hansenSteps12509 =
    [1, 2, 6, 12, 24, 48, 96, 192, 384, 768, 781, 1562, 3124, 6248, 12496, 12509] :=
  by decide

theorem hansen12509_source_count : (hansenPairsFrom 1 hansenSteps12509).length = 17 :=
  by decide

/-- Per-mark maxima, in the same order as `hansen12509_marks`. Unmarked
values 4 and 13 have no shift allocation; the final marked value has cap zero. -/
theorem hansen12509_shift_caps : hansenShiftCaps 1 hansenSteps12509 =
    [1, 4, 6, 12, 24, 48, 96, 192, 384, 13, 781, 1562, 3124, 6248, 13, 0] :=
  by decide

/-- Specialisation of the general telescoping theorem, not a large replay. -/
theorem hansen12509_shift_sum : (hansenShiftCaps 1 hansenSteps12509).sum = 12508 :=
  hansenShiftCaps_sum hansen12509_checked (by decide :
    hansenAnchorFrom 1 hansenSteps12509 = 12509)

/-- This is the verified allocation budget. Lifted-node distinctness and
sorted replay are still required before it gives a Mersenne length bound. -/
theorem hansen12509_shift_budget :
    (hansenShiftCaps 1 hansenSteps12509).sum + hansenSteps12509.length = 12525 := by
  have h := hansenShiftCaps_budget hansen12509_checked (by decide :
    hansenAnchorFrom 1 hansenSteps12509 = 12509)
  simpa [hansenSteps12509] using h

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
