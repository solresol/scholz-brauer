import ScholzBrauer.Hansen
import ScholzBrauer.BrauerBlock

/-! Clift's non-Hansen source and a finite one-exception lift.
Source: https://www.additionchains.com/ScholzBrauer.html, rechecked 2026-10-06.
The unique fixed-spine labelling is a separate Python experiment. No general
extension, source optimum, or Mersenne optimum is assumed or proved here. -/
namespace ScholzBrauer.NonHansen29

def source : List ℕ := [1, 2, 4, 8, 9, 13, 16, 29]

theorem source_valid : IsAdditionChain source := by decide +kernel

/-- Exhausts every marking, including endpoint choices, using the existing
Hansen predicate. Source summands are existential, not preselected. -/
theorem source_not_hansen (b₂ b₄ b₈ b₉ b₁₃ b₁₆ b₂₉ : Bool) :
    ¬ IsHansenFrom [1] 1
      [(2, b₂), (4, b₄), (8, b₈), (9, b₉), (13, b₁₃), (16, b₁₆), (29, b₂₉)] := by
  revert b₂ b₄ b₈ b₉ b₁₃ b₁₆ b₂₉
  decide +kernel

/-- Caps for all standard Mersenne-base orientations of the three unequal
parent pairs. The four equal-parent choices do not change their caps. -/
def mersenneCaps (reverse9 reverse13 reverse29 : Bool) : List ℕ :=
  [if reverse9 then 8 else 1,
   2,
   if reverse13 then 9 else 4,
   8,
   if reverse13 then 0 else 4,
   if reverse29 then 16 else 0,
   if reverse29 then 0 else 13,
   0]

theorem mersenne_orientation_min :
    (∀ x y z, 32 ≤ (mersenneCaps x y z).sum) ∧
      (mersenneCaps false false false).sum = 32 := by decide +kernel

def liftedSteps : List Step :=
  [(1, 1),
   (2, 1),
   (3, 3),
   (6, 6),
   (12, 3),
   (15, 15),
   (30, 30),
   (60, 60),
   (120, 120),
   (240, 15),
   (255, 255),
   (510, 510),
   (1020, 1020),
   (2040, 2040),
   (4080, 4080),
   (8160, 1),
   (8161, 30),
   (8160, 8160),
   (16320, 16320),
   (32640, 32640),
   (65280, 255),
   (65535, 65535),
   (131070, 131070),
   (262140, 262140),
   (524280, 524280),
   (1048560, 1048560),
   (2097120, 2097120),
   (4194240, 4194240),
   (8388480, 8388480),
   (16776960, 16776960),
   (33553920, 33553920),
   (67107840, 67107840),
   (134215680, 134215680),
   (268431360, 268431360),
   (536862720, 8191)]

def liftedValues : List ℕ :=
  [1, 2, 3, 6, 12, 15, 30, 60, 120, 240, 255, 510, 1020, 2040, 4080, 8160, 8161, 8191, 16320, 32640, 65280, 65535, 131070, 262140, 524280, 1048560, 2097120, 4194240, 8388480, 16776960, 33553920, 67107840, 134215680, 268431360, 536862720, 536870911]

theorem lifted_replay : replay liftedSteps = some liftedValues := by decide +kernel

theorem lifted_count : liftedSteps.length = 35 := by decide +kernel

theorem lifted_valid : IsAdditionChain liftedValues := replay_sound lifted_replay

theorem lifted_bound : additionChainLength (2 ^ 29 - 1) ≤ 35 :=
  certificate_upper_bound lifted_replay (by decide +kernel) (by decide +kernel)

/-- Only the source-9 base departs from a Mersenne number. These identities
explain the repair: the source-4 contribution fills the remaining low bits. -/
theorem exceptional_base_identities :
    8161 = 2 ^ 5 * (2 ^ 8 - 1) + 1 ∧
    8161 + 2 * (2 ^ 4 - 1) = (2 ^ 13 - 1 : ℕ) ∧
    8161 ≠ (2 ^ 9 - 1 : ℕ) := by decide +kernel

/-- A reusable local repair identity. It does not by itself prove allocation,
distinctness, or a global shift budget for any family of source chains. -/
theorem one_gap_repair_identity (a b : ℕ) :
    (2 ^ (b + 1) * (2 ^ a - 1) + 1) + 2 * (2 ^ b - 1) =
      2 ^ (a + b + 1) - 1 := by
  have hlo := mersenne_block_identity b 1
  change 2 * (2 ^ b - 1) + 1 = 2 ^ (b + 1) - 1 at hlo
  have hhi := mersenne_block_identity a (b + 1)
  rw [← Nat.add_assoc] at hhi
  omega

end ScholzBrauer.NonHansen29
