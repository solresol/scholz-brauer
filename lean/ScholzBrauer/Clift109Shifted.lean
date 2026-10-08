import ScholzBrauer.Clift109
import ScholzBrauer.HansenNodes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ScholzBrauer.Clift109

/-- Two shifted positive Mersenne blocks can sum to a shifted block of their
combined length only by adjoining their intervals in one of the two orders.
No upper bound on any shift is assumed. -/
theorem mersenne_sum_shifts {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (a b t : ℕ)
    (h : (2 ^ p - 1) * 2 ^ a + (2 ^ q - 1) * 2 ^ b =
      (2 ^ (p + q) - 1) * 2 ^ t) :
    (a = t + q ∧ b = t) ∨ (a = t ∧ b = t + p) := by
  have op := mersenne_mod_two hp
  have oq := mersenne_mod_two hq
  have ot := mersenne_mod_two (show 0 < p + q by omega)
  have pp : 0 < 2 ^ p - 1 := by omega
  have pq : 0 < 2 ^ q - 1 := by omega
  have block := mersenne_block_identity p q
  have block' := mersenne_block_identity q p
  rw [Nat.add_comm q p] at block'
  have small : (2 ^ p - 1) + (2 ^ q - 1) < 2 ^ (p + q) - 1 := by
    have : 2 ≤ 2 ^ q := by
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hq
      simpa using this
    nlinarith
  induction t generalizing a b with
  | zero =>
    simp only [pow_zero, Nat.mul_one] at h
    cases a with
    | zero =>
      simp only [pow_zero, Nat.mul_one] at h
      have he : 2 ^ b = 2 ^ p := by nlinarith [block']
      have hb := Nat.pow_right_injective (by decide : 2 ≤ 2) he
      exact Or.inr ⟨rfl, by omega⟩
    | succ a =>
      cases b with
      | zero =>
        simp only [pow_zero, Nat.mul_one] at h
        have he : 2 ^ (a + 1) = 2 ^ q := by nlinarith [block]
        have ha := Nat.pow_right_injective (by decide : 2 ≤ 2) he
        exact Or.inl ⟨by omega, rfl⟩
      | succ b =>
        have hm := congrArg (· % 2) h
        simp [pow_succ, Nat.mul_mod, Nat.add_mod, ot] at hm
  | succ t ih =>
    cases a with
    | zero =>
      cases b with
      | zero =>
        simp only [pow_zero, Nat.mul_one] at h
        have := Nat.le_mul_of_pos_right (2 ^ (p + q) - 1) (Nat.two_pow_pos (t + 1))
        omega
      | succ b =>
        have hm := congrArg (· % 2) h
        simp [pow_succ, Nat.mul_mod, Nat.add_mod, op] at hm
    | succ a =>
      cases b with
      | zero =>
        have hm := congrArg (· % 2) h
        simp [pow_succ, Nat.mul_mod, Nat.add_mod, oq] at hm
      | succ b =>
        have hc : (2 ^ p - 1) * 2 ^ a + (2 ^ q - 1) * 2 ^ b =
            (2 ^ (p + q) - 1) * 2 ^ t := by
          simp only [pow_succ] at h
          nlinarith
        rcases ih a b hc with h | h <;> omega

/-- The actual numerical sum and allocated parent shifts for one graph step. -/
def ShiftedStep (offset cap : ℕ → ℕ) (p q : ℕ) : Prop :=
  ∃ a b : ℕ, a ≤ cap p ∧ b ≤ cap q ∧
    ((2 ^ p - 1) * 2 ^ offset p) * 2 ^ a +
      ((2 ^ q - 1) * 2 ^ offset q) * 2 ^ b =
        (2 ^ (p + q) - 1) * 2 ^ offset (p + q)

/-- Eliminate all exponentials before analysing the total allocation cost. -/
theorem shifted_step_constraints {offset cap : ℕ → ℕ} {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (h : ShiftedStep offset cap p q) :
    (offset p ≤ offset (p+q) + q ∧ offset q ≤ offset (p+q) ∧
      offset (p+q) + q ≤ offset p + cap p ∧ offset (p+q) ≤ offset q + cap q) ∨
    (offset p ≤ offset (p+q) ∧ offset q ≤ offset (p+q) + p ∧
      offset (p+q) ≤ offset p + cap p ∧ offset (p+q) + p ≤ offset q + cap q) := by
  obtain ⟨a, b, ha, hb, he⟩ := h
  have he' : (2 ^ p - 1) * 2 ^ (offset p + a) +
      (2 ^ q - 1) * 2 ^ (offset q + b) =
        (2 ^ (p + q) - 1) * 2 ^ offset (p + q) := by
    simpa only [pow_add, Nat.mul_assoc] using he
  rcases mersenne_sum_shifts hp hq _ _ _ he' with h | h <;> omega

set_option maxHeartbeats 4000000 in
/-- Even allowing EVERY base to be an arbitrarily shifted Mersenne cannot
attain the 108-doubling budget on this selected graph. The shifts are unbounded;
this is a linear-arithmetic proof after the general two-block lemma. -/
theorem shifted_mersenne_cost_ge_109 (offset cap : ℕ → ℕ)
    (hroot : offset 1 = 0) (hlast : offset 109 = 0)
    (hsteps : ∀ s ∈ selectedSteps, ShiftedStep offset cap s.1 s.2) :
    109 ≤ cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 := by
  have h2 := shifted_step_constraints (by decide : 0 < 1) (by decide : 0 < 1)
    (hsteps (1,1) (by decide))
  have h4 := shifted_step_constraints (by decide : 0 < 2) (by decide : 0 < 2)
    (hsteps (2,2) (by decide))
  have h5 := shifted_step_constraints (by decide : 0 < 4) (by decide : 0 < 1)
    (hsteps (4,1) (by decide))
  have h7 := shifted_step_constraints (by decide : 0 < 5) (by decide : 0 < 2)
    (hsteps (5,2) (by decide))
  have h8 := shifted_step_constraints (by decide : 0 < 4) (by decide : 0 < 4)
    (hsteps (4,4) (by decide))
  have h15 := shifted_step_constraints (by decide : 0 < 8) (by decide : 0 < 7)
    (hsteps (8,7) (by decide))
  have h23 := shifted_step_constraints (by decide : 0 < 15) (by decide : 0 < 8)
    (hsteps (15,8) (by decide))
  have h28 := shifted_step_constraints (by decide : 0 < 23) (by decide : 0 < 5)
    (hsteps (23,5) (by decide))
  have h51 := shifted_step_constraints (by decide : 0 < 28) (by decide : 0 < 23)
    (hsteps (28,23) (by decide))
  have h58 := shifted_step_constraints (by decide : 0 < 51) (by decide : 0 < 7)
    (hsteps (51,7) (by decide))
  have h109 := shifted_step_constraints (by decide : 0 < 58) (by decide : 0 < 51)
    (hsteps (58,51) (by decide))
  norm_num only at h2 h4 h5 h7 h8 h15 h23 h28 h51 h58 h109
  have hd2 : offset 1 ≤ offset 2 ∧ offset 2 + 1 ≤ offset 1 + cap 1 := by omega
  have hd4 : offset 2 ≤ offset 4 ∧ offset 4 + 2 ≤ offset 2 + cap 2 := by omega
  have hd8 : offset 4 ≤ offset 8 ∧ offset 8 + 4 ≤ offset 4 + cap 4 := by omega
  clear h2 h4 h8 hsteps
  grind

/-- An attained 109-cap allocation: shift just bases 5 and 28 by one. -/
def repairOffset (v : ℕ) : ℕ := if v = 5 ∨ v = 28 then 1 else 0

def repairCap : ℕ → ℕ
  | 1 => 1 | 2 => 2 | 4 => 4 | 5 => 1 | 8 => 15
  | 23 => 6 | 28 => 22 | 51 => 58 | _ => 0

theorem repair_shifted_steps :
    ∀ s ∈ selectedSteps, ShiftedStep repairOffset repairCap s.1 s.2 := by
  intro s hs
  simp only [selectedSteps, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, by decide, by decide, by decide⟩
  · exact ⟨2, 0, by decide, by decide, by decide⟩
  · exact ⟨2, 1, by decide, by decide, by decide⟩
  · exact ⟨1, 0, by decide, by decide, by decide⟩
  · exact ⟨4, 0, by decide, by decide, by decide⟩
  · exact ⟨7, 0, by decide, by decide, by decide⟩
  · exact ⟨0, 15, by decide, by decide, by decide⟩
  · exact ⟨6, 0, by decide, by decide, by decide⟩
  · exact ⟨22, 0, by decide, by decide, by decide⟩
  · exact ⟨7, 0, by decide, by decide, by decide⟩
  · exact ⟨0, 58, by decide, by decide, by decide⟩

theorem repair_endpoints : repairOffset 1 = 0 ∧ repairOffset 109 = 0 := by decide

theorem repair_cost :
    repairCap 1 + repairCap 2 + repairCap 4 + repairCap 5 + repairCap 7 +
    repairCap 8 + repairCap 15 + repairCap 23 + repairCap 28 + repairCap 51 +
    repairCap 58 = 109 := by decide

/-- Any budget-108 labelling needs a base that is not a shifted Mersenne.
This is a conditional obstruction for the selected graph, not for all chains. -/
theorem no_shifted_mersenne_budget_108 (offset cap : ℕ → ℕ)
    (hroot : offset 1 = 0) (hlast : offset 109 = 0)
    (hsteps : ∀ s ∈ selectedSteps, ShiftedStep offset cap s.1 s.2) :
    ¬ (cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) := by
  have := shifted_mersenne_cost_ge_109 offset cap hroot hlast hsteps
  omega

end ScholzBrauer.Clift109
