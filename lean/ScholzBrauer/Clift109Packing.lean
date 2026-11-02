import ScholzBrauer.Clift109Residues

/-! Packing bounds for dissociated boxes, before interval/cap classification. -/
namespace ScholzBrauer.CliftLabelling

theorem subsetSums_mem_le_sum (ds : List ℕ) :
    ∀ x ∈ subsetSums ds, x ≤ ds.sum := by
  induction ds with
  | nil => simp [subsetSums]
  | cons d ds ih =>
    intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · have := ih x hx
      simp only [List.sum_cons]
      omega
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      have := ih y hy
      simp only [List.sum_cons]
      omega

/-- A k-dimensional dissociated nonnegative box needs span at least 2^k-1. -/
theorem subsetSums_packing (ds : List ℕ) (h : (subsetSums ds).Nodup) :
    2 ^ ds.length ≤ ds.sum + 1 := by
  have hle : subsetSums ds ≤ Multiset.range (ds.sum + 1) := by
    apply (Multiset.le_iff_subset h).mpr
    intro x hx
    exact Multiset.mem_range.mpr (by have := subsetSums_mem_le_sum ds x hx; omega)
  have := Multiset.card_le_card hle
  simpa only [card_subsetSums, Multiset.card_range] using this

theorem subsetSums_sublist {xs ys : List ℕ} (h : xs.Sublist ys) :
    subsetSums xs ≤ subsetSums ys := by
  induction h with
  | slnil => exact le_rfl
  | cons a h ih => exact ih.trans (Multiset.le_add_right _ _)
  | cons₂ a h ih => exact add_le_add ih (Multiset.map_le_map ih)

/-- The four retained dimensions consume at least fifteen units of span. -/
theorem six_box_pair_packing (x₁ x₂ x₃ x₄ x₅ x₆ offset : ℕ)
    (h : (subsetSums [x₁,x₂,x₃,x₄,x₅,x₆]).Nodup)
    (hb : offset + [x₁,x₂,x₃,x₄,x₅,x₆].sum ≤ 108) :
    offset ≤ 45 ∧ offset + x₁ + x₆ ≤ 93 := by
  have hall := subsetSums_packing _ h
  have hs : ([x₂,x₃,x₄,x₅] : List ℕ).Sublist [x₁,x₂,x₃,x₄,x₅,x₆] := by
    exact .cons _ (.cons₂ _ (.cons₂ _ (.cons₂ _ (.cons₂ _ (.cons _ .slnil)))))
  have hfour := subsetSums_packing _ (Multiset.nodup_of_le (subsetSums_sublist hs) h)
  simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at *
  norm_num at hall hfour
  omega

end ScholzBrauer.CliftLabelling

namespace ScholzBrauer.Clift109
open CliftLabelling

/-- Necessary packing bounds for every budget-108 labelling. -/
theorem box_pair_packing_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    pairOffset (boxPairs a b) ≤ 45 ∧
    pairOffset (boxPairs a b) + pairGap (a 58 + a 109, b 109) +
      pairGap (a 2, b 2) ≤ 93 := by
  have h := box_constraints_of_budget B a b cap h1 hsteps hcap h109 hbudget
  exact six_box_pair_packing _ _ _ _ _ _ _ h.2.1 h.2.2.2.2

private theorem pairGap_cast (x y : ℕ) :
    ((pairGap (x,y) : ℕ) : ℤ) = |(x : ℤ) - y| := by
  rcases le_total x y with h | h
  · simp [pairGap, max_eq_right h, min_eq_left h,
      abs_of_nonpos (show (x : ℤ) - y ≤ 0 by omega)]
    omega
  · simp [pairGap, max_eq_left h, min_eq_right h,
      abs_of_nonneg (show 0 ≤ (x : ℤ) - y by omega)]
    omega

/-- The residue domain has a gap between 29 and 51. -/
theorem residueSteps_gap (d : ℤ) (h : d ∈ residueSteps) : d ≤ 29 ∨ 51 ≤ d := by
  simp [residueSteps] at h
  omega

/-- Joint restriction: at least one halving step is at most 29. Both steps
remain in the proved 27-value domain; the bound does not assert feasibility. -/
theorem joint_steps_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    c.u ∈ residueSteps ∧ c.d1 ∈ residueSteps ∧ c.u ≠ c.d1 ∧
      c.u + c.d1 ≤ 93 ∧ min c.u c.d1 ≤ 29 := by
  dsimp only
  have hr := residue_steps_of_budget B a b cap h1 hsteps hcap h109 hbudget
  have hp := box_pair_packing_of_budget B a b cap h1 hsteps hcap h109 hbudget
  have hd := (box_constraints_of_budget B a b cap h1 hsteps hcap h109 hbudget).2.2.1
  have hne : pairGap (a 58 + a 109, b 109) ≠ pairGap (a 2, b 2) := by
    simp [boxPairs] at hd
    tauto
  have hg1 := pairGap_cast (a 2) (b 2)
  have hg2 := pairGap_cast (a 58 + a 109) (b 109)
  have hu := residueSteps_gap _ hr.1
  have hv := residueSteps_gap _ hr.2.1
  refine ⟨hr.1, hr.2.1, ?_, ?_, ?_⟩ <;>
    simp only [minimumCoordinates, Nat.cast_add] at * <;> omega

end ScholzBrauer.Clift109
