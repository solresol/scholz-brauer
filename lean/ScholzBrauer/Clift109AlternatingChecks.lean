import ScholzBrauer.Clift109AlternatingChecks04
import ScholzBrauer.Clift109AlternatingChecks05
import ScholzBrauer.Clift109AlternatingChecks06
import ScholzBrauer.Clift109AlternatingChecks07
import ScholzBrauer.Clift109AlternatingChecks08
import ScholzBrauer.Clift109AlternatingChecks11
import ScholzBrauer.Clift109AlternatingChecks13
import ScholzBrauer.Clift109AlternatingChecks14
import ScholzBrauer.Clift109AlternatingChecks17
import ScholzBrauer.Clift109AlternatingChecks18
import ScholzBrauer.Clift109AlternatingChecks19
import ScholzBrauer.Clift109AlternatingChecks26
import ScholzBrauer.Clift109AlternatingChecks27
import ScholzBrauer.Clift109AlternatingChecks28
import ScholzBrauer.Clift109AlternatingChecks29
import ScholzBrauer.Clift109AlternatingChecks53
import ScholzBrauer.Clift109AlternatingChecks54
import ScholzBrauer.Clift109AlternatingChecks55
import ScholzBrauer.Clift109AlternatingChecks56

/-! Every finite removal is kernel checked. Survivors need not be feasible. -/

namespace ScholzBrauer.Clift109

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def alternatingRejectedDirections : List (ℤ × ℤ) :=
  [(7, 6), (7, 8), (8, 7), (8, 9), (8, 55), (13, 11), (13, 14), (14, 4), (14, 5), (14, 13), (17, 18), (17, 19), (17, 53), (17, 54), (17, 55), (19, 17), (19, 18), (19, 54), (19, 55), (19, 56), (26, 27), (26, 28), (26, 29), (28, 9), (28, 26), (28, 27), (28, 29), (29, 26), (29, 27), (29, 28), (53, 17), (53, 18), (56, 18), (56, 19)]

def alternatingDisjointPairs : List (ℤ × ℤ) :=
  [(4, 27), (5, 54), (6, 55), (8, 54), (11, 18), (11, 54), (18, 55)]

theorem alternatingRejectedDirections_checked (p : ℤ × ℤ)
    (hp : p ∈ alternatingRejectedDirections) (s : ℤ) (hs : 0 ≤ s ∧ s < 109) :
    ¬intervalThreePairPlacement p.1 p.2 s := by
  simp only [alternatingRejectedDirections, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_7_6 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_7_8 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_8_7 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_8_9 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_8_55 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_13_11 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_13_14 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_14_4 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_14_5 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_14_13 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_17_18 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_17_19 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_17_53 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_17_54 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_17_55 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_19_17 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_19_18 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_19_54 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_19_55 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_19_56 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_26_27 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_26_28 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_26_29 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_28_9 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_28_26 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_28_27 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_28_29 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_29_26 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_29_27 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_29_28 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_53_17 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_53_18 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_56_18 s hs h
  · intro h
    simpa only [List.not_mem_nil] using alternating_allowed_56_19 s hs h

theorem alternatingDisjointPairs_checked (p : ℤ × ℤ)
    (hp : p ∈ alternatingDisjointPairs) (s : ℤ) (hs : 0 ≤ s ∧ s < 109) :
    ¬(intervalThreePairPlacement p.1 p.2 s ∧ intervalThreePairPlacement p.2 p.1 s) := by
  simp only [alternatingDisjointPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro h
    have ha := alternating_allowed_4_27 s hs h.1
    have hb := alternating_allowed_27_4 s hs h.2
    have hd : ∀ i ∈ ([1, 3, 9, 11, 17, 19, 25, 27, 33, 35, 41, 43, 49, 51, 57, 59, 65, 67, 73, 75, 81, 83, 89, 91, 97, 99, 105, 107] : List ℕ), i ∉ ([15, 23, 31, 39, 69, 77, 85, 93] : List ℕ) := by
      decide +kernel
    exact hd s.toNat ha hb
  · intro h
    have ha := alternating_allowed_5_54 s hs h.1
    have hb := alternating_allowed_54_5 s hs h.2
    have hd : ∀ i ∈ ([1, 3, 5, 7, 11, 13, 15, 17, 21, 23, 25, 27, 31, 33, 35, 37, 41, 43, 45, 47, 51, 53, 55, 57, 61, 63, 65, 67, 71, 73, 75, 77, 81, 83, 85, 87, 91, 93, 95, 97, 101, 103, 105, 107] : List ℕ), i ∉ ([39, 49, 59, 69] : List ℕ) := by
      decide +kernel
    exact hd s.toNat ha hb
  · intro h
    have ha := alternating_allowed_6_55 s hs h.1
    have hb := alternating_allowed_55_6 s hs h.2
    have hd : ∀ i ∈ ([1, 3, 9, 11, 13, 15, 21, 23, 25, 27, 33, 35, 37, 39, 45, 47, 49, 51, 57, 59, 61, 63, 69, 71, 73, 75, 81, 83, 85, 87, 93, 95, 97, 99, 105, 107] : List ℕ), i ∉ ([5, 17, 91, 103] : List ℕ) := by
      decide +kernel
    exact hd s.toNat ha hb
  · intro h
    have ha := alternating_allowed_8_54 s hs h.1
    have hb := alternating_allowed_54_8 s hs h.2
    have hd : ∀ i ∈ ([6, 22, 38, 54, 70, 86, 102] : List ℕ), i ∉ ([30, 46, 62, 78] : List ℕ) := by
      decide +kernel
    exact hd s.toNat ha hb
  · intro h
    have ha := alternating_allowed_11_18 s hs h.1
    have hb := alternating_allowed_18_11 s hs h.2
    have hd : ∀ i ∈ ([3, 9, 11, 17, 25, 31, 33, 39, 47, 53, 55, 61, 69, 75, 77, 83, 91, 97, 99, 105] : List ℕ), i ∉ ([7, 15, 21, 29, 43, 51, 57, 65, 79, 87, 93, 101] : List ℕ) := by
      decide +kernel
    exact hd s.toNat ha hb
  · intro h
    have ha := alternating_allowed_11_54 s hs h.1
    have hb := alternating_allowed_54_11 s hs h.2
    have hd : ∀ i ∈ ([7, 9, 11, 13, 29, 31, 33, 35, 51, 53, 55, 57, 73, 75, 77, 79, 95, 97, 99, 101] : List ℕ), i ∉ ([21, 43, 65, 87] : List ℕ) := by
      decide +kernel
    exact hd s.toNat ha hb
  · intro h
    have ha := alternating_allowed_18_55 s hs h.1
    have hb := alternating_allowed_55_18 s hs h.2
    have hd : ∀ i ∈ ([1, 3, 33, 35, 37, 39, 69, 71, 73, 75, 105, 107] : List ℕ), i ∉ ([17, 53, 55, 91] : List ℕ) := by
      decide +kernel
    exact hd s.toNat ha hb

end ScholzBrauer.Clift109
