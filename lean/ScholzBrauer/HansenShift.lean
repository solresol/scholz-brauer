import ScholzBrauer.Hansen

/-! The shift budget for a Hansen lift. A step `v = anchor + b` consumes
`2^b * (2^anchor - 1)`, so the anchor must store every doubling through `b`.
The demands stop at the next mark (including the step that creates it).
For accepted sources their maximum is the difference between successive marks.
This file proves the budget, not existence or sorted replay of lifted nodes. -/
namespace ScholzBrauer

/-- Shift requests to the current anchor, through the next marked step. -/
def hansenShiftDemands (anchor : ℕ) : List MarkedStep → List ℕ
  | [] => []
  | (v, true) :: _ => [v - anchor]
  | (v, false) :: rest => (v - anchor) :: hansenShiftDemands anchor rest

/-- The next marked value, or the current anchor when no further mark exists. -/
def hansenNextMark (anchor : ℕ) : List MarkedStep → ℕ
  | [] => anchor
  | (v, true) :: _ => v
  | (_, false) :: rest => hansenNextMark anchor rest

/-- An executable maximum of the requests, with zero for the final anchor. -/
def hansenShiftMax (anchor : ℕ) (steps : List MarkedStep) : ℕ :=
  (hansenShiftDemands anchor steps).foldr max 0

/-- One proposed shift cap per marked value, including final cap zero.
Correctness as a maximum, rather than just a gap count, is proved below. -/
def hansenShiftCaps (anchor : ℕ) : List MarkedStep → List ℕ
  | [] => [0]
  | (v, true) :: rest => (v - anchor) :: hansenShiftCaps v rest
  | (_, false) :: rest => hansenShiftCaps anchor rest

/-- Every already stored source value precedes the next mark. In the empty
case acceptance identifies the endpoint with the current anchor. -/
theorem hansenNextMark_bounds_prefix {source : List ℕ} {anchor : ℕ}
    {steps : List MarkedStep} (hs : IsAdditionChain source)
    (h : IsHansenFrom source anchor steps) :
    ∀ x ∈ source, x ≤ hansenNextMark anchor steps := by
  induction steps generalizing source anchor with
  | nil =>
    have hlast : source.getLast? = some anchor := h
    have hne : source ≠ [] := by rintro rfl; simp at hlast
    have heq : source.getLast hne = anchor := by
      rw [List.getLast?_eq_some_getLast (h := hne)] at hlast
      exact Option.some.inj hlast
    intro x hx
    simpa [hansenNextMark, heq] using (hs.2.1.imp le_of_lt).rel_getLast hx
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    cases mark with
    | true => exact fun x hx => le_of_lt (h.2.2.1 x hx)
    | false =>
      obtain ⟨b, hb, hv⟩ := h.2.1
      have hs' : IsAdditionChain (source ++ [v]) := by
        rw [hv]
        exact append_sum hs h.1 hb (by simpa [hv] using h.2.2.1)
      exact fun x hx => ih hs' h.2.2.2 x (List.mem_append_left _ hx)

/-- The demand maximum is attained at the next marked step: all intervening
unmarked values are smaller. The terminal anchor has maximum zero. -/
theorem hansenShiftMax_eq_gap {source : List ℕ} {anchor : ℕ}
    {steps : List MarkedStep} (hs : IsAdditionChain source)
    (h : IsHansenFrom source anchor steps) :
    hansenShiftMax anchor steps = hansenNextMark anchor steps - anchor := by
  induction steps generalizing source anchor with
  | nil => simp [hansenShiftMax, hansenShiftDemands, hansenNextMark]
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    cases mark with
    | true => simp [hansenShiftMax, hansenShiftDemands, hansenNextMark]
    | false =>
      obtain ⟨b, hb, hv⟩ := h.2.1
      have hs' : IsAdditionChain (source ++ [v]) := by
        rw [hv]
        exact append_sum hs h.1 hb (by simpa [hv] using h.2.2.1)
      have hbound := hansenNextMark_bounds_prefix hs' h.2.2.2 v (by simp)
      have hi := ih hs' h.2.2.2
      simp only [Bool.false_eq_true, ↓reduceIte] at hi hbound
      change max (v - anchor) (hansenShiftMax anchor rest) =
        hansenNextMark anchor rest - anchor
      rw [hi, max_eq_right (by omega)]

/-- Each requested shift is at most the proved maximum. -/
theorem hansenShiftDemands_le_max (anchor : ℕ) (steps : List MarkedStep)
    {b : ℕ} (hb : b ∈ hansenShiftDemands anchor steps) :
    b ≤ hansenShiftMax anchor steps := by
  unfold hansenShiftMax
  generalize hansenShiftDemands anchor steps = demands at *
  induction demands with
  | nil => simp at hb
  | cons a rest ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact le_max_left _ _
    · exact le_trans (ih hb) (le_max_right _ _)

/-- The first planned cap really is the maximum over all consumers of the
current anchor; dropping unmarked entries from the cap plan loses no demand. -/
theorem hansenShiftCaps_head {source : List ℕ} {anchor : ℕ}
    {steps : List MarkedStep} (hs : IsAdditionChain source)
    (h : IsHansenFrom source anchor steps) :
    (hansenShiftCaps anchor steps).head? = some (hansenShiftMax anchor steps) := by
  rw [hansenShiftMax_eq_gap hs h]
  clear hs h
  induction steps generalizing anchor with
  | nil => simp [hansenShiftCaps, hansenNextMark]
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    cases mark <;> simp [hansenShiftCaps, hansenNextMark, ih]

/-- Caps and marked source values align one for one. Unmarked source values
need no shifted copies; their base Mersenne node is counted separately. -/
theorem hansenShiftCaps_length (anchor : ℕ) (steps : List MarkedStep) :
    (hansenShiftCaps anchor steps).length = (hansenMarksFrom anchor steps).length := by
  induction steps generalizing anchor with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    cases mark <;> simp [hansenShiftCaps, hansenMarksFrom, ih]

/-- The shift caps telescope. No optimal-source hypothesis is needed. -/
theorem hansenShiftCaps_telescope {source : List ℕ} {anchor : ℕ}
    {steps : List MarkedStep} (ha : anchor ∈ source)
    (h : IsHansenFrom source anchor steps) :
    (hansenShiftCaps anchor steps).sum + anchor = hansenAnchorFrom anchor steps := by
  induction steps generalizing source anchor with
  | nil => simp [hansenShiftCaps, hansenAnchorFrom]
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    cases mark with
    | false => exact ih (List.mem_append_left _ ha) h.2.2.2
    | true =>
      have hav : anchor < v := h.2.2.1 anchor ha
      have hi := ih (by simp : v ∈ source ++ [v]) h.2.2.2
      simp only [hansenShiftCaps, List.sum_cons, hansenAnchorFrom, ↓reduceIte]
      omega

/-- Starting at 1, the planned doublings total exactly `n - 1`. -/
theorem hansenShiftCaps_sum {steps : List MarkedStep} {n : ℕ}
    (h : IsHansenFrom [1] 1 steps)
    (hn : hansenAnchorFrom 1 steps = n) :
    (hansenShiftCaps 1 steps).sum = n - 1 := by
  have ht := hansenShiftCaps_telescope (by simp : 1 ∈ [1]) h
  omega

/-- The budget for shifted nodes is `n - 1 + r` additions, provided a later
construction proves distinctness and valid replay of those nodes. This is a
count identity only; it does not assert existence of that addition chain. -/
theorem hansenShiftCaps_budget {steps : List MarkedStep} {n : ℕ}
    (h : IsHansenFrom [1] 1 steps)
    (hn : hansenAnchorFrom 1 steps = n) :
    (hansenShiftCaps 1 steps).sum + steps.length = n - 1 + steps.length := by
  rw [hansenShiftCaps_sum h hn]

-- The singleton source allocates no shifted copies.
example : hansenShiftCaps 1 [] = [0] := by decide
example : hansenShiftMax 1 [] = 0 := by decide
-- Retain anchor 12 across 13; the consumer 24 sets the maximum, not 13.
example : hansenShiftDemands 12 [(13, false), (24, true)] = [1, 12] := by decide
example : hansenShiftMax 12 [(13, false), (24, true)] = 12 := by decide
-- Clift's 29 example: the demands on 8 are 1, 4 and 9.
example : hansenShiftCaps 1
    [(2, true), (4, true), (8, true), (9, false), (12, false),
     (17, true), (29, true)] = [1, 2, 4, 9, 12, 0] := by decide
-- Without acceptance, a decreasing request can exceed the next-mark gap.
example : hansenShiftMax 2 [(9, false), (4, true)] = 7 := by decide
example : hansenNextMark 2 [(9, false), (4, true)] - 2 = 2 := by decide
example : ¬ IsHansenFrom [1, 2] 2 [(9, false), (4, true)] := by decide

end ScholzBrauer
