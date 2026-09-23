import ScholzBrauer.Certificate

/-! Checked Hansen underlining of source values. The initial value is marked;
each subsequent `(value, mark)` must use the latest marked value as a summand.
The last source value must be marked. This formalises the criterion described
by Clift, https://www.additionchains.com/ScholzBrauer.html (2026-09-24).
It does not yet construct the shifted Mersenne nodes of the Hansen lift. -/
namespace ScholzBrauer

abbrev MarkedStep := ℕ × Bool

/-- A marking certificate over values, with existential choice of the other
summand. The empty case enforces a marked endpoint, including source `[1]`. -/
def IsHansenFrom (source : List ℕ) (anchor : ℕ) : List MarkedStep → Prop
  | [] => source.getLast? = some anchor
  | (v, mark) :: rest =>
      anchor ∈ source ∧ (∃ b ∈ source, v = anchor + b) ∧
      (∀ x ∈ source, x < v) ∧
      IsHansenFrom (source ++ [v]) (if mark then v else anchor) rest

instance (source : List ℕ) (anchor : ℕ) (steps : List MarkedStep) :
    Decidable (IsHansenFrom source anchor steps) := by
  induction steps generalizing source anchor with
  | nil => unfold IsHansenFrom; infer_instance
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    unfold IsHansenFrom
    have := ih (source ++ [v]) (if mark then v else anchor)
    infer_instance

def hansenSourceFrom (source : List ℕ) : List MarkedStep → List ℕ
  | [] => source
  | (v, _) :: rest => hansenSourceFrom (source ++ [v]) rest

def hansenAnchorFrom (anchor : ℕ) : List MarkedStep → ℕ
  | [] => anchor
  | (v, mark) :: rest => hansenAnchorFrom (if mark then v else anchor) rest

/-- Marked values in order, including the initial anchor exactly once. -/
def hansenMarksFrom (anchor : ℕ) : List MarkedStep → List ℕ
  | [] => [anchor]
  | (v, true) :: rest => anchor :: hansenMarksFrom v rest
  | (_, false) :: rest => hansenMarksFrom anchor rest

/-- Source replay certificate, not the Mersenne lift certificate. -/
def hansenPairsFrom (anchor : ℕ) : List MarkedStep → List Step
  | [] => []
  | (v, mark) :: rest =>
      (anchor, v - anchor) :: hansenPairsFrom (if mark then v else anchor) rest

theorem hansenSourceFrom_length (source : List ℕ) (steps : List MarkedStep) :
    (hansenSourceFrom source steps).length = source.length + steps.length := by
  induction steps generalizing source with
  | nil => simp [hansenSourceFrom]
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    simp only [hansenSourceFrom, ih, List.length_append, List.length_cons, List.length_nil]
    omega

theorem hansenPairsFrom_length (anchor : ℕ) (steps : List MarkedStep) :
    (hansenPairsFrom anchor steps).length = steps.length := by
  induction steps generalizing anchor with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    simp [hansenPairsFrom, ih]

/-- The checker generates a successful ordinary source certificate. Natural
subtraction is justified by the checked sum, never by truncated subtraction. -/
theorem hansenPairsFrom_replay {source : List ℕ} {anchor : ℕ}
    {steps : List MarkedStep} (h : IsHansenFrom source anchor steps) :
    replayFrom source (hansenPairsFrom anchor steps) =
      some (hansenSourceFrom source steps) := by
  induction steps generalizing source anchor with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    obtain ⟨ha, ⟨b, hb, hv⟩, hgt, hrest⟩ := h
    have hsub : v - anchor = b := by omega
    have he : extend source (anchor, v - anchor) = some (source ++ [v]) := by
      rw [hsub]
      unfold extend
      simp only [hv]
      rw [if_pos ⟨ha, hb, by simpa [hv] using hgt⟩]
    simpa only [hansenPairsFrom, hansenSourceFrom, replayFrom, he,
      Option.bind_some] using ih hrest

theorem hansenSourceFrom_valid {source : List ℕ} {anchor : ℕ}
    {steps : List MarkedStep} (hs : IsAdditionChain source)
    (h : IsHansenFrom source anchor steps) :
    IsAdditionChain (hansenSourceFrom source steps) :=
  replayFrom_sound hs (hansenPairsFrom_replay h)

/-- The carried anchor is exactly the latest marked value, regardless of
whether the proposed source is accepted. -/
theorem hansenAnchorFrom_latest (anchor : ℕ) (steps : List MarkedStep) :
    (hansenMarksFrom anchor steps).getLast? = some (hansenAnchorFrom anchor steps) := by
  induction steps generalizing anchor with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    cases mark with
    | false => simpa [hansenMarksFrom, hansenAnchorFrom] using ih anchor
    | true =>
      simp only [hansenMarksFrom, hansenAnchorFrom, ↓reduceIte,
        List.getLast?_cons, ih v, Option.getD_some]

/-- Accepted completion ends precisely at its final marked anchor. -/
theorem hansenSourceFrom_endpoint {source : List ℕ} {anchor : ℕ}
    {steps : List MarkedStep} (h : IsHansenFrom source anchor steps) :
    (hansenSourceFrom source steps).getLast? = some (hansenAnchorFrom anchor steps) := by
  induction steps generalizing source anchor with
  | nil => exact h
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    exact ih h.2.2.2

/-- Every marked value survives in the source. The carried anchor is its
largest marked value; strict source growth is essential for this implication. -/
theorem hansenMarksFrom_stored_max {source : List ℕ} {anchor : ℕ}
    {steps : List MarkedStep} (ha : anchor ∈ source)
    (h : IsHansenFrom source anchor steps) :
    anchor ≤ hansenAnchorFrom anchor steps ∧
      ∀ m ∈ hansenMarksFrom anchor steps,
        m ∈ hansenSourceFrom source steps ∧ m ≤ hansenAnchorFrom anchor steps := by
  induction steps generalizing source anchor with
  | nil => simpa [hansenAnchorFrom, hansenMarksFrom, hansenSourceFrom] using ha
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    have hkeep : source ⊆ hansenSourceFrom (source ++ [v]) rest := by
      clear h ih ha
      induction rest generalizing source v with
      | nil => exact List.subset_append_left _ _
      | cons t ts iht =>
        obtain ⟨w, flag⟩ := t
        exact fun x hx => iht w (List.mem_append_left _ hx)
    cases mark with
    | false =>
      exact ih (List.mem_append_left _ ha) h.2.2.2
    | true =>
      obtain ⟨hle, hm⟩ := ih (by simp : v ∈ source ++ [v]) h.2.2.2
      have hav : anchor < v := h.2.2.1 anchor ha
      refine ⟨by simpa [hansenAnchorFrom] using le_trans (le_of_lt hav) hle, ?_⟩
      intro m hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨hkeep ha, by simpa [hansenAnchorFrom] using le_trans (le_of_lt hav) hle⟩
      · exact hm m hmem

/-- Splitting an accepted certificate at any point preserves validity of the
remaining checks and availability of the current anchor in the prefix. -/
theorem hansenFrom_split {source : List ℕ} {anchor : ℕ}
    (pre suffix : List MarkedStep) (ha : anchor ∈ source)
    (h : IsHansenFrom source anchor (pre ++ suffix)) :
    IsHansenFrom (hansenSourceFrom source pre)
      (hansenAnchorFrom anchor pre) suffix ∧
    hansenAnchorFrom anchor pre ∈ hansenSourceFrom source pre := by
  induction pre generalizing source anchor with
  | nil => exact ⟨h, ha⟩
  | cons s rest ih =>
    obtain ⟨v, mark⟩ := s
    have hnext : (if mark then v else anchor) ∈ source ++ [v] := by
      cases mark <;> simp [ha]
    exact ih hnext h.2.2.2

/-- At every cut before a next step, the latest actual mark is available and
is a summand of that step. This connects the carried state to the marking list. -/
theorem hansen_latest_anchor_step {source : List ℕ} {anchor v : ℕ} {mark : Bool}
    (pre rest : List MarkedStep) (ha : anchor ∈ source)
    (h : IsHansenFrom source anchor (pre ++ (v, mark) :: rest)) :
    ∃ a, (hansenMarksFrom anchor pre).getLast? = some a ∧
      a ∈ hansenSourceFrom source pre ∧
      ∃ b ∈ hansenSourceFrom source pre, v = a + b := by
  obtain ⟨hnext, hmem⟩ := hansenFrom_split pre ((v, mark) :: rest) ha h
  exact ⟨_, hansenAnchorFrom_latest anchor pre, hmem, hnext.2.1⟩

/-- For a nonempty accepted certificate, endpoint equality really forces the
final flag to be true; it cannot be satisfied by retaining an older mark. -/
theorem hansen_final_mark {source : List ℕ} {anchor v : ℕ} {mark : Bool}
    (pre : List MarkedStep) (ha : anchor ∈ source)
    (h : IsHansenFrom source anchor (pre ++ [(v, mark)])) : mark = true := by
  obtain ⟨hnext, _⟩ := hansenFrom_split pre [(v, mark)] ha h
  have hgt := hnext.2.2.1 _ hnext.1
  have hfinish := hnext.2.2.2
  cases mark with
  | true => rfl
  | false =>
    have he : v = hansenAnchorFrom anchor pre := by
      simpa [IsHansenFrom] using hfinish
    omega

-- Boundary checks and invalid markings: neither a future summand nor an
-- unmarked final value may pass. The initial value 1 is marked implicitly.
example : IsHansenFrom [1] 1 [] := by decide
example : IsHansenFrom [1] 1 [(2, true), (3, true)] := by decide
example : ¬ IsHansenFrom [1] 1 [(2, false)] := by decide
example : ¬ IsHansenFrom [1] 1 [(3, true)] := by decide
example : ¬ IsHansenFrom [1] 1 [(2, true), (2, true)] := by decide
example : ¬ IsHansenFrom [1] 1 [(0, true)] := by decide
example : ¬ IsHansenFrom [1] 1 [(2, false), (4, true)] := by decide
-- Marking 13 would make the subsequent non-star step 24 invalid.
example : ¬ IsHansenFrom [1] 1
    [(2, true), (4, false), (6, true), (12, true), (13, true), (24, true)] := by decide
-- This valid marking keeps 8 as anchor through 9 and 12, then marks 17.
example : IsHansenFrom [1] 1
    [(2, true), (4, true), (8, true), (9, false), (12, false),
     (17, true), (29, true)] := by decide

end ScholzBrauer
