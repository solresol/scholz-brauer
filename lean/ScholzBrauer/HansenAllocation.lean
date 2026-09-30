import ScholzBrauer.HansenShift
import ScholzBrauer.HansenNodes

/-! Finite Hansen allocation. Labels are grouped by marked intervals, not
numerically ordered. An unmarked source contributes just its base; a marked
anchor contributes every shift through the gap to the next mark. -/
namespace ScholzBrauer

/-- All shifts of one exponent, including its base. -/
def hansenRow (a cap : ℕ) : List (ℕ × ℕ) :=
  (List.range (cap + 1)).map (fun k => (a, k))

@[simp] theorem mem_hansenRow {a cap : ℕ} {p : ℕ × ℕ} :
    p ∈ hansenRow a cap ↔ p.1 = a ∧ p.2 ≤ cap := by
  simp [hansenRow, List.mem_map, Prod.ext_iff, Nat.lt_succ_iff, eq_comm, and_comm]

/-- Allocate each source base exactly once, and all marked-anchor shifts.
Unmarked bases precede their anchor row in this list; sorting is a later step. -/
def hansenLabels (a : ℕ) : List MarkedStep → List (ℕ × ℕ)
  | [] => [(a, 0)]
  | (v, false) :: rest => (v, 0) :: hansenLabels a rest
  | (v, true) :: rest => hansenRow a (v - a) ++ hansenLabels v rest

theorem hansenLabels_anchor (a : ℕ) (steps : List MarkedStep) {k : ℕ}
    (hk : k ≤ hansenNextMark a steps - a) :
    (a, k) ∈ hansenLabels a steps := by
  induction steps generalizing a with
  | nil => simpa [hansenNextMark, hansenLabels] using hk
  | cons s rest ih =>
    obtain ⟨v, flag⟩ := s
    cases flag with
    | false => exact List.mem_cons_of_mem _ (ih a hk)
    | true => exact List.mem_append_left _ (mem_hansenRow.mpr ⟨rfl, hk⟩)

theorem hansenLabels_base (a : ℕ) (steps : List MarkedStep) :
    (a, 0) ∈ hansenLabels a steps := hansenLabels_anchor a steps (Nat.zero_le _)

theorem hansenLabels_tail (a v : ℕ) (flag : Bool) (rest : List MarkedStep) :
    hansenLabels (if flag then v else a) rest ⊆ hansenLabels a ((v, flag) :: rest) := by
  cases flag
  · exact fun _ hp => List.mem_cons_of_mem _ hp
  · exact List.subset_append_right _ _

/-- Allocation is downward closed in the shift coordinate. -/
theorem hansenLabels_downward {a b k l : ℕ} {steps : List MarkedStep}
    (hp : (b, k) ∈ hansenLabels a steps) (hl : l ≤ k) :
    (b, l) ∈ hansenLabels a steps := by
  induction steps generalizing a with
  | nil => simp only [hansenLabels, List.mem_singleton, Prod.mk.injEq] at hp ⊢; omega
  | cons s rest ih =>
    obtain ⟨v, flag⟩ := s
    cases flag with
    | false =>
      rcases List.mem_cons.mp hp with he | ht
      · have he' := Prod.mk.inj he
        simp only at he'
        have : l = 0 := by omega
        simp [hansenLabels, he'.1, this]
      · exact List.mem_cons_of_mem _ (ih ht)
    | true =>
      rcases List.mem_append.mp hp with hr | ht
      · have hr' := mem_hansenRow.mp hr
        exact List.mem_append_left _ (mem_hansenRow.mpr ⟨hr'.1, le_trans hl hr'.2⟩)
      · exact List.mem_append_right _ (ih ht)

/-- The actual allocated list has the previously proved shift budget. -/
theorem hansenLabels_length (a : ℕ) (steps : List MarkedStep) :
    (hansenLabels a steps).length = steps.length + (hansenShiftCaps a steps).sum + 1 := by
  induction steps generalizing a with
  | nil => simp [hansenLabels, hansenShiftCaps]
  | cons s rest ih =>
    obtain ⟨v, flag⟩ := s
    cases flag <;> simp [hansenLabels, hansenRow, hansenShiftCaps, ih] <;> omega

/-- Source bases already stored or subsequently created occur in the union
of the prefix bases and the allocated continuation. -/
theorem hansenLabels_source_base {source : List ℕ} {a x : ℕ} {steps : List MarkedStep}
    (hx : x ∈ hansenSourceFrom source steps) :
    x ∈ source ∨ (x, 0) ∈ hansenLabels a steps := by
  induction steps generalizing source a with
  | nil => exact Or.inl hx
  | cons s rest ih =>
    obtain ⟨v, flag⟩ := s
    rcases ih (a := if flag then v else a) hx with hp | ht
    · rcases List.mem_append.mp hp with hp | hv
      · exact Or.inl hp
      · have hxv := List.mem_singleton.mp hv
        subst x
        cases flag with
        | false => exact Or.inr (List.mem_cons_self ..)
        | true => exact Or.inr (List.mem_append_right _ (hansenLabels_base v rest))
    · exact Or.inr (hansenLabels_tail a v flag rest ht)

/-- Labels use the current anchor or a newly created source value. -/
theorem hansenLabels_exponent {source : List ℕ} {a : ℕ} {steps : List MarkedStep}
    {p : ℕ × ℕ} (h : IsHansenFrom source a steps)
    (hp : p ∈ hansenLabels a steps) :
    p.1 = a ∨ (p.1 ∈ hansenSourceFrom source steps ∧ ∀ x ∈ source, x < p.1) := by
  induction steps generalizing source a with
  | nil => have := List.mem_singleton.mp hp; subst p; exact Or.inl rfl
  | cons s rest ih =>
    obtain ⟨v, flag⟩ := s
    have keep : ∀ x ∈ source ++ [v], x ∈ hansenSourceFrom (source ++ [v]) rest := by
      intro x hx
      clear h hp ih
      induction rest generalizing source v with
      | nil => exact hx
      | cons t ts iht => exact iht t.1 (List.mem_append_left _ hx)
    cases flag with
    | false =>
      rcases List.mem_cons.mp hp with he | ht
      · subst p
        exact Or.inr ⟨keep v (by simp), h.2.2.1⟩
      · rcases ih h.2.2.2 ht with he | ⟨hm, hg⟩
        · exact Or.inl he
        · exact Or.inr ⟨hm, fun x hx => hg x (List.mem_append_left _ hx)⟩
    | true =>
      rcases List.mem_append.mp hp with hr | ht
      · exact Or.inl (mem_hansenRow.mp hr).1
      · rcases ih h.2.2.2 ht with he | ⟨hm, hg⟩
        · exact Or.inr ⟨he ▸ keep v (by simp), fun x hx => he ▸ h.2.2.1 x hx⟩
        · exact Or.inr ⟨hm, fun x hx => hg x (List.mem_append_left _ hx)⟩

/-- Every allocated exponent is positive. -/
theorem hansenLabels_positive {source : List ℕ} {a : ℕ} {steps : List MarkedStep}
    (hs : IsAdditionChain source) (ha : a ∈ source) (h : IsHansenFrom source a steps) :
    ∀ p ∈ hansenLabels a steps, 0 < p.1 := by
  intro p hp
  rcases hansenLabels_exponent h hp with he | ⟨hm, _⟩
  · have := hs.one_le_of_mem ha; omega
  · exact (hansenSourceFrom_valid hs h).one_le_of_mem hm

/-- No label is allocated twice, even when anchor rows span unmarked entries. -/
theorem hansenLabels_nodup {source : List ℕ} {a : ℕ} {steps : List MarkedStep}
    (ha : a ∈ source) (h : IsHansenFrom source a steps) :
    (hansenLabels a steps).Nodup := by
  induction steps generalizing source a with
  | nil => simp [hansenLabels]
  | cons s rest ih =>
    obtain ⟨v, flag⟩ := s
    have hav : a < v := h.2.2.1 a ha
    cases flag with
    | false =>
      refine List.nodup_cons.mpr ⟨?_, ih (List.mem_append_left _ ha) h.2.2.2⟩
      intro hp
      rcases hansenLabels_exponent h.2.2.2 hp with he | ⟨_, hg⟩
      · simp only [Bool.false_eq_true, ↓reduceIte] at he; omega
      · have := hg v (by simp); omega
    | true =>
      apply List.nodup_append.mpr
      refine ⟨?_, ih (by simp) h.2.2.2, ?_⟩
      · apply List.Nodup.map (fun x y he => (Prod.mk.inj he).2) List.nodup_range
      · intro p hp q ht hpq
        subst q
        have he := (mem_hansenRow.mp hp).1
        rcases hansenLabels_exponent h.2.2.2 ht with he' | ⟨_, hg⟩
        · simp only [↓reduceIte] at he'; omega
        · have := hg a (List.mem_append_left _ ha); omega


/-- Source replay retains every prefix entry. -/
theorem hansenSourceFrom_mem {source : List ℕ} {steps : List MarkedStep} {x : ℕ}
    (hx : x ∈ source) : x ∈ hansenSourceFrom source steps := by
  induction steps generalizing source with
  | nil => exact hx
  | cons s rest ih => exact ih (List.mem_append_left _ hx)

/-- Any completed source value is at most its final marked endpoint. -/
theorem hansenSourceFrom_bound {source : List ℕ} {a x : ℕ} {steps : List MarkedStep}
    (hs : IsAdditionChain source) (h : IsHansenFrom source a steps)
    (hx : x ∈ hansenSourceFrom source steps) : x ≤ hansenAnchorFrom a steps := by
  have hc := hansenSourceFrom_valid hs h
  have he := hansenSourceFrom_endpoint h
  have hn : hansenSourceFrom source steps ≠ [] := by rintro hh; simp [hh] at hx
  have hl := (hc.2.1.imp le_of_lt).rel_getLast hx
  rw [List.getLast?_eq_some_getLast (h := hn)] at he
  simpa [Option.some.inj he] using hl

/-- Every label lies below the endpoint in exponent-plus-shift coordinates. -/
theorem hansenLabels_envelope {source : List ℕ} {a : ℕ} {steps : List MarkedStep}
    (hs : IsAdditionChain source) (ha : a ∈ source) (h : IsHansenFrom source a steps) :
    ∀ p ∈ hansenLabels a steps, p.1 + p.2 ≤ hansenAnchorFrom a steps := by
  induction steps generalizing source a with
  | nil => simp [hansenLabels, hansenAnchorFrom]
  | cons s rest ih =>
    obtain ⟨v, flag⟩ := s
    obtain ⟨b, hb, hv⟩ := h.2.1
    have hs' : IsAdditionChain (source ++ [v]) := by
      rw [hv]; exact append_sum hs ha hb (by simpa [hv] using h.2.2.1)
    intro p hp
    cases flag with
    | false =>
      rcases List.mem_cons.mp hp with he | ht
      · subst p
        have hkeep : v ∈ hansenSourceFrom (source ++ [v]) rest :=
          hansenSourceFrom_mem (by simp)
        change v ≤ hansenAnchorFrom a rest
        exact hansenSourceFrom_bound hs' h.2.2.2 hkeep
      · exact ih hs' (List.mem_append_left _ ha) h.2.2.2 p ht
    | true =>
      rcases List.mem_append.mp hp with hr | ht
      · have hr' := mem_hansenRow.mp hr
        have hav := h.2.2.1 a ha
        have hvn := (hansenMarksFrom_stored_max (by simp : v ∈ source ++ [v]) h.2.2.2).1
        change p.1 + p.2 ≤ hansenAnchorFrom v rest
        omega
      · exact ih hs' (by simp) h.2.2.2 p ht

/-- All newly created source bases have both Hansen summands in any ambient
allocation containing the prefix bases and this continuation's labels. -/
theorem hansenLabels_base_sums {source : List ℕ} {a : ℕ} {steps : List MarkedStep}
    {F : List (ℕ × ℕ)} (hs : IsAdditionChain source) (ha : a ∈ source)
    (h : IsHansenFrom source a steps)
    (hprefix : ∀ x ∈ source, (x, 0) ∈ F) (hlabels : hansenLabels a steps ⊆ F) :
    ∀ x ∈ hansenSourceFrom source steps, x ∈ source ∨
      ∃ p ∈ F, ∃ q ∈ F,
        shiftedMersenne x 0 = shiftedMersenne p.1 p.2 + shiftedMersenne q.1 q.2 := by
  induction steps generalizing source a with
  | nil => exact fun x hx => Or.inl hx
  | cons s rest ih =>
    obtain ⟨v, flag⟩ := s
    obtain ⟨b, hb, hv⟩ := h.2.1
    have hs' : IsAdditionChain (source ++ [v]) := by
      rw [hv]; exact append_sum hs ha hb (by simpa [hv] using h.2.2.1)
    have hbcap : b ≤ hansenNextMark a ((v, flag) :: rest) - a := by
      rw [← hansenShiftMax_eq_gap hs h]
      apply hansenShiftDemands_le_max
      cases flag <;> simp [hansenShiftDemands, hv]
    have hvsum : ∃ p ∈ F, ∃ q ∈ F,
        shiftedMersenne v 0 = shiftedMersenne p.1 p.2 + shiftedMersenne q.1 q.2 :=
      ⟨(a, b), hlabels (hansenLabels_anchor a _ hbcap), (b, 0), hprefix b hb,
        hv ▸ (shiftedMersenne_base_sum a b).symm⟩
    have hvbase : (v, 0) ∈ F := by
      apply hlabels
      cases flag with
      | false => exact List.mem_cons_self ..
      | true => exact List.mem_append_right _ (hansenLabels_base v rest)
    have hp' : ∀ x ∈ source ++ [v], (x, 0) ∈ F := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hprefix x hx
      · simpa [List.mem_singleton.mp hx] using hvbase
    have ha' : (if flag then v else a) ∈ source ++ [v] := by cases flag <;> simp [ha]
    intro x hx
    rcases ih hs' ha' h.2.2.2 hp' (fun _ hp => hlabels (hansenLabels_tail a v flag rest hp)) x hx with hp | hd
    · rcases List.mem_append.mp hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (List.mem_singleton.mp hp ▸ hvsum)
    · exact Or.inr hd

/-- For a complete Hansen source, every non-seed allocated label has two
allocated summands. Positive shifts double their predecessor; bases use the
latest marked anchor and its checked companion. -/
theorem hansenLabels_closed {steps : List MarkedStep}
    (h : IsHansenFrom [1] 1 steps) :
    ∀ p ∈ hansenLabels 1 steps, p ≠ (1, 0) →
      ∃ q ∈ hansenLabels 1 steps, ∃ r ∈ hansenLabels 1 steps,
        shiftedMersenne p.1 p.2 = shiftedMersenne q.1 q.2 + shiftedMersenne r.1 r.2 := by
  intro p hp hne
  obtain ⟨a, k⟩ := p
  cases k with
  | succ k =>
    have hm := hansenLabels_downward hp (Nat.le_succ k)
    exact ⟨(a, k), hm, (a, k), hm, shiftedMersenne_succ a k⟩
  | zero =>
    have ha : a ∈ hansenSourceFrom [1] steps := by
      rcases hansenLabels_exponent h hp with he | ⟨hm, _⟩
      · exact False.elim (hne (Prod.ext he rfl))
      · exact hm
    have hh := hansenLabels_base_sums (by decide : IsAdditionChain [1]) (by simp) h
      (F := hansenLabels 1 steps)
      (by intro x hx; simpa [List.mem_singleton.mp hx] using hansenLabels_base 1 steps)
      (fun _ hm => hm) a ha
    rcases hh with hs | hd
    · exact False.elim (hne (Prod.ext (List.mem_singleton.mp hs) rfl))
    · exact hd

end ScholzBrauer
