import ScholzBrauer.Clift109SinkClassifier

namespace ScholzBrauer.Clift109

/-- Subtracting the common shift p from each exceptional weight gives
seven compulsory members of the prescribed half. -/
def translatedExceptions (u v r s z anchor : ℤ) : List ℤ :=
  [r-z+anchor, r-z+anchor+u, r-z+anchor+v, r-z+anchor+u+v,
   s-z+anchor, s-z+anchor+u, anchor]

private theorem mem_shift {a : Multiset ℤ} {x : ℤ} (hx : x ∈ a) (d : ℤ) :
    x+d ∈ zshift a d := Multiset.mem_map.mpr ⟨x, hx, rfl⟩

private theorem mem_branch {a : Multiset ℤ} {x : ℤ} (hx : x ∈ a) (d : ℤ) :
    x ∈ zbranch a d ∧ x+d ∈ zbranch a d :=
  ⟨Multiset.mem_add.mpr (.inl hx), Multiset.mem_add.mpr (.inr (mem_shift hx d))⟩

theorem translatedExceptions_mem_half (c : GaugeCoordinates) :
    ∀ x ∈ translatedExceptions c.u c.v (c.A1+c.p) (c.A2+c.p) (c.A3+c.p) c.A3,
      x ∈ sinkHalf c := by
  have h0 : (0 : ℤ) ∈ ({0, c.d2} + {c.q} : Multiset ℤ) := by simp
  have hu := mem_branch h0 c.u
  have h0v := mem_branch hu.1 c.v
  have huv := mem_branch hu.2 c.v
  have ht := mem_branch (by simp : (0 : ℤ) ∈ ({0, c.d2} : Multiset ℤ)) c.u
  simp only [translatedExceptions, List.mem_cons, List.not_mem_nil, or_false]
  intro x hx
  rcases hx with h|h|h|h|h|h|h <;> subst x
  all_goals simp only [sinkHalf, Multiset.mem_add]
  · exact Or.inl (Or.inl (by convert mem_shift h0v.1 c.A1 using 1; ring))
  · exact Or.inl (Or.inl (by convert mem_shift huv.1 c.A1 using 1; ring))
  · exact Or.inl (Or.inl (by convert mem_shift h0v.2 c.A1 using 1; ring))
  · exact Or.inl (Or.inl (by convert mem_shift huv.2 c.A1 using 1; ring))
  · exact Or.inl (Or.inr (by convert mem_shift ht.1 c.A2 using 1; ring))
  · exact Or.inl (Or.inr (by convert mem_shift ht.2 c.A2 using 1; ring))
  · exact Or.inr (by simpa using mem_shift h0 c.A3)

/-- A surviving unrestricted half, with the rectangle step and three starts. -/
structure Sparse827Row where
  v : ℤ
  r : ℤ
  s : ℤ
  z : ℤ
  half : Multiset ℤ
  deriving DecidableEq

/-- Witnesses from the 25 November outer scan. Coverage of this list by the
outer enumeration is a separate obligation. -/
def sparse827Rows : List Sparse827Row :=
  [⟨11, 0, 38, 35, {3, 4, 5, 16, 22, 23, 24, 27, 57, 58, 59, 62, 65, 70, 73, 76, 77, 78, 81}⟩,
   ⟨11, 0, 38, 89, {3, 4, 5, 16, 22, 23, 24, 27, 35, 57, 58, 59, 65, 70, 73, 76, 77, 78, 81}⟩,
   ⟨11, 0, 92, 35, {3, 4, 5, 16, 22, 23, 24, 27, 38, 46, 57, 58, 59, 62, 70, 76, 77, 78, 81}⟩,
   ⟨11, 0, 92, 89, {3, 4, 5, 16, 22, 23, 24, 27, 35, 38, 46, 57, 58, 59, 70, 76, 77, 78, 81}⟩,
   ⟨11, 35, 8, 19, {0, 3, 4, 5, 11, 22, 23, 24, 57, 58, 59, 62, 65, 70, 73, 76, 77, 78, 81}⟩,
   ⟨11, 43, 16, 89, {0, 3, 4, 5, 8, 11, 19, 22, 23, 57, 58, 59, 65, 70, 73, 76, 77, 78, 81}⟩,
   ⟨11, 46, 84, 19, {0, 3, 4, 5, 8, 11, 16, 22, 23, 24, 58, 59, 62, 70, 73, 76, 77, 78, 81}⟩,
   ⟨11, 54, 92, 89, {0, 3, 4, 5, 8, 11, 16, 19, 22, 23, 24, 57, 58, 59, 70, 76, 77, 78, 81}⟩,
   ⟨11, 89, 8, 19, {0, 3, 4, 5, 11, 22, 23, 24, 35, 43, 46, 54, 57, 58, 59, 65, 76, 77, 78}⟩,
   ⟨11, 89, 8, 73, {0, 3, 4, 5, 11, 19, 22, 23, 24, 35, 43, 54, 57, 58, 59, 65, 76, 77, 78}⟩,
   ⟨11, 89, 62, 19, {0, 3, 4, 5, 8, 11, 16, 22, 23, 24, 46, 54, 57, 58, 59, 65, 76, 77, 78}⟩,
   ⟨11, 89, 62, 73, {0, 3, 4, 5, 8, 11, 16, 19, 22, 23, 24, 54, 57, 58, 59, 65, 76, 77, 78}⟩,
   ⟨54, 0, 27, 89, {3, 4, 5, 11, 16, 19, 22, 23, 24, 57, 58, 59, 65, 70, 73, 76, 77, 78, 81}⟩,
   ⟨54, 46, 73, 19, {0, 3, 4, 5, 8, 11, 16, 22, 23, 24, 57, 58, 59, 62, 65, 70, 76, 77, 78}⟩]

def sparse827Box : GaugeCoordinates := ⟨8, 11, 1, 27, 5, 54, 1, 0, 0, 0, 0, 0⟩

private def rowBox (k : Sparse827Row) : GaugeCoordinates := { sparse827Box with v := k.v }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem sparse827_halves_checked : ∀ k ∈ sparse827Rows,
    coordinateBox sparse827Box + (zbranch k.half 27 + placedSinkExceptions (rowBox k) k.r k.s k.z)
      = (Multiset.range 109).map Int.ofNat ∧
    ∀ a ∈ k.half, ¬ (∀ x ∈ translatedExceptions 8 k.v k.r k.s k.z a, x ∈ k.half) := by
  decide +kernel

theorem zSS_perm {xs ys : List ℤ} (hp : xs.Perm ys) : zSS xs = zSS ys := by
  induction hp with
  | nil => rfl
  | cons _ _ ih => simp only [zSS, ih]
  | swap x y l =>
    simp only [zSS, zbranch, zshift_add, zshift_shift, add_comm x y]
    ac_rfl
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

/-- The seven compulsory weights alone rule out each listed input, irrespective
of the remaining dimension roles whenever they give the same translated box. -/
theorem sparse827_no_interval (c : GaugeCoordinates) (k : Sparse827Row) (hk : k ∈ sparse827Rows)
    (ht : c.t = 1)
    (hp : [c.d3, c.d2, c.d1, c.w, c.v, c.u].Perm [54, 5, 27, 1, 11, 8])
    (hu : c.u = 8) (hv : c.v = k.v)
    (hd : c.d1 = 27) (hr : c.A1+c.p = k.r) (hs : c.A2+c.p = k.s) (hz : c.A3+c.p = k.z) :
    coordinateWeights c ≠ (Multiset.range 109).map Int.ofNat := by
  intro hi
  obtain ⟨hpart, hbad⟩ := sparse827_halves_checked k hk
  have hb : coordinateBox c = coordinateBox sparse827Box := by
    simp only [coordinateBox, zSS_perm hp, ht, sparse827Box]
  have he : sinkExceptions c = placedSinkExceptions (rowBox k) k.r k.s k.z := by
    rw [sinkExceptions_eq_placed, hr, hs, hz]
    simp only [placedSinkExceptions, hu, hv, rowBox, sparse827Box]
  rw [coordinateWeights, remainder_sink_factor, hb, he, hd, ← hpart] at hi
  have hh := zbranch_injective 27 (by decide) (add_right_cancel (add_left_cancel hi))
  have hm := translatedExceptions_mem_half c
  rw [hu, hv, hr, hs, hz, hh] at hm
  exact hbad c.A3 (hh ▸ anchor_mem_sinkHalf c) hm

end ScholzBrauer.Clift109
