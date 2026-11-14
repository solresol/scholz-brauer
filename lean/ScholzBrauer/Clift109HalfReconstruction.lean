import ScholzBrauer.Clift109Halving

/-! Recover the prescribed nineteen-weight sink half, retaining its shape.
Its first moment recovers q from the actual exception positions and anchor A3.
Its first two moments leave at most two anchor candidates. This is a necessary
reconstruction; the prescribed shape and cap constraints remain obligations. -/

namespace ScholzBrauer.Clift109

/-- First moment of the graph's prescribed nineteen-weight sink half. -/
theorem sum_sinkHalf (c : GaugeCoordinates) :
    (sinkHalf c).sum = 12 * c.A1 + 4 * c.A2 + 3 * c.A3 +
      8 * c.u + 6 * c.v + 7 * c.d2 + 5 * c.q := by
  simp [sinkHalf, zbranch, zshift]
  ring

/-- Reconstruct q from the unique half and the ACTUAL sink exception
positions r=A1+p, s=A2+p, z=A3+p. No arbitrary half is substituted. -/
def sinkRecoveredQ (h : Multiset ℤ) (u v d2 r s z anchor : ℤ) : ℤ :=
  (h.sum - 12 * r - 4 * s + 16 * z - 19 * anchor -
    8 * u - 6 * v - 7 * d2) / 5

/-- The anchor A3 occurs in the graph's prescribed half. -/
theorem anchor_mem_sinkHalf (c : GaugeCoordinates) : c.A3 ∈ sinkHalf c := by
  simp [sinkHalf, zbranch, zshift]

/-- Exact recovery removes the otherwise free q coordinate. -/
theorem sinkRecoveredQ_eq (c : GaugeCoordinates) :
    sinkRecoveredQ (sinkHalf c) c.u c.v c.d2
      (c.A1 + c.p) (c.A2 + c.p) (c.A3 + c.p) c.A3 = c.q := by
  unfold sinkRecoveredQ
  rw [sum_sinkHalf]
  omega

/-- The first moment also restricts the anchor to one residue class mod 5. -/
theorem sink_anchor_residue (c : GaugeCoordinates) :
    (sinkHalf c).sum - 12 * (c.A1 + c.p) - 4 * (c.A2 + c.p) +
      16 * (c.A3 + c.p) - 8 * c.u - 6 * c.v - 7 * c.d2 ≡
        19 * c.A3 [ZMOD 5] := by
  rw [sum_sinkHalf]
  rw [Int.modEq_iff_dvd]
  use -c.q
  ring

/-- Once the box roles, actual sink exception positions and unique half
are fixed, there is at most one tuple for each choice of the anchor A3. -/
theorem sink_coordinates_unique (c c' : GaugeCoordinates)
    (hu : c.u = c'.u) (hv : c.v = c'.v) (hw : c.w = c'.w)
    (hd1 : c.d1 = c'.d1) (hd2 : c.d2 = c'.d2) (hd3 : c.d3 = c'.d3)
    (ht : c.t = c'.t) (hr : c.A1 + c.p = c'.A1 + c'.p)
    (hs : c.A2 + c.p = c'.A2 + c'.p) (hz : c.A3 + c.p = c'.A3 + c'.p)
    (ha : c.A3 = c'.A3) (hh : sinkHalf c = sinkHalf c') : c = c' := by
  have hp : c.p = c'.p := by omega
  have hA1 : c.A1 = c'.A1 := by omega
  have hA2 : c.A2 = c'.A2 := by omega
  have hq : c.q = c'.q := by
    have h := sinkRecoveredQ_eq c
    have h' := sinkRecoveredQ_eq c'
    rw [hh, hu, hv, hd2, hr, hs, hz, ha] at h
    exact h.symm.trans h'
  cases c
  cases c'
  simp_all

/-- Integer reconstruction used after choosing an anchor in the exact half.
The remaining seven coordinates come from the fixed common box and its roles. -/
def reconstructSink (box : GaugeCoordinates) (h : Multiset ℤ)
    (r s z anchor : ℤ) : GaugeCoordinates :=
  { box with
    p := z - anchor
    q := sinkRecoveredQ h box.u box.v box.d2 r s z anchor
    A1 := r - z + anchor
    A2 := s - z + anchor
    A3 := anchor }

/-- Completeness of the reconstruction formula for the prescribed half. -/
theorem reconstructSink_eq (c : GaugeCoordinates) :
    reconstructSink c (sinkHalf c) (c.A1 + c.p) (c.A2 + c.p)
      (c.A3 + c.p) c.A3 = c := by
  have hq := sinkRecoveredQ_eq c
  cases c
  simp_all [reconstructSink]

private theorem interval_remainder_bounds (c : GaugeCoordinates)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat)
    (x : ℤ) (hx : x ∈ coordinateRemainder c) : 0 ≤ x ∧ x < 109 := by
  have hm : x ∈ (Multiset.range 109).map Int.ofNat := by
    rw [← hi]
    exact Multiset.mem_add.mpr (Or.inr hx)
  obtain ⟨i, hmem, rfl⟩ := Multiset.mem_map.mp hm
  have := Multiset.mem_range.mp hmem
  change 0 ≤ (i : ℤ) ∧ (i : ℤ) < 109
  omega

/-- Every recovered anchor lies in the bounded exact half. This keeps all
nineteen prescribed weights, including the partner at distance d1. -/
theorem interval_sinkHalf_bounds (c : GaugeCoordinates)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    ∀ x ∈ sinkHalf c, 0 ≤ x ∧ x + c.d1 < 109 := by
  intro x hx
  have h0 : x ∈ coordinateRemainder c := by
    rw [remainder_sink_factor]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl hx)))
  have h1 : x + c.d1 ∈ coordinateRemainder c := by
    rw [remainder_sink_factor]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr
      (Or.inr (Multiset.mem_map.mpr ⟨x, hx, rfl⟩))))
  exact ⟨(interval_remainder_bounds c hi x h0).1,
    (interval_remainder_bounds c hi (x + c.d1) h1).2⟩

/-- Any successful exact sink halving of an interval tuple recovers its
prescribed half. Its nineteen bounded anchors and one residue class suffice
for complete coordinate reconstruction; the full shape still must be checked. -/
theorem interval_sink_reconstruction (c : GaugeCoordinates) (hd : 0 < c.d1)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat)
    (h : Multiset ℤ)
    (hh : halve c.d1 (((Multiset.range 109).map Int.ofNat - coordinateBox c) -
      sinkExceptions c) = some h) :
    h = sinkHalf c ∧ h.card = 19 ∧ h.Nodup ∧ c.A3 ∈ h ∧
    (∀ x ∈ h, 0 ≤ x ∧ x + c.d1 < 109) ∧
    h.sum - 12 * (c.A1 + c.p) - 4 * (c.A2 + c.p) +
      16 * (c.A3 + c.p) - 8 * c.u - 6 * c.v - 7 * c.d2 ≡
        19 * c.A3 [ZMOD 5] ∧
    reconstructSink c h (c.A1 + c.p) (c.A2 + c.p) (c.A3 + c.p) c.A3 = c := by
  have he : h = sinkHalf c := by
    apply Option.some.inj
    rw [← hh]
    apply (halve_eq_some_iff _ hd _ _).mpr
    rw [← hi]
    simp only [coordinateWeights, add_tsub_cancel_left]
    rw [remainder_sink_factor, add_tsub_cancel_right]
  subst h
  exact ⟨rfl, card_sinkHalf c, (interval_halves_disjoint c hi).1,
    anchor_mem_sinkHalf c, interval_sinkHalf_bounds c hi,
    sink_anchor_residue c, reconstructSink_eq c⟩

/-- Transport exact recovery and its finite anchor domain to the original
natural edge labels. No interval classification or cap feasibility is assumed. -/
theorem sink_reconstruction_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    ∃ h : Multiset ℤ,
      halve c.d1 (((Multiset.range 109).map Int.ofNat - coordinateBox c) -
        sinkExceptions c) = some h ∧
      h.card = 19 ∧ h.Nodup ∧ c.A3 ∈ h ∧
      (∀ x ∈ h, 0 ≤ x ∧ x + c.d1 < 109) ∧
      h.sum - 12 * (c.A1 + c.p) - 4 * (c.A2 + c.p) +
        16 * (c.A3 + c.p) - 8 * c.u - 6 * c.v - 7 * c.d2 ≡
          19 * c.A3 [ZMOD 5] ∧
      reconstructSink c h (c.A1 + c.p) (c.A2 + c.p) (c.A3 + c.p) c.A3 = c := by
  dsimp only
  obtain ⟨_, hd, hh, _⟩ := halving_of_budget B a b cap h1 hsteps hcap h109 hbudget
  have hi := normalized_interval_of_budget B a b cap h1 hsteps hcap h109 hbudget
  obtain ⟨_, hc, hn, ha, hb, hr, he⟩ := interval_sink_reconstruction _ hd hi _ hh
  exact ⟨_, hh, hc, hn, ha, hb, hr, he⟩

/-- The second moment of integer path weights, with multiplicities. -/
def weightSquareSum (h : Multiset ℤ) : ℤ := (h.map (fun x => x ^ 2)).sum

private theorem sum_zshift (h : Multiset ℤ) (a : ℤ) :
    (zshift h a).sum = h.sum + h.card * a := by
  induction h using Multiset.induction_on with
  | empty => simp [zshift]
  | @cons x h ih =>
    simp only [zshift, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons] at *
    push_cast
    linarith

private theorem weightSquareSum_zshift (h : Multiset ℤ) (a : ℤ) :
    weightSquareSum (zshift h a) = weightSquareSum h + 2 * h.sum * a + h.card * a ^ 2 := by
  induction h using Multiset.induction_on with
  | empty => simp [weightSquareSum, zshift]
  | @cons x h ih =>
    simp only [weightSquareSum, zshift, Multiset.map_cons, Multiset.sum_cons,
      Multiset.card_cons] at *
    push_cast
    nlinarith

/-- A fixed fourteen-point shape and a fixed five-point shape admit at most
two choices of the first translation in ANY prescribed multiset. Signed
weights and multiplicities are allowed. First and second moments suffice. -/
theorem fourteen_five_moments_at_most_two (k p h : Multiset ℤ)
    (hk : k.card = 14) (hp : p.card = 5)
    (x₁ x₂ x₃ y₁ y₂ y₃ : ℤ)
    (h₁ : (zshift k x₁ + zshift p y₁).sum = h.sum ∧
      weightSquareSum (zshift k x₁ + zshift p y₁) = weightSquareSum h)
    (h₂ : (zshift k x₂ + zshift p y₂).sum = h.sum ∧
      weightSquareSum (zshift k x₂ + zshift p y₂) = weightSquareSum h)
    (h₃ : (zshift k x₃ + zshift p y₃).sum = h.sum ∧
      weightSquareSum (zshift k x₃ + zshift p y₃) = weightSquareSum h) :
    x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃ := by
  let C := h.sum - k.sum - p.sum
  let D := weightSquareSum h - weightSquareSum k - weightSquareSum p
  let L := 10 * k.sum - 28 * p.sum - 28 * C
  have quadratic : ∀ x y : ℤ,
      (zshift k x + zshift p y).sum = h.sum ∧
      weightSquareSum (zshift k x + zshift p y) = weightSquareSum h →
      266 * x ^ 2 + L * x + C ^ 2 + 2 * p.sum * C - 5 * D = 0 := by
    intro x y he
    have hs := he.1
    simp only [Multiset.sum_add, sum_zshift, hk, hp] at hs
    norm_num at hs
    have hs' : 14 * x + 5 * y - C = 0 := by dsimp [C]; linarith
    have hq := he.2
    simp only [weightSquareSum, Multiset.map_add, Multiset.sum_add] at hq
    change weightSquareSum (zshift k x) + weightSquareSum (zshift p y) = weightSquareSum h at hq
    rw [weightSquareSum_zshift, weightSquareSum_zshift, hk, hp] at hq
    norm_num at hq
    have hq' : 14 * x ^ 2 + 5 * y ^ 2 + 2 * k.sum * x +
        2 * p.sum * y - D = 0 := by dsimp [D]; linarith
    dsimp only [L]
    calc
      _ = 5 * (14 * x ^ 2 + 5 * y ^ 2 + 2 * k.sum * x +
          2 * p.sum * y - D) -
          (5 * y + C - 14 * x + 2 * p.sum) * (14 * x + 5 * y - C) := by ring
      _ = 0 := by rw [hq', hs']; ring
  have q₁ := quadratic _ _ h₁
  have q₂ := quadratic _ _ h₂
  have q₃ := quadratic _ _ h₃
  have e₁₂ : (x₁ - x₂) * (266 * (x₁ + x₂) + L) = 0 := by nlinarith
  have e₁₃ : (x₁ - x₃) * (266 * (x₁ + x₃) + L) = 0 := by nlinarith
  by_cases h12 : x₁ = x₂
  · exact Or.inl h12
  by_cases h13 : x₁ = x₃
  · exact Or.inr (Or.inl h13)
  have z12 := (mul_eq_zero.mp e₁₂).resolve_left (sub_ne_zero.mpr h12)
  have z13 := (mul_eq_zero.mp e₁₃).resolve_left (sub_ne_zero.mpr h13)
  exact Or.inr (Or.inr (by linarith))

private def sinkAnchorCore (u v d2 r s : ℤ) : Multiset ℤ :=
  zshift (zbranch (zbranch {0, d2} u) v) r +
    zshift (zbranch {0, d2} u) s + {0, d2}

private def sinkAnchorPetal (u v r : ℤ) : Multiset ℤ :=
  zshift (zbranch (zbranch {0} u) v) r + {0}

private theorem sinkHalf_reconstruct_factor (box : GaugeCoordinates) (h : Multiset ℤ)
    (r s z anchor : ℤ) :
    sinkHalf (reconstructSink box h r s z anchor) =
      zshift (sinkAnchorCore box.u box.v box.d2 (r - z) (s - z)) anchor +
      zshift (sinkAnchorPetal box.u box.v (r - z))
        (anchor + sinkRecoveredQ h box.u box.v box.d2 r s z anchor) := by
  simp [sinkHalf, reconstructSink, sinkAnchorCore, sinkAnchorPetal, zbranch, zshift]
  simp only [Int.add_assoc, Int.add_left_comm, Int.add_comm, ← Multiset.singleton_add]
  ac_rfl

/-- First and second moments are a necessary test for the prescribed half;
they are deliberately weaker than equality of all nineteen weights. -/
def sinkMomentCompatible (box : GaugeCoordinates) (h : Multiset ℤ)
    (r s z anchor : ℤ) : Prop :=
  let candidate := sinkHalf (reconstructSink box h r s z anchor)
  candidate.sum = h.sum ∧ weightSquareSum candidate = weightSquareSum h

/-- Every prescribed half passes the moment test at its actual anchor. -/
theorem sink_moments_of_prescribed_half (c : GaugeCoordinates) :
    sinkMomentCompatible c (sinkHalf c) (c.A1 + c.p) (c.A2 + c.p)
      (c.A3 + c.p) c.A3 := by
  simp [sinkMomentCompatible, reconstructSink_eq]

/-- At most two anchors pass even the moment test, for fixed box roles,
actual exception positions and recovered half. -/
theorem sink_moments_at_most_two_anchors (box : GaugeCoordinates)
    (h : Multiset ℤ) (r s z x₁ x₂ x₃ : ℤ)
    (h₁ : sinkMomentCompatible box h r s z x₁)
    (h₂ : sinkMomentCompatible box h r s z x₂)
    (h₃ : sinkMomentCompatible box h r s z x₃) :
    x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃ := by
  unfold sinkMomentCompatible at h₁ h₂ h₃
  dsimp only at h₁ h₂ h₃
  rw [sinkHalf_reconstruct_factor] at h₁ h₂ h₃
  apply fourteen_five_moments_at_most_two _ _ h _ _ _ _ _ _ _ _ h₁ h₂ h₃
  · simp [sinkAnchorCore, zbranch, zshift]
  · simp [sinkAnchorPetal, zbranch, zshift]

/-- The prescribed half leaves at most TWO anchors for fixed box roles,
actual exception positions and recovered half. Each candidate must still pass
the full nineteen-weight shape and the remaining interval/cap constraints. -/
theorem sink_reconstruction_at_most_two_anchors (box : GaugeCoordinates)
    (h : Multiset ℤ) (r s z x₁ x₂ x₃ : ℤ)
    (h₁ : sinkHalf (reconstructSink box h r s z x₁) = h)
    (h₂ : sinkHalf (reconstructSink box h r s z x₂) = h)
    (h₃ : sinkHalf (reconstructSink box h r s z x₃) = h) :
    x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃ := by
  apply sink_moments_at_most_two_anchors box h r s z
  · simp [sinkMomentCompatible, h₁]
  · simp [sinkMomentCompatible, h₂]
  · simp [sinkMomentCompatible, h₃]

end ScholzBrauer.Clift109
