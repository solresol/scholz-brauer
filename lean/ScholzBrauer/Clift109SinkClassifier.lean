import ScholzBrauer.Clift109HalfReconstruction

/-! A complete finite interval classifier for FIXED box roles and actual sink
exception positions. Exact halving and the prescribed nineteen-weight shape
are both checked. Outer box/position enumeration and caps remain obligations. -/

namespace ScholzBrauer.Clift109

/-- The seven box coordinates, with their roles retained. -/
def SameSinkBox (c box : GaugeCoordinates) : Prop :=
  c.u = box.u ∧ c.v = box.v ∧ c.w = box.w ∧ c.d1 = box.d1 ∧
    c.d2 = box.d2 ∧ c.d3 = box.d3 ∧ c.t = box.t

/-- Actual exceptional positions, rather than three unrelated opposite pairs. -/
def placedSinkExceptions (box : GaugeCoordinates) (r s z : ℤ) : Multiset ℤ :=
  zbranch (zbranch {r} box.u) box.v + zbranch {s} box.u + {z}

theorem reconstructSink_same_box (box : GaugeCoordinates) (h : Multiset ℤ)
    (r s z anchor : ℤ) : SameSinkBox (reconstructSink box h r s z anchor) box := by
  simp [SameSinkBox, reconstructSink]

theorem reconstructSink_positions (box : GaugeCoordinates) (h : Multiset ℤ)
    (r s z anchor : ℤ) :
    let c := reconstructSink box h r s z anchor
    c.A1 + c.p = r ∧ c.A2 + c.p = s ∧ c.A3 + c.p = z := by
  dsimp [reconstructSink]
  omega

theorem reconstructSink_box (box : GaugeCoordinates) (h : Multiset ℤ)
    (r s z anchor : ℤ) :
    coordinateBox (reconstructSink box h r s z anchor) = coordinateBox box := by
  rfl

theorem sinkExceptions_eq_placed (c : GaugeCoordinates) :
    sinkExceptions c = placedSinkExceptions c (c.A1 + c.p)
      (c.A2 + c.p) (c.A3 + c.p) := by
  simp [sinkExceptions, placedSinkExceptions, zbranch, zshift]
  simp only [Int.add_left_comm, Int.add_comm]

theorem reconstructSink_exceptions (box : GaugeCoordinates) (h : Multiset ℤ)
    (r s z anchor : ℤ) :
    sinkExceptions (reconstructSink box h r s z anchor) =
      placedSinkExceptions box r s z := by
  rw [sinkExceptions_eq_placed]
  obtain ⟨hr, hs, hz⟩ := reconstructSink_positions box h r s z anchor
  rw [hr, hs, hz]
  rfl

/-- Changing the unused coordinates of the box prototype loses no tuple. -/
theorem reconstructSink_eq_of_same_box (c box : GaugeCoordinates)
    (hb : SameSinkBox c box) :
    reconstructSink box (sinkHalf c) (c.A1 + c.p) (c.A2 + c.p)
      (c.A3 + c.p) c.A3 = c := by
  obtain ⟨hu, hv, hw, hd1, hd2, hd3, ht⟩ := hb
  have he : reconstructSink box (sinkHalf c) (c.A1 + c.p) (c.A2 + c.p)
      (c.A3 + c.p) c.A3 =
      reconstructSink c (sinkHalf c) (c.A1 + c.p) (c.A2 + c.p)
        (c.A3 + c.p) c.A3 := by
    ext <;> simp [reconstructSink, ← hu, ← hv, ← hw, ← hd1, ← hd2, ← hd3, ← ht]
  exact he.trans (reconstructSink_eq c)

/-- Full shape equality, including multiplicities, filters the nineteen anchors.
The moment test is a proved necessary optimization, not an acceptance rule. -/
def sinkShapeAnchors (box : GaugeCoordinates) (h : Multiset ℤ)
    (r s z : ℤ) : Finset ℤ :=
  h.toFinset.filter (fun anchor => sinkHalf (reconstructSink box h r s z anchor) = h)

theorem mem_sinkShapeAnchors (box : GaugeCoordinates) (h : Multiset ℤ)
    (r s z anchor : ℤ) :
    anchor ∈ sinkShapeAnchors box h r s z ↔
      anchor ∈ h ∧ sinkHalf (reconstructSink box h r s z anchor) = h := by
  simp [sinkShapeAnchors]

/-- The exact shape filter retains at most two anchors for arbitrary inputs. -/
theorem card_sinkShapeAnchors_le_two (box : GaugeCoordinates) (h : Multiset ℤ)
    (r s z : ℤ) : (sinkShapeAnchors box h r s z).card ≤ 2 := by
  by_contra hn
  obtain ⟨x, y, a, hx, hy, ha, hxy, hxa, hya⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < (sinkShapeAnchors box h r s z).card)
  have he := sink_reconstruction_at_most_two_anchors box h r s z x y a
    ((mem_sinkShapeAnchors _ _ _ _ _ _).mp hx).2
    ((mem_sinkShapeAnchors _ _ _ _ _ _).mp hy).2
    ((mem_sinkShapeAnchors _ _ _ _ _ _).mp ha).2
  exact he.elim hxy (fun he => he.elim hxa hya)

/-- Exact fixed-input classifier. The explicit partition check prevents
truncated multiset subtraction from silently discarding excess box/exceptions. -/
def sinkIntervalAnchors (box : GaugeCoordinates) (r s z : ℤ) : Finset ℤ :=
  let interval := (Multiset.range 109).map Int.ofNat
  let exceptions := placedSinkExceptions box r s z
  match halve box.d1 ((interval - coordinateBox box) - exceptions) with
  | none => ∅
  | some h =>
      if coordinateBox box + zbranch h box.d1 + exceptions = interval then
        sinkShapeAnchors box h r s z
      else ∅

/-- Every accepted anchor yields the whole coordinate interval, with its
prescribed half. This direction needs no positivity or dissociation assumption. -/
theorem sinkIntervalAnchors_sound (box : GaugeCoordinates) (r s z anchor : ℤ)
    (ha : anchor ∈ sinkIntervalAnchors box r s z) :
    ∃ h : Multiset ℤ,
      coordinateWeights (reconstructSink box h r s z anchor) =
        (Multiset.range 109).map Int.ofNat := by
  unfold sinkIntervalAnchors at ha
  dsimp only at ha
  split at ha
  · simp at ha
  · rename_i h hh
    split_ifs at ha with hp
    · have hs := ((mem_sinkShapeAnchors _ _ _ _ _ _).mp ha).2
      refine ⟨h, ?_⟩
      rw [coordinateWeights, remainder_sink_factor, reconstructSink_box,
        reconstructSink_exceptions, hs]
      exact (add_assoc _ _ _).symm.trans hp
    · simp at ha

/-- At most two whole-interval candidates for fixed box roles and positions. -/
theorem card_sinkIntervalAnchors_le_two (box : GaugeCoordinates) (r s z : ℤ) :
    (sinkIntervalAnchors box r s z).card ≤ 2 := by
  unfold sinkIntervalAnchors
  dsimp only
  split
  · simp
  · split_ifs
    · exact card_sinkShapeAnchors_le_two _ _ _ _ _
    · simp

/-- Completeness for ANY tuple with the fixed box roles and actual positions.
The outer box/position choices still require a separate complete enumeration. -/
theorem sinkIntervalAnchors_complete (c box : GaugeCoordinates)
    (hb : SameSinkBox c box) (hd : 0 < c.d1)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    c.A3 ∈ sinkIntervalAnchors box (c.A1 + c.p) (c.A2 + c.p) (c.A3 + c.p) := by
  have hbox : coordinateBox c = coordinateBox box := by
    obtain ⟨hu, hv, hw, hd1, hd2, hd3, ht⟩ := hb
    simp only [coordinateBox, hu, hv, hw, hd1, hd2, hd3, ht]
  have hex : sinkExceptions c = placedSinkExceptions box (c.A1 + c.p)
      (c.A2 + c.p) (c.A3 + c.p) := by
    rw [sinkExceptions_eq_placed]
    simp only [placedSinkExceptions, hb.1, hb.2.1]
  have hh : halve c.d1 (((Multiset.range 109).map Int.ofNat - coordinateBox c) -
      sinkExceptions c) = some (sinkHalf c) := by
    apply (halve_eq_some_iff _ hd _ _).mpr
    rw [← hi]
    simp only [coordinateWeights, add_tsub_cancel_left]
    rw [remainder_sink_factor, add_tsub_cancel_right]
  unfold sinkIntervalAnchors
  dsimp only
  rw [← hex, ← hbox, ← hb.2.2.2.1, hh]
  dsimp only
  have hp' : coordinateBox c + zbranch (sinkHalf c) c.d1 + sinkExceptions c =
      (Multiset.range 109).map Int.ofNat := by
    rw [add_assoc, ← remainder_sink_factor]
    exact hi
  rw [if_pos hp']
  apply (mem_sinkShapeAnchors _ _ _ _ _ _).mpr
  exact ⟨anchor_mem_sinkHalf c, by rw [reconstructSink_eq_of_same_box c box hb]⟩

/-- Exact existential meaning of the finite classifier, for positive d1.
Neither independent relaxed halves nor moment equality suffice for acceptance. -/
theorem mem_sinkIntervalAnchors_iff (box : GaugeCoordinates) (r s z anchor : ℤ)
    (hd : 0 < box.d1) :
    anchor ∈ sinkIntervalAnchors box r s z ↔
      ∃ c : GaugeCoordinates, SameSinkBox c box ∧
        c.A1 + c.p = r ∧ c.A2 + c.p = s ∧ c.A3 + c.p = z ∧
        c.A3 = anchor ∧
        coordinateWeights c = (Multiset.range 109).map Int.ofNat := by
  constructor
  · intro ha
    obtain ⟨h, hi⟩ := sinkIntervalAnchors_sound box r s z anchor ha
    obtain ⟨hr, hs, hz⟩ := reconstructSink_positions box h r s z anchor
    exact ⟨reconstructSink box h r s z anchor,
      reconstructSink_same_box box h r s z anchor, hr, hs, hz, rfl, hi⟩
  · rintro ⟨c, hb, hr, hs, hz, ha, hi⟩
    have hc := sinkIntervalAnchors_complete c box hb
      (by rw [hb.2.2.2.1]; exact hd) hi
    rw [hr, hs, hz, ha] at hc
    exact hc

/-- Accepted anchors retain the finite bounds of the prescribed half. -/
theorem sinkIntervalAnchors_bounds (box : GaugeCoordinates) (r s z anchor : ℤ)
    (ha : anchor ∈ sinkIntervalAnchors box r s z) :
    0 ≤ anchor ∧ anchor + box.d1 < 109 := by
  obtain ⟨h, hi⟩ := sinkIntervalAnchors_sound box r s z anchor ha
  have hb := interval_sinkHalf_bounds _ hi _
    (anchor_mem_sinkHalf (reconstructSink box h r s z anchor))
  exact hb

/-- Every original budget-108 labelling is retained by this finite, full-shape
test at its actual box roles and sink positions. No cap feasibility is inferred. -/
theorem sink_classifier_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    let candidates := sinkIntervalAnchors c (c.A1 + c.p) (c.A2 + c.p) (c.A3 + c.p)
    c.A3 ∈ candidates ∧ candidates.card ≤ 2 := by
  dsimp only
  have hd := (halving_of_budget B a b cap h1 hsteps hcap h109 hbudget).2.1
  exact ⟨sinkIntervalAnchors_complete _ _ (by simp [SameSinkBox]) hd
    (normalized_interval_of_budget B a b cap h1 hsteps hcap h109 hbudget),
    card_sinkIntervalAnchors_le_two _ _ _ _⟩

end ScholzBrauer.Clift109
