import ScholzBrauer.Clift109SinkClassifier
import ScholzBrauer.Clift109Alternating

/-! Complete actual sink-position coverage for each fixed box. The signed
fingerprint only prunes inputs; the existing full-shape classifier still decides
interval completion. Enumerating the outer box roles and enforcing caps remain. -/

namespace ScholzBrauer.Clift109

/-- The interval is listed explicitly so finite coverage can be kernel evaluated. -/
def sinkPositionRange : List ℤ := (List.range 109).map Int.ofNat

def sinkRectangle (box : GaugeCoordinates) (r : ℤ) : Multiset ℤ :=
  zbranch (zbranch {r} box.u) box.v

def sinkPair (box : GaugeCoordinates) (s : ℤ) : Multiset ℤ :=
  zbranch {s} box.u

/-- When all seven odd residues are needed, every exception must occupy
one of them: there is no room for an even repeated residue. Otherwise this
filter imposes no additional restriction. -/
def sinkAllowedPosition (box : GaugeCoordinates) (x : ℤ) : Prop :=
  (intervalOddResidues box.d1).card = 7 → x % box.d1 ∈ intervalOddResidues box.d1

instance (box : GaugeCoordinates) (x : ℤ) : Decidable (sinkAllowedPosition box x) :=
  inferInstanceAs (Decidable ((intervalOddResidues box.d1).card = 7 →
    x % box.d1 ∈ intervalOddResidues box.d1))

/-- Saturating the odd-label cardinality forces every label to be odd. -/
theorem mem_oddLabels_of_card_eq {a : Multiset ℤ}
    (hc : (oddLabels a).card = a.card) {x : ℤ} (hx : x ∈ a) : x ∈ oddLabels a := by
  have hle : a.toFinset.card ≤ (oddLabels a).card := by
    rw [hc]
    exact Multiset.toFinset_card_le a
  have he := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hle
  rw [show oddLabels a = a.toFinset from he]
  exact Multiset.mem_toFinset.mpr hx

/-- Every actual sink exception passes the saturated-residue position filter. -/
theorem interval_sink_allowed_positions (c : GaugeCoordinates)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    ∀ x ∈ sinkExceptions c, sinkAllowedPosition c x := by
  intro x hx hcard
  have hf := interval_residue_fingerprint c.d1
    (zshift (zSS [c.d3, c.d2, c.w, c.v, c.u]) c.t + sinkHalf c)
    (sinkExceptions c) ((weights_sink_factor c).symm.trans hi).symm
  have hc : (oddLabels ((sinkExceptions c).map (· % c.d1))).card =
      ((sinkExceptions c).map (· % c.d1)).card := by
    rw [← hf, hcard, Multiset.card_map, card_sinkExceptions]
  rw [hf]
  exact mem_oddLabels_of_card_eq hc (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)

/-- Rectangle starts are checked once before any pair/singleton search. -/
def sinkRectangleStarts (box : GaugeCoordinates) : List ℤ :=
  let rest := (Multiset.range 109).map Int.ofNat - coordinateBox box
  sinkPositionRange.filter fun r => sinkAllowedPosition box r ∧ sinkRectangle box r ≤ rest

/-- The remaining search at one rectangle start. Keeping this stage separate
permits context-specific kernel checks without repeating a monolithic reduction. -/
def sinkPositionChoicesAt (box : GaugeCoordinates) (r : ℤ) : List (ℤ × ℤ × ℤ) :=
  let rest := (Multiset.range 109).map Int.ofNat - coordinateBox box
  let afterRectangle := rest - sinkRectangle box r
  (sinkPositionRange.filter fun s => sinkAllowedPosition box s ∧ sinkPair box s ≤ afterRectangle).flatMap fun s =>
    let afterPair := afterRectangle - sinkPair box s
    let target := alternatingTarget box.d1 -
      alternatingSum box.d1 (sinkRectangle box r + sinkPair box s)
    (sinkPositionRange.filter fun z => sinkAllowedPosition box z ∧ z ∈ afterPair ∧
      alternatingDigit box.d1 z = target).map fun z => (r, s, z)

/-- Enumerate actual rectangle, pair and singleton positions in stages. Each
subtraction is preceded by a multiset inclusion check, preserving multiplicity.
The signed fingerprint cancels both the box and the prescribed translated half. -/
def sinkPositionChoices (box : GaugeCoordinates) : List (ℤ × ℤ × ℤ) :=
  (sinkRectangleStarts box).flatMap (sinkPositionChoicesAt box)

private theorem mem_position_range_of_interval {x : ℤ}
    (hx : x ∈ (Multiset.range 109).map Int.ofNat) : x ∈ sinkPositionRange := by
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr (Multiset.mem_range.mp hi), rfl⟩

/-- Every actual interval tuple has the signed exception fingerprint. No
independently chosen nineteen-weight half is substituted in this implication. -/
theorem interval_sink_position_fingerprint (c : GaugeCoordinates) (hd : 0 < c.d1)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    alternatingSum c.d1 (sinkExceptions c) = alternatingTarget c.d1 := by
  have he := congrArg (alternatingSum c.d1) ((weights_sink_factor c).symm.trans hi)
  rw [show alternatingSum c.d1
      (zbranch (zshift (zSS [c.d3, c.d2, c.w, c.v, c.u]) c.t + sinkHalf c) c.d1 +
        sinkExceptions c) =
      alternatingSum c.d1
        (zbranch (zshift (zSS [c.d3, c.d2, c.w, c.v, c.u]) c.t + sinkHalf c) c.d1) +
      alternatingSum c.d1 (sinkExceptions c) by
        simp only [alternatingSum, Multiset.map_add, Multiset.sum_add],
    alternatingSum_branch _ hd, zero_add] at he
  exact he

/-- Coverage of ALL actual sink positions, with the seven box roles fixed.
The prototype's other five coordinates are irrelevant and may be arbitrary. -/
theorem sinkPositionChoices_complete (c box : GaugeCoordinates)
    (hb : SameSinkBox c box) (hd : 0 < c.d1)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    (c.A1 + c.p, c.A2 + c.p, c.A3 + c.p) ∈ sinkPositionChoices box := by
  let r := c.A1 + c.p
  let s := c.A2 + c.p
  let z := c.A3 + c.p
  let rest := (Multiset.range 109).map Int.ofNat - coordinateBox box
  have hbox : coordinateBox c = coordinateBox box := by
    obtain ⟨hu, hv, hw, hd1, hd2, hd3, ht⟩ := hb
    simp only [coordinateBox, hu, hv, hw, hd1, hd2, hd3, ht]
  have hex : sinkExceptions c = sinkRectangle box r + sinkPair box s + {z} := by
    rw [sinkExceptions_eq_placed]
    simp only [sinkRectangle, sinkPair, placedSinkExceptions, hb.1, hb.2.1]
    rfl
  have he : sinkRectangle box r + sinkPair box s + {z} ≤ rest := by
    dsimp only [rest]
    rw [← hbox, ← hi]
    simp only [coordinateWeights, add_tsub_cancel_left]
    rw [← hex, remainder_sink_factor]
    exact Multiset.le_add_left _ _
  have hr : sinkRectangle box r ≤ rest :=
    (Multiset.le_add_right _ _).trans ((Multiset.le_add_right _ _).trans he)
  have hsz : sinkPair box s + {z} ≤ rest - sinkRectangle box r :=
    le_tsub_of_add_le_left (by simpa only [add_assoc] using he)
  have hs : sinkPair box s ≤ rest - sinkRectangle box r :=
    (Multiset.le_add_right _ _).trans hsz
  have hz : z ∈ rest - sinkRectangle box r - sinkPair box s :=
    Multiset.singleton_le.mp (le_tsub_of_add_le_left hsz)
  have hrest : rest ≤ (Multiset.range 109).map Int.ofNat := Multiset.sub_le_self _ _
  have hrange : r ∈ sinkPositionRange := by
    apply mem_position_range_of_interval
    apply Multiset.mem_of_le (hr.trans hrest)
    simp [sinkRectangle, zbranch, zshift]
  have srange : s ∈ sinkPositionRange := by
    apply mem_position_range_of_interval
    apply Multiset.mem_of_le (hs.trans ((Multiset.sub_le_self _ _).trans hrest))
    simp [sinkPair, zbranch, zshift]
  have zrange : z ∈ sinkPositionRange := by
    apply mem_position_range_of_interval
    exact Multiset.mem_of_le ((Multiset.sub_le_self _ _).trans
      ((Multiset.sub_le_self _ _).trans hrest)) hz
  have allowed (x : ℤ) (hx : x ∈ sinkExceptions c) : sinkAllowedPosition box x := by
    simpa only [sinkAllowedPosition, hb.2.2.2.1] using
      interval_sink_allowed_positions c hi x hx
  have har : sinkAllowedPosition box r := allowed r (by
    rw [hex]; simp [sinkRectangle, zbranch, zshift])
  have has : sinkAllowedPosition box s := allowed s (by
    rw [hex]; simp [sinkPair, zbranch, zshift])
  have haz : sinkAllowedPosition box z := allowed z (by rw [hex]; simp)
  have hf := interval_sink_position_fingerprint c hd hi
  rw [hex, hb.2.2.2.1] at hf
  have hzfp : alternatingDigit box.d1 z = alternatingTarget box.d1 -
      alternatingSum box.d1 (sinkRectangle box r + sinkPair box s) := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [alternatingSum, Multiset.map_add, Multiset.sum_add,
      Multiset.map_singleton, Multiset.sum_singleton, add_comm] using hf
  unfold sinkPositionChoices sinkRectangleStarts sinkPositionChoicesAt
  exact List.mem_flatMap.mpr ⟨r,
    List.mem_filter.mpr ⟨hrange, by simpa only [decide_eq_true_eq] using And.intro har hr⟩,
    List.mem_flatMap.mpr ⟨s,
      List.mem_filter.mpr ⟨srange, by simpa only [decide_eq_true_eq] using And.intro has hs⟩,
      List.mem_map.mpr ⟨z,
        List.mem_filter.mpr ⟨zrange, by
          simpa only [decide_eq_true_eq] using And.intro haz (And.intro hz hzfp)⟩, rfl⟩⟩⟩

/-- Combine complete position coverage with the full-shape classifier. The
remaining outer choices are the box roles; this theorem assumes no fixture list. -/
theorem sink_outer_positions_complete (c box : GaugeCoordinates)
    (hb : SameSinkBox c box) (hd : 0 < c.d1)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    (c.A1 + c.p, c.A2 + c.p, c.A3 + c.p) ∈ sinkPositionChoices box ∧
    c.A3 ∈ sinkIntervalAnchors box (c.A1 + c.p) (c.A2 + c.p) (c.A3 + c.p) :=
  ⟨sinkPositionChoices_complete c box hb hd hi,
    sinkIntervalAnchors_complete c box hb hd hi⟩

/-- Once actual positions and the anchor are fixed, an interval completion
is unique. Exact halving forces the same prescribed half in both tuples. -/
theorem interval_same_sink_inputs_unique (c c' : GaugeCoordinates)
    (hb : SameSinkBox c c') (hd : 0 < c.d1)
    (hr : c.A1 + c.p = c'.A1 + c'.p)
    (hs : c.A2 + c.p = c'.A2 + c'.p)
    (hz : c.A3 + c.p = c'.A3 + c'.p) (ha : c.A3 = c'.A3)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat)
    (hi' : coordinateWeights c' = (Multiset.range 109).map Int.ofNat) : c = c' := by
  have hbox : coordinateBox c = coordinateBox c' := by
    obtain ⟨hu, hv, hw, hd1, hd2, hd3, ht⟩ := hb
    simp only [coordinateBox, hu, hv, hw, hd1, hd2, hd3, ht]
  have hex : sinkExceptions c = sinkExceptions c' := by
    rw [sinkExceptions_eq_placed, sinkExceptions_eq_placed, hr, hs, hz]
    simp only [placedSinkExceptions, hb.1, hb.2.1]
  have half (d : GaugeCoordinates) (hd : 0 < d.d1)
      (hi : coordinateWeights d = (Multiset.range 109).map Int.ofNat) :
      halve d.d1 (((Multiset.range 109).map Int.ofNat - coordinateBox d) -
        sinkExceptions d) = some (sinkHalf d) := by
    apply (halve_eq_some_iff _ hd _ _).mpr
    rw [← hi]
    simp only [coordinateWeights, add_tsub_cancel_left]
    rw [remainder_sink_factor, add_tsub_cancel_right]
  have hh := half c hd hi
  have hh' := half c' (by rw [← hb.2.2.2.1]; exact hd) hi'
  rw [hbox, hex, hb.2.2.2.1, hh'] at hh
  exact sink_coordinates_unique c c' hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
    hb.2.2.2.2.1 hb.2.2.2.2.2.1 hb.2.2.2.2.2.2 hr hs hz ha
    (Option.some.inj hh).symm

/-- Every original budget-108 labelling is covered at its actual positions.
No cap feasibility or completeness of an outer box enumeration is asserted. -/
theorem sink_positions_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    (c.A1 + c.p, c.A2 + c.p, c.A3 + c.p) ∈ sinkPositionChoices c ∧
    c.A3 ∈ sinkIntervalAnchors c (c.A1 + c.p) (c.A2 + c.p) (c.A3 + c.p) := by
  dsimp only
  exact sink_outer_positions_complete _ _ (by simp [SameSinkBox])
    (halving_of_budget B a b cap h1 hsteps hcap h109 hbudget).2.1
    (normalized_interval_of_budget B a b cap h1 hsteps hcap h109 hbudget)

end ScholzBrauer.Clift109
