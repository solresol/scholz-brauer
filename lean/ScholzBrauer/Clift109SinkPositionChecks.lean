import ScholzBrauer.Clift109SinkPositions

/-! A full fixed-box position classification. This covers all actual exception
positions for these seven roles, not merely the previously saved fixture. -/

set_option Elab.async false

namespace ScholzBrauer.Clift109

/-- Only the seven box coordinates matter to the position enumeration. -/
def sinkPositionBox : GaugeCoordinates :=
  ⟨1, 2, 4, 51, 23, 8, 0, 0, 0, 0, 0, 0⟩

private theorem position_box_rest :
    (Multiset.range 109).map Int.ofNat - coordinateBox sinkPositionBox =
      ({16, 17, 18, 19, 20, 21, 22, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 67, 68, 69, 70, 71, 72, 73, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108} : Multiset ℤ) := by
  decide +kernel

private theorem position_odd_residues :
    intervalOddResidues 51 = {0, 1, 2, 3, 4, 5, 6} := by
  decide +kernel

private theorem position_allowed (x : ℤ) :
    sinkAllowedPosition sinkPositionBox x ↔ x % 51 ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset ℤ) := by
  change ((intervalOddResidues 51).card = 7 → x % 51 ∈ intervalOddResidues 51) ↔ _
  rw [position_odd_residues]
  norm_num

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Every residue-allowed rectangle start in the complement is enumerated. -/
theorem sink_position_rectangle_starts_checked :
    sinkRectangleStarts sinkPositionBox =
      [102, 103, 104, 105] := by
  unfold sinkRectangleStarts
  rw [position_box_rest]
  simp only [position_allowed]
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem position_at_102 :
    sinkPositionChoicesAt sinkPositionBox 102 = [(102, 106, 108), (102, 107, 106)] := by
  unfold sinkPositionChoicesAt
  rw [position_box_rest]
  simp only [position_allowed]
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem position_at_103 :
    sinkPositionChoicesAt sinkPositionBox 103 = [(103, 107, 102)] := by
  unfold sinkPositionChoicesAt
  rw [position_box_rest]
  simp only [position_allowed]
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem position_at_104 :
    sinkPositionChoicesAt sinkPositionBox 104 = [(104, 102, 108)] := by
  unfold sinkPositionChoicesAt
  rw [position_box_rest]
  simp only [position_allowed]
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem position_at_105 :
    sinkPositionChoicesAt sinkPositionBox 105 = [(105, 102, 104), (105, 103, 102)] := by
  unfold sinkPositionChoicesAt
  rw [position_box_rest]
  simp only [position_allowed]
  decide +kernel

/-- Complete enumeration of the six signed-fingerprint inputs for these roles.
Every rectangle branch is separately kernel checked and the exact list is composed. -/
theorem sink_position_box_choices_checked :
    sinkPositionChoices sinkPositionBox =
      [(102, 106, 108), (102, 107, 106), (103, 107, 102),
       (104, 102, 108), (105, 102, 104), (105, 103, 102)] := by
  simp only [sinkPositionChoices, sink_position_rectangle_starts_checked,
    List.flatMap_cons, List.flatMap_nil,
    position_at_102, position_at_103, position_at_104, position_at_105,
    List.nil_append, List.cons_append]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Full nineteen-weight shape, not the fingerprint alone, leaves four inputs. -/
theorem sink_position_box_anchors_checked :
    sinkIntervalAnchors sinkPositionBox 102 106 108 = ∅ ∧
    sinkIntervalAnchors sinkPositionBox 102 107 106 = {20} ∧
    sinkIntervalAnchors sinkPositionBox 103 107 102 = {16} ∧
    sinkIntervalAnchors sinkPositionBox 104 102 108 = {22} ∧
    sinkIntervalAnchors sinkPositionBox 105 102 104 = {18} ∧
    sinkIntervalAnchors sinkPositionBox 105 103 102 = ∅ := by
  decide +kernel

/-- EVERY interval tuple at these fixed roles has one of four actual-position
and anchor records. This is a complete fixed-box result, without cap feasibility. -/
theorem sink_position_box_complete (c : GaugeCoordinates)
    (hb : SameSinkBox c sinkPositionBox)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    (c.A1 + c.p, c.A2 + c.p, c.A3 + c.p, c.A3) ∈
      ([(102, 107, 106, 20), (103, 107, 102, 16),
        (104, 102, 108, 22), (105, 102, 104, 18)] : List (ℤ × ℤ × ℤ × ℤ)) := by
  have hd : 0 < c.d1 := by rw [hb.2.2.2.1]; decide
  obtain ⟨hp, ha⟩ := sink_outer_positions_complete c sinkPositionBox hb hd hi
  rw [sink_position_box_choices_checked] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := sink_position_box_anchors_checked
  rcases hp with hp | hp | hp | hp | hp | hp
  all_goals obtain ⟨hr, hs, hz⟩ := hp
  all_goals rw [hr, hs, hz] at ha ⊢
  · rw [h0] at ha; exact (Finset.notMem_empty _ ha).elim
  · rw [h1] at ha
    have hac : c.A3 = 20 := Finset.mem_singleton.mp ha
    simp [hac]
  · rw [h2] at ha
    have hac : c.A3 = 16 := Finset.mem_singleton.mp ha
    simp [hac]
  · rw [h3] at ha
    have hac : c.A3 = 22 := Finset.mem_singleton.mp ha
    simp [hac]
  · rw [h4] at ha
    have hac : c.A3 = 18 := Finset.mem_singleton.mp ha
    simp [hac]
  · rw [h5] at ha; exact (Finset.notMem_empty _ ha).elim

/-- The four whole coordinate tuples, retaining all prescribed graph roles. -/
def sinkPositionCompletions : List GaugeCoordinates :=
  [⟨1, 2, 4, 51, 23, 8, 0, 86, 30, 16, 21, 20⟩,
   ⟨1, 2, 4, 51, 23, 8, 0, 86, 30, 17, 21, 16⟩,
   ⟨1, 2, 4, 51, 23, 8, 0, 86, 28, 18, 16, 22⟩,
   ⟨1, 2, 4, 51, 23, 8, 0, 86, 28, 19, 16, 18⟩]

/-- The four listed tuples really solve the interval equation. -/
theorem sink_position_completions_valid (c : GaugeCoordinates)
    (hc : c ∈ sinkPositionCompletions) :
    SameSinkBox c sinkPositionBox ∧
      coordinateWeights c = (Multiset.range 109).map Int.ofNat := by
  simp only [sinkPositionCompletions, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals
    constructor
    · simp [SameSinkBox, sinkPositionBox]
    · decide +kernel

/-- No other coordinate tuple at these box roles solves the interval equation.
Position coverage and exact halving, rather than a saved fixture assumption,
prove completeness of this four-element list. -/
theorem sink_position_completions_complete (c : GaugeCoordinates)
    (hb : SameSinkBox c sinkPositionBox)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    c ∈ sinkPositionCompletions := by
  have hd : 0 < c.d1 := by rw [hb.2.2.2.1]; decide
  have hc := sink_position_box_complete c hb hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
  simp only [sinkPositionCompletions, List.mem_cons, List.not_mem_nil, or_false]
  rcases hc with hc | hc | hc | hc
  all_goals obtain ⟨hr, hs, hz, ha⟩ := hc
  · left
    apply interval_same_sink_inputs_unique c (⟨1, 2, 4, 51, 23, 8, 0, 86, 30, 16, 21, 20⟩ : GaugeCoordinates) (by simpa only [SameSinkBox, sinkPositionBox] using hb) hd
      hr hs hz ha hi
    decide +kernel
  · right; left
    apply interval_same_sink_inputs_unique c (⟨1, 2, 4, 51, 23, 8, 0, 86, 30, 17, 21, 16⟩ : GaugeCoordinates) (by simpa only [SameSinkBox, sinkPositionBox] using hb) hd
      hr hs hz ha hi
    decide +kernel
  · right; right; left
    apply interval_same_sink_inputs_unique c (⟨1, 2, 4, 51, 23, 8, 0, 86, 28, 18, 16, 22⟩ : GaugeCoordinates) (by simpa only [SameSinkBox, sinkPositionBox] using hb) hd
      hr hs hz ha hi
    decide +kernel
  · right; right; right
    apply interval_same_sink_inputs_unique c (⟨1, 2, 4, 51, 23, 8, 0, 86, 28, 19, 16, 18⟩ : GaugeCoordinates) (by simpa only [SameSinkBox, sinkPositionBox] using hb) hd
      hr hs hz ha hi
    decide +kernel

/-- Exact fixed-box coordinate classification. None of these four interval
configurations is asserted to admit the original nonnegative cap labelling. -/
theorem mem_sinkPositionCompletions_iff (c : GaugeCoordinates) :
    c ∈ sinkPositionCompletions ↔ SameSinkBox c sinkPositionBox ∧
      coordinateWeights c = (Multiset.range 109).map Int.ofNat :=
  ⟨sink_position_completions_valid c,
    fun h => sink_position_completions_complete c h.1 h.2⟩

end ScholzBrauer.Clift109
