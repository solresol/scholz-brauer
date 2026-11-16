import ScholzBrauer.Clift109SinkPositionCapChecks00
import ScholzBrauer.Clift109SinkPositionCapChecks01
import ScholzBrauer.Clift109SinkPositionCapChecks02
import ScholzBrauer.Clift109SinkPositionCapChecks03

/-! Cap exclusion for the completely classified fixed box. All 64 signed
orientations and all endpoint-fixed gauges are covered by linear arithmetic.
The outer box-role classification, hence the full 109 exclusion, remains open. -/

namespace ScholzBrauer.Clift109

/-- None of the four interval completions admits nonnegative oriented edge
shifts within a total cap budget of 108. This includes every endpoint-fixed
gauge and all 64 orientations, with no assumed critical-path enumeration. -/
theorem sink_position_completions_cap_exclusion (c : GaugeCoordinates)
    (hmem : c ∈ sinkPositionCompletions) (o : Orientations)
    (g : ℕ → ℤ) (cap : ℕ → ℕ) (hg1 : g 1 = 0) (hg109 : g 109 = 0)
    (hc : ∀ s ∈ selectedSteps,
      (0 ≤ canonicalA (orientCoordinates c o) (s.1 + s.2) + g (s.1 + s.2) - g s.1 ∧
       canonicalA (orientCoordinates c o) (s.1 + s.2) + g (s.1 + s.2) - g s.1 ≤ cap s.1) ∧
      (0 ≤ canonicalB (orientCoordinates c o) (s.1 + s.2) + g (s.1 + s.2) - g s.2 ∧
       canonicalB (orientCoordinates c o) (s.1 + s.2) + g (s.1 + s.2) - g s.2 ≤ cap s.2))
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) : False := by
  simp only [sinkPositionCompletions, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact sink_position_cap_check_0 o g cap hg1 hg109 hc hbudget
  · exact sink_position_cap_check_1 o g cap hg1 hg109 hc hbudget
  · exact sink_position_cap_check_2 o g cap hg1 hg109 hc hbudget
  · exact sink_position_cap_check_3 o g cap hg1 hg109 hc hbudget

/-- Exclude every original budget-108 labelling with these seven minimum box
coordinates. Actual positions, anchors, orientation and gauge remain arbitrary. -/
theorem sink_position_box_no_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108)
    (hbox : SameSinkBox (minimumCoordinates (fun i => a i) (fun i => b i))
      sinkPositionBox) : False := by
  have hi := normalized_interval_of_budget B a b cap h1 hsteps hcap h109 hbudget
  have hm := sink_position_completions_complete _ hbox hi
  obtain ⟨o, g, hg1, hg109, hc⟩ := oriented_cap_constraints a b cap hcap
  exact sink_position_completions_cap_exclusion _ hm o g cap hg1 hg109 hc hbudget

end ScholzBrauer.Clift109
