import ScholzBrauer.Clift109SinkClassifier
import ScholzBrauer.Clift109CommonBoxExample

/-! Concrete checks of the fixed-input classifier. The positive fixture is an
interval configuration only; it is not a cap-feasible natural labelling. -/

namespace ScholzBrauer.Clift109

private def sinkClassifierFixture : GaugeCoordinates :=
  ⟨1, 2, 4, 51, 23, 8, 0, 86, 28, 18, 16, 22⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- A saved interval fixture is accepted at its unique anchor, with full shape. -/
theorem sink_classifier_fixture_checked :
    sinkIntervalAnchors sinkClassifierFixture 104 102 108 = {22} := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The relaxed same-box counterexample has NO prescribed-shape completion
at these actual exception positions, even after allowing a different anchor. -/
theorem sink_classifier_gap_checked :
    sinkIntervalAnchors commonBoxExample 66 69 1 = ∅ := by
  decide +kernel

/-- No coordinate tuple with these box roles and exception positions solves
the interval equation. The relaxed partitions therefore cannot be completed. -/
theorem common_box_gap_no_interval_completion :
    ¬ ∃ c : GaugeCoordinates, SameSinkBox c commonBoxExample ∧
      c.A1 + c.p = 66 ∧ c.A2 + c.p = 69 ∧ c.A3 + c.p = 1 ∧
      coordinateWeights c = (Multiset.range 109).map Int.ofNat := by
  rintro ⟨c, hb, hr, hs, hz, hi⟩
  have ha := sinkIntervalAnchors_complete c commonBoxExample hb
    (by rw [hb.2.2.2.1]; decide) hi
  rw [hr, hs, hz, sink_classifier_gap_checked] at ha
  exact Finset.notMem_empty _ ha

end ScholzBrauer.Clift109
