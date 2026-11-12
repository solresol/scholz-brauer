import ScholzBrauer.Clift109AlternatingDomain
import ScholzBrauer.Clift109OddRuns

/-! A compatibility obstruction to a tempting intermediate reduction.
One common dissociated box, the actual two exceptional multisets of ONE
coordinate tuple, and a shared singleton still permit (u,d1)=(2,3).
The independent nineteen-weight halves below are not that tuple's prescribed
sourceHalf and sinkHalf. This is not a feasible graph labelling. -/

namespace ScholzBrauer.Clift109

def commonBoxExample : GaugeCoordinates :=
  ⟨2, 16, 8, 3, 4, 32, 0, -63, 2, 129, 132, 64⟩

private def exampleSourceHalf : Multiset ℤ :=
  {70, 73, 74, 77, 78, 81, 82, 85, 86, 89, 90, 93, 94, 97, 98, 101, 102, 105, 106}

private def exampleSinkHalf : Multiset ℤ :=
  {64, 70, 72, 74, 76, 78, 80, 85, 86, 87, 91, 92, 93, 97, 98, 99, 103, 104, 105}

/-- The common box is dissociated and fits [0,108], with two steps above one.
Its singleton is 1; the other four dimensions, including v and d2, are distinct. -/
theorem common_box_example_box :
    (coordinateBox commonBoxExample).Nodup ∧
    (coordinateBox commonBoxExample).card = 64 ∧
    commonBoxExample.u = 2 ∧ commonBoxExample.d1 = 3 ∧
    commonBoxExample.A3 + commonBoxExample.p = 1 ∧
    commonBoxExample.t + commonBoxExample.u + commonBoxExample.v + commonBoxExample.w +
      commonBoxExample.d1 + commonBoxExample.d2 + commonBoxExample.d3 ≤ 108 := by
  decide +kernel

/-- The actual source exceptions fit the interval complement of this box. -/
theorem common_box_example_source_partition :
    (Multiset.range 109).map Int.ofNat =
      coordinateBox commonBoxExample + zbranch exampleSourceHalf commonBoxExample.u +
        zshift (rem5 commonBoxExample) commonBoxExample.A3 := by
  decide +kernel

/-- The actual sink exceptions fit the SAME complement, at the SAME singleton. -/
theorem common_box_example_sink_partition :
    (Multiset.range 109).map Int.ofNat =
      coordinateBox commonBoxExample + zbranch exampleSinkHalf commonBoxExample.d1 +
        sinkExceptions commonBoxExample := by
  decide +kernel

/-- Both previously proved odd-run bounds hold on this common remainder.
They therefore do not remove the explicit (2,3) compatibility gap. -/
theorem common_box_example_odd_runs :
    let r := (Multiset.range 109).map Int.ofNat - coordinateBox commonBoxExample
    oddRunCount commonBoxExample.u r ≤ 7 ∧
      oddRunCount commonBoxExample.d1 r ≤ 7 := by
  dsimp only
  constructor
  · rw [common_box_example_source_partition]
    simp only [add_assoc, add_tsub_cancel_left]
    simpa only [card_sourceExceptions] using
      oddRunCount_le_exceptions commonBoxExample.u exampleSourceHalf
        (zshift (rem5 commonBoxExample) commonBoxExample.A3)
  · rw [common_box_example_sink_partition]
    simp only [add_assoc, add_tsub_cancel_left]
    simpa only [card_sinkExceptions] using
      oddRunCount_le_exceptions commonBoxExample.d1 exampleSinkHalf
        (sinkExceptions commonBoxExample)

/-- Neither relaxed half has the graph's required nineteen-weight shape. -/
theorem common_box_example_halves_mismatch :
    exampleSourceHalf ≠ sourceHalf commonBoxExample ∧
      exampleSinkHalf ≠ sinkHalf commonBoxExample := by
  decide +kernel

/-- The two relaxed partitions do not imply the coordinate interval equation.
Retaining the prescribed nineteen-weight halves is a separate obligation. -/
theorem common_box_example_not_interval :
    coordinateWeights commonBoxExample ≠ (Multiset.range 109).map Int.ofNat := by
  decide +kernel

end ScholzBrauer.Clift109
