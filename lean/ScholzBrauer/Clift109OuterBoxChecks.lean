import ScholzBrauer.Clift109OuterBoxes
import ScholzBrauer.Clift109SinkPositionChecks

/-! Small kernel evaluations of the outer generator and ordered-role replay.
No full 109-domain cardinality or interval-output classification is asserted. -/

namespace ScholzBrauer.Clift109
open CliftLabelling

theorem outer_dimensions_two_checked :
    dissociatedDimensions 2 1 5 = [[1,2], [1,3], [1,4], [2,3]] := by
  decide +kernel

theorem outer_dimensions_three_checked :
    dissociatedDimensions 3 1 7 = [[1,2,4]] := by
  decide +kernel

/-- The earlier completely classified box is retained with its actual roles,
including w=4 and d3=8. Interchanging them is a distinct outer input. -/
theorem sink_position_box_mem_outer_branch :
    sinkPositionBox ∈ outerBoxRolesAt [1,2,4,8,23,51] := by
  apply List.mem_flatMap.mpr
  refine ⟨[51,23,8,4,2,1], List.mem_permutations.mpr ?_, ?_⟩
  · decide +kernel
  · exact List.mem_map.mpr ⟨0, by decide +kernel, rfl⟩

end ScholzBrauer.Clift109
