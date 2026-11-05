import ScholzBrauer.Clift109SparseCheck

/-! Generated finite checks for one modulus. Every rejection is kernel reduced. -/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ScholzBrauer.Clift109

private theorem rejected_00 : sparseExcluded 19 4 = true := by
  decide +kernel

private theorem rejected_01 : sparseExcluded 19 5 = true := by
  decide +kernel

private theorem rejected_02 : sparseExcluded 19 6 = true := by
  decide +kernel

private theorem rejected_03 : sparseExcluded 19 7 = true := by
  decide +kernel

private theorem rejected_04 : sparseExcluded 19 8 = true := by
  decide +kernel

private theorem rejected_05 : sparseExcluded 19 9 = true := by
  decide +kernel

private theorem rejected_06 : sparseExcluded 19 11 = true := by
  decide +kernel

private theorem rejected_07 : sparseExcluded 19 14 = true := by
  decide +kernel

private theorem rejected_08 : sparseExcluded 19 26 = true := by
  decide +kernel

private theorem rejected_09 : sparseExcluded 19 27 = true := by
  decide +kernel

private theorem rejected_10 : sparseExcluded 19 28 = true := by
  decide +kernel

private theorem rejected_11 : sparseExcluded 19 29 = true := by
  decide +kernel

private theorem rejected_12 : sparseExcluded 19 51 = true := by
  decide +kernel

private theorem rejected_13 : sparseExcluded 19 52 = true := by
  decide +kernel

private theorem rejected_14 : sparseExcluded 19 53 = true := by
  decide +kernel

theorem sparseRejected_mod19 (d : ℤ)
    (hd : d ∈ ([4, 5, 6, 7, 8, 9, 11, 14, 26, 27, 28, 29, 51, 52, 53] : List ℤ)) :
    sparseExcluded 19 d = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rejected_00
  · exact rejected_01
  · exact rejected_02
  · exact rejected_03
  · exact rejected_04
  · exact rejected_05
  · exact rejected_06
  · exact rejected_07
  · exact rejected_08
  · exact rejected_09
  · exact rejected_10
  · exact rejected_11
  · exact rejected_12
  · exact rejected_13
  · exact rejected_14

end ScholzBrauer.Clift109
