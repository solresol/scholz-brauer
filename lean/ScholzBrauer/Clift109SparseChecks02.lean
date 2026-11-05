import ScholzBrauer.Clift109SparseCheck

/-! Generated finite checks for one modulus. Every rejection is kernel reduced. -/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ScholzBrauer.Clift109

private theorem rejected_00 : sparseExcluded 17 5 = true := by
  decide +kernel

private theorem rejected_01 : sparseExcluded 17 6 = true := by
  decide +kernel

private theorem rejected_02 : sparseExcluded 17 7 = true := by
  decide +kernel

private theorem rejected_03 : sparseExcluded 17 8 = true := by
  decide +kernel

private theorem rejected_04 : sparseExcluded 17 9 = true := by
  decide +kernel

private theorem rejected_05 : sparseExcluded 17 11 = true := by
  decide +kernel

private theorem rejected_06 : sparseExcluded 17 26 = true := by
  decide +kernel

private theorem rejected_07 : sparseExcluded 17 27 = true := by
  decide +kernel

private theorem rejected_08 : sparseExcluded 17 28 = true := by
  decide +kernel

private theorem rejected_09 : sparseExcluded 17 29 = true := by
  decide +kernel

private theorem rejected_10 : sparseExcluded 17 56 = true := by
  decide +kernel

private theorem rejected_11 : sparseExcluded 17 57 = true := by
  decide +kernel

private theorem rejected_12 : sparseExcluded 17 58 = true := by
  decide +kernel

theorem sparseRejected_mod17 (d : ℤ)
    (hd : d ∈ ([5, 6, 7, 8, 9, 11, 26, 27, 28, 29, 56, 57, 58] : List ℤ)) :
    sparseExcluded 17 d = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

end ScholzBrauer.Clift109
