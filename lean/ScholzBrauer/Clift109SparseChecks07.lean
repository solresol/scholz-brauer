import ScholzBrauer.Clift109SparseCheck

/-! Generated finite checks for one modulus. Every rejection is kernel reduced. -/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ScholzBrauer.Clift109

private theorem rejected_00 : sparseExcluded 51 5 = true := by
  decide +kernel

private theorem rejected_01 : sparseExcluded 51 6 = true := by
  decide +kernel

private theorem rejected_02 : sparseExcluded 51 7 = true := by
  decide +kernel

private theorem rejected_03 : sparseExcluded 51 8 = true := by
  decide +kernel

private theorem rejected_04 : sparseExcluded 51 9 = true := by
  decide +kernel

private theorem rejected_05 : sparseExcluded 51 11 = true := by
  decide +kernel

private theorem rejected_06 : sparseExcluded 51 13 = true := by
  decide +kernel

private theorem rejected_07 : sparseExcluded 51 14 = true := by
  decide +kernel

private theorem rejected_08 : sparseExcluded 51 18 = true := by
  decide +kernel

private theorem rejected_09 : sparseExcluded 51 26 = true := by
  decide +kernel

private theorem rejected_10 : sparseExcluded 51 27 = true := by
  decide +kernel

theorem sparseRejected_mod51 (d : ℤ)
    (hd : d ∈ ([5, 6, 7, 8, 9, 11, 13, 14, 18, 26, 27] : List ℤ)) :
    sparseExcluded 51 d = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

end ScholzBrauer.Clift109
