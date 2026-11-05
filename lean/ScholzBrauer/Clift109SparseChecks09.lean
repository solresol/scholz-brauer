import ScholzBrauer.Clift109SparseChecks08

/-! Generated finite checks for one modulus. Every rejection is kernel reduced. -/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ScholzBrauer.Clift109

private theorem rejected_00 : sparseExcluded 53 3 = true := by
  decide +kernel

private theorem rejected_01 : sparseExcluded 53 4 = true := by
  decide +kernel

private theorem rejected_02 : sparseExcluded 53 5 = true := by
  decide +kernel

private theorem rejected_03 : sparseExcluded 53 6 = true := by
  decide +kernel

private theorem rejected_04 : sparseExcluded 53 7 = true := by
  decide +kernel

private theorem rejected_05 : sparseExcluded 53 8 = true := by
  decide +kernel

private theorem rejected_06 : sparseExcluded 53 9 = true := by
  decide +kernel

private theorem rejected_07 : sparseExcluded 53 11 = true := by
  decide +kernel

private theorem rejected_08 : sparseExcluded 53 13 = true := by
  decide +kernel

theorem sparseRejected_mod53 (d : ℤ)
    (hd : d ∈ ([3, 4, 5, 6, 7, 8, 9, 11, 13] : List ℤ)) :
    sparseExcluded 53 d = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rejected_00
  · exact rejected_01
  · exact rejected_02
  · exact rejected_03
  · exact rejected_04
  · exact rejected_05
  · exact rejected_06
  · exact rejected_07
  · exact rejected_08

end ScholzBrauer.Clift109
