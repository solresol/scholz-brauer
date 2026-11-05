import ScholzBrauer.Clift109SparseChecks10

/-! Generated finite checks for one modulus. Every rejection is kernel reduced. -/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ScholzBrauer.Clift109

private theorem rejected_00 : sparseExcluded 57 4 = true := by
  decide +kernel

private theorem rejected_01 : sparseExcluded 57 5 = true := by
  decide +kernel

private theorem rejected_02 : sparseExcluded 57 6 = true := by
  decide +kernel

private theorem rejected_03 : sparseExcluded 57 7 = true := by
  decide +kernel

private theorem rejected_04 : sparseExcluded 57 8 = true := by
  decide +kernel

private theorem rejected_05 : sparseExcluded 57 9 = true := by
  decide +kernel

private theorem rejected_06 : sparseExcluded 57 11 = true := by
  decide +kernel

private theorem rejected_07 : sparseExcluded 57 14 = true := by
  decide +kernel

private theorem rejected_08 : sparseExcluded 57 18 = true := by
  decide +kernel

private theorem rejected_09 : sparseExcluded 57 27 = true := by
  decide +kernel

private theorem rejected_10 : sparseExcluded 57 28 = true := by
  decide +kernel

private theorem rejected_11 : sparseExcluded 57 29 = true := by
  decide +kernel

theorem sparseRejected_mod57 (d : ℤ)
    (hd : d ∈ ([4, 5, 6, 7, 8, 9, 11, 14, 18, 27, 28, 29] : List ℤ)) :
    sparseExcluded 57 d = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

end ScholzBrauer.Clift109
