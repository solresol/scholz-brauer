import ScholzBrauer.Clift109SparseCheck

/-! Generated finite checks for one modulus. Every rejection is kernel reduced. -/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ScholzBrauer.Clift109

private theorem rejected_00 : sparseExcluded 52 5 = true := by
  decide +kernel

private theorem rejected_01 : sparseExcluded 52 6 = true := by
  decide +kernel

private theorem rejected_02 : sparseExcluded 52 7 = true := by
  decide +kernel

private theorem rejected_03 : sparseExcluded 52 9 = true := by
  decide +kernel

private theorem rejected_04 : sparseExcluded 52 11 = true := by
  decide +kernel

private theorem rejected_05 : sparseExcluded 52 14 = true := by
  decide +kernel

private theorem rejected_06 : sparseExcluded 52 17 = true := by
  decide +kernel

private theorem rejected_07 : sparseExcluded 52 18 = true := by
  decide +kernel

private theorem rejected_08 : sparseExcluded 52 27 = true := by
  decide +kernel

theorem sparseRejected_mod52 (d : ℤ)
    (hd : d ∈ ([5, 6, 7, 9, 11, 14, 17, 18, 27] : List ℤ)) :
    sparseExcluded 52 d = true := by
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
