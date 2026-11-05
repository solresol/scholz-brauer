import ScholzBrauer.Clift109SparseCheck

/-! Generated finite checks for one modulus. Every rejection is kernel reduced. -/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ScholzBrauer.Clift109

private theorem rejected_00 : sparseExcluded 28 3 = true := by
  decide +kernel

private theorem rejected_01 : sparseExcluded 28 5 = true := by
  decide +kernel

private theorem rejected_02 : sparseExcluded 28 6 = true := by
  decide +kernel

private theorem rejected_03 : sparseExcluded 28 11 = true := by
  decide +kernel

private theorem rejected_04 : sparseExcluded 28 51 = true := by
  decide +kernel

private theorem rejected_05 : sparseExcluded 28 53 = true := by
  decide +kernel

theorem sparseRejected_mod28 (d : ℤ)
    (hd : d ∈ ([3, 5, 6, 11, 51, 53] : List ℤ)) :
    sparseExcluded 28 d = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rejected_00
  · exact rejected_01
  · exact rejected_02
  · exact rejected_03
  · exact rejected_04
  · exact rejected_05

end ScholzBrauer.Clift109
