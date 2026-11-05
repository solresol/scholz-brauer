import ScholzBrauer.Clift109SparseCheck

/-! Generated finite checks for one modulus. Every rejection is kernel reduced. -/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ScholzBrauer.Clift109

private theorem rejected_00 : sparseExcluded 14 3 = true := by
  decide +kernel

private theorem rejected_01 : sparseExcluded 14 11 = true := by
  decide +kernel

private theorem rejected_02 : sparseExcluded 14 17 = true := by
  decide +kernel

private theorem rejected_03 : sparseExcluded 14 53 = true := by
  decide +kernel

theorem sparseRejected_mod14 (d : ℤ)
    (hd : d ∈ ([3, 11, 17, 53] : List ℤ)) :
    sparseExcluded 14 d = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact rejected_00
  · exact rejected_01
  · exact rejected_02
  · exact rejected_03

end ScholzBrauer.Clift109
