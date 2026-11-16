import ScholzBrauer.Clift109SinkPositionChecks

/-! Cap exclusion for one completely classified fixed-box interval tuple.
Separate files keep kernel compilation within the unchanged command bound. -/

namespace ScholzBrauer.Clift109

set_option maxHeartbeats 2000000 in
/-- Every one of the 64 orientations, every endpoint-fixed integer gauge,
and every natural cap allocation of total at most 108 is excluded. -/
theorem sink_position_cap_check_0 (o : Orientations)
    (g : ℕ → ℤ) (cap : ℕ → ℕ) (hg1 : g 1 = 0) (hg109 : g 109 = 0)
    (hc : ∀ s ∈ selectedSteps,
      (0 ≤ canonicalA (orientCoordinates (⟨1, 2, 4, 51, 23, 8, 0, 86, 30, 16, 21, 20⟩ : GaugeCoordinates) o) (s.1 + s.2) + g (s.1 + s.2) - g s.1 ∧
       canonicalA (orientCoordinates (⟨1, 2, 4, 51, 23, 8, 0, 86, 30, 16, 21, 20⟩ : GaugeCoordinates) o) (s.1 + s.2) + g (s.1 + s.2) - g s.1 ≤ cap s.1) ∧
      (0 ≤ canonicalB (orientCoordinates (⟨1, 2, 4, 51, 23, 8, 0, 86, 30, 16, 21, 20⟩ : GaugeCoordinates) o) (s.1 + s.2) + g (s.1 + s.2) - g s.2 ∧
       canonicalB (orientCoordinates (⟨1, 2, 4, 51, 23, 8, 0, 86, 30, 16, 21, 20⟩ : GaugeCoordinates) o) (s.1 + s.2) + g (s.1 + s.2) - g s.2 ≤ cap s.2))
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) : False := by
  have hb : (cap 1 : ℤ) + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108 := by exact_mod_cast hbudget
  have e2 := hc (1, 1) (by decide)
  have e4 := hc (2, 2) (by decide)
  have e5 := hc (4, 1) (by decide)
  have e7 := hc (5, 2) (by decide)
  have e8 := hc (4, 4) (by decide)
  have e15 := hc (8, 7) (by decide)
  have e23 := hc (15, 8) (by decide)
  have e28 := hc (23, 5) (by decide)
  have e51 := hc (28, 23) (by decide)
  have e58 := hc (51, 7) (by decide)
  have e109 := hc (58, 51) (by decide)
  cases hu : o 0 <;> cases hv : o 1 <;> cases hw : o 2 <;>
    cases hd1 : o 3 <;> cases hd2 : o 4 <;> cases hd3 : o 5
  all_goals
    norm_num [orientCoordinates, signedDifference, hu, hv, hw, hd1, hd2, hd3,
      canonicalA, canonicalB, hg1, hg109] at e2 e4 e5 e7 e8 e15 e23 e28 e51 e58 e109
    linarith only [e2, e4, e5, e7, e8, e15, e23, e28, e51, e58, e109, hb]

end ScholzBrauer.Clift109
