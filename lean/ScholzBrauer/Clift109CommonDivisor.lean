import ScholzBrauer.Clift109Packing

/-! A common divisor of the two halving steps sees only one unpaired weight.
This uses the shape of the seven exceptions, beyond their cardinality. -/

namespace ScholzBrauer.Clift109

theorem sourceExceptions_pair (c : GaugeCoordinates) :
    zshift (rem5 c) c.A3 =
      zbranch (zshift ({0, c.d2} + {c.q}) c.A3) c.d1 + {c.A3 + c.p} := by
  simp [rem5, rem7, zSS, zbranch, zshift]
  simp only [Int.add_left_comm, Int.add_comm, ← Multiset.singleton_add]
  ac_rfl

/-- Modulo any common divisor, both paired contributions disappear. -/
theorem interval_common_divisor (c : GaugeCoordinates) (d : ℤ)
    (hu : d ∣ c.u) (hd : d ∣ c.d1)
    (h : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    intervalOddResidues d = {(c.A3 + c.p) % d} := by
  have hfu : ∀ x ∈ zshift (zSS [c.d3, c.d2, c.d1, c.w, c.v]) c.t + sourceHalf c,
      (x + c.u) % d = x % d := by
    intros
    simp [Int.add_emod, Int.emod_eq_zero_of_dvd hu]
  have hfd : ∀ x ∈ zshift ({0, c.d2} + {c.q}) c.A3,
      (x + c.d1) % d = x % d := by
    intros
    simp [Int.add_emod, Int.emod_eq_zero_of_dvd hd]
  have hs := oddLabels_paired c.u
    (zshift (zSS [c.d3, c.d2, c.d1, c.w, c.v]) c.t + sourceHalf c)
    (zshift (rem5 c) c.A3) (fun x => x % d) hfu
  rw [← weights_source_factor, h] at hs
  change intervalOddResidues d = _ at hs
  rw [sourceExceptions_pair] at hs
  rw [oddLabels_paired c.d1 _ _ (fun x => x % d) hfd] at hs
  rw [hs]
  ext q
  by_cases hq : q = (c.A3 + c.p) % d <;>
    simp [oddLabels, Multiset.count_singleton, hq]

/-- Only thirty possible gcd values remain after the joint packing bound. -/
theorem singleton_residue_check : ∀ d : Fin 30, 0 < d.val →
    ((intervalOddResidues (d.val : ℤ)).card = 1 ↔ d.val ∣ 54 ∨ d.val ∣ 55) := by
  intro d
  fin_cases d <;> decide +kernel

/-- The common divisor must divide 54 or 55. This is a necessary condition,
not feasibility of any surviving ordered pair. -/
theorem interval_gcd_restriction (c : GaugeCoordinates)
    (hu : 0 < c.u) (hd : 0 < c.d1) (hm : min c.u c.d1 ≤ 29)
    (h : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    Int.gcd c.u c.d1 ∣ 54 ∨ Int.gcd c.u c.d1 ∣ 55 := by
  have hg0 := Int.gcd_pos_of_ne_zero_left c.d1 (ne_of_gt hu)
  have hgu := Int.gcd_le_left c.d1 hu
  have hgd := Int.gcd_le_right c.u hd
  have hglt : Int.gcd c.u c.d1 < 30 := by omega
  have hf := interval_common_divisor c (Int.gcd c.u c.d1)
    (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _) h
  exact (singleton_residue_check ⟨_, hglt⟩ hg0).mp (by rw [hf]; simp)

/-- Applies the common-divisor obstruction to every original budget-108
labelling, using the proved normalization and packing reductions. -/
theorem gcd_restriction_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    Int.gcd c.u c.d1 ∣ 54 ∨ Int.gcd c.u c.d1 ∣ 55 := by
  have hp := halving_of_budget B a b cap h1 hsteps hcap h109 hbudget
  have hj := joint_steps_of_budget B a b cap h1 hsteps hcap h109 hbudget
  exact interval_gcd_restriction _ hp.1 hp.2.1 hj.2.2.2.2
    (normalized_interval_of_budget B a b cap h1 hsteps hcap h109 hbudget)

/-- A necessary ordered-pair domain, retaining all earlier residue and
packing restrictions and adding the common-divisor obstruction. -/
def commonDivisorPairs : Finset (ℤ × ℤ) :=
  (residueSteps.product residueSteps).filter (fun p =>
    p.1 ≠ p.2 ∧ p.1 + p.2 ≤ 93 ∧ (Int.gcd p.1 p.2 ∣ 54 ∨ Int.gcd p.1 p.2 ∣ 55))

theorem card_commonDivisorPairs : commonDivisorPairs.card = 606 := by decide +kernel

theorem common_divisor_pairs_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    (c.u, c.d1) ∈ commonDivisorPairs := by
  have hj := joint_steps_of_budget B a b cap h1 hsteps hcap h109 hbudget
  have hg := gcd_restriction_of_budget B a b cap h1 hsteps hcap h109 hbudget
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hj.1, hj.2.1⟩,
    hj.2.2.1, hj.2.2.2.1, hg⟩

end ScholzBrauer.Clift109
