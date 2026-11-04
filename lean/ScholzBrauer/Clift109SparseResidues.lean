import ScholzBrauer.Clift109CommonDivisor

/-! Each seven-weight exception is three pairs at the *other* halving step
and one singleton. Retaining this shape strengthens the residue test. The
finite compatibility count is a separate computational result. -/

namespace ScholzBrauer.Clift109

/-- Three pairs and a singleton, with multiplicities retained. -/
def threePairWeights (d x y z s : ℤ) : Multiset ℤ :=
  zbranch {x, y, z} d + {s}

theorem sourceExceptions_three_pairs (c : GaugeCoordinates) :
    zshift (rem5 c) c.A3 =
      threePairWeights c.d1 c.A3 (c.A3 + c.d2) (c.A3 + c.q) (c.A3 + c.p) := by
  simp [threePairWeights, rem5, rem7, zSS, zbranch, zshift]
  simp only [Int.add_left_comm, Int.add_comm, ← Multiset.singleton_add]
  ac_rfl

theorem sinkExceptions_three_pairs (c : GaugeCoordinates) :
    sinkExceptions c = threePairWeights c.u (c.A1 + c.p)
      (c.A1 + c.p + c.v) (c.A2 + c.p) (c.A3 + c.p) := by
  simp [threePairWeights, sinkExceptions, zbranch, zshift]
  simp only [Int.add_left_comm, Int.add_comm, ← Multiset.singleton_add]
  ac_rfl

/-- Reducing the four starting points modulo m preserves every residue count.
No distinctness of the residues is assumed. -/
theorem threePairWeights_emod (m d x y z s : ℤ) :
    (threePairWeights d (x % m) (y % m) (z % m) (s % m)).map (· % m) =
      (threePairWeights d x y z s).map (· % m) := by
  simp [threePairWeights, zbranch, zshift, Int.add_emod]

/-- A finite necessary test: four residues in 0..m-1 must supply the exact
interval fingerprint as three pairs at step d and a singleton. -/
def threePairCompatible (m d : ℤ) : Prop :=
  ∃ x y z s : ℤ,
    (0 ≤ x ∧ x < m) ∧ (0 ≤ y ∧ y < m) ∧
    (0 ≤ z ∧ z < m) ∧ (0 ≤ s ∧ s < m) ∧
    intervalOddResidues m = oddLabels ((threePairWeights d x y z s).map (· % m))

theorem threePairCompatible_of_fingerprint (m d x y z s : ℤ) (hm : 0 < m)
    (h : intervalOddResidues m =
      oddLabels ((threePairWeights d x y z s).map (· % m))) :
    threePairCompatible m d := by
  have bounds : ∀ a : ℤ, 0 ≤ a % m ∧ a % m < m := fun a =>
    ⟨Int.emod_nonneg a (ne_of_gt hm), Int.emod_lt_of_pos a hm⟩
  refine ⟨x % m, y % m, z % m, s % m,
    bounds x, bounds y, bounds z, bounds s, ?_⟩
  rw [threePairWeights_emod]
  exact h

/-- Both exceptional fingerprints have the sparse form. This only uses the
proved interval equation, without any cap or enumeration premise. -/
theorem interval_three_pair_compatible (c : GaugeCoordinates)
    (hu : 0 < c.u) (hd : 0 < c.d1)
    (h : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    threePairCompatible c.u c.d1 ∧ threePairCompatible c.d1 c.u := by
  obtain ⟨_, _, hs, ht⟩ := interval_residues c hu hd h
  rw [sourceExceptions_three_pairs] at hs
  rw [sinkExceptions_three_pairs] at ht
  exact ⟨threePairCompatible_of_fingerprint _ _ _ _ _ _ hu hs,
    threePairCompatible_of_fingerprint _ _ _ _ _ _ hd ht⟩

/-- Applies both sparse tests and all previous step restrictions to every
original budget-108 labelling. Finite evaluation is not an assumed premise. -/
theorem three_pair_constraints_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    (c.u, c.d1) ∈ commonDivisorPairs ∧
      threePairCompatible c.u c.d1 ∧ threePairCompatible c.d1 c.u := by
  have hp := halving_of_budget B a b cap h1 hsteps hcap h109 hbudget
  exact ⟨common_divisor_pairs_of_budget B a b cap h1 hsteps hcap h109 hbudget,
    interval_three_pair_compatible _ hp.1 hp.2.1
      (normalized_interval_of_budget B a b cap h1 hsteps hcap h109 hbudget)⟩

end ScholzBrauer.Clift109
