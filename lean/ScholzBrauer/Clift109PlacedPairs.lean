import ScholzBrauer.Clift109SparseDomain

/-! Retain the actual positions of the three opposite-step pairs and their
shared singleton. Finite evaluation of this necessary condition is separate
computational evidence, not a kernel-checked enumeration theorem. -/

namespace ScholzBrauer.Clift109

/-- An exact partition of [0,108] into step-m pairs, three step-d pairs and
one singleton. Multiset equality requires all 109 positions to be distinct. -/
def intervalThreePairPlacement (m d s : ℤ) : Prop :=
  ∃ (x y z : ℤ) (a : Multiset ℤ),
    (Multiset.range 109).map Int.ofNat =
      zbranch a m + threePairWeights d x y z s

/-- The full interval supplies finite bounds and distinctness, even if the
original normalized coordinates were signed. There are exactly 51 m-pairs. -/
theorem interval_three_pair_bounds (m d s x y z : ℤ) (a : Multiset ℤ)
    (h : (Multiset.range 109).map Int.ofNat =
      zbranch a m + threePairWeights d x y z s) :
    (threePairWeights d x y z s).Nodup ∧
    (∀ r ∈ ({x, y, z} : Multiset ℤ), 0 ≤ r ∧ r + d < 109) ∧
    (0 ≤ s ∧ s < 109) ∧ a.card = 51 := by
  have hnd : ((Multiset.range 109).map Int.ofNat).Nodup :=
    (Multiset.nodup_range 109).map Int.ofNat_injective
  rw [h] at hnd
  have bounds : ∀ w ∈ threePairWeights d x y z s, 0 ≤ w ∧ w < 109 := by
    intro w hw
    have hi : w ∈ (Multiset.range 109).map Int.ofNat := by
      rw [h]
      exact Multiset.mem_add.mpr (Or.inr hw)
    obtain ⟨i, hmem, rfl⟩ := Multiset.mem_map.mp hi
    have := Multiset.mem_range.mp hmem
    change 0 ≤ (i : ℤ) ∧ (i : ℤ) < 109
    omega
  have hc := congrArg Multiset.card h
  simp [threePairWeights, zbranch, zshift] at hc
  refine ⟨(Multiset.nodup_add.mp hnd).2.1, ?_, ?_, by omega⟩
  · intro r hr
    have hr0 := bounds r (Multiset.mem_add.mpr (Or.inl
      (Multiset.mem_add.mpr (Or.inl hr))))
    have hr1 := bounds (r + d) (Multiset.mem_add.mpr (Or.inl
      (Multiset.mem_add.mpr (Or.inr (Multiset.mem_map.mpr ⟨r, hr, rfl⟩)))))
    exact ⟨hr0.1, hr1.2⟩
  · exact bounds s (by simp [threePairWeights])

/-- Both full-interval partitions retain the same actual singleton A3+p.
Separate residue witnesses need not share such a position. -/
theorem interval_three_pair_placements (c : GaugeCoordinates)
    (h : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    intervalThreePairPlacement c.u c.d1 (c.A3 + c.p) ∧
    intervalThreePairPlacement c.d1 c.u (c.A3 + c.p) := by
  constructor
  · refine ⟨c.A3, c.A3 + c.d2, c.A3 + c.q,
      zshift (zSS [c.d3, c.d2, c.d1, c.w, c.v]) c.t + sourceHalf c, ?_⟩
    rw [← sourceExceptions_three_pairs, ← weights_source_factor, h]
  · refine ⟨c.A1 + c.p, c.A1 + c.p + c.v, c.A2 + c.p,
      zshift (zSS [c.d3, c.d2, c.w, c.v, c.u]) c.t + sinkHalf c, ?_⟩
    rw [← sinkExceptions_three_pairs, ← weights_sink_factor, h]

/-- Every original budget-108 labelling satisfies the placed-pair test in
both directions at one shared singleton, in addition to the 344-pair domain. -/
theorem placed_pairs_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    (c.u, c.d1) ∈ sparseStepPairs ∧
      ∃ s : ℤ, (0 ≤ s ∧ s < 109) ∧
        intervalThreePairPlacement c.u c.d1 s ∧
        intervalThreePairPlacement c.d1 c.u s := by
  dsimp only
  have hi := normalized_interval_of_budget B a b cap h1 hsteps hcap h109 hbudget
  obtain ⟨hs, ht⟩ := interval_three_pair_placements _ hi
  refine ⟨sparse_pairs_of_budget B a b cap h1 hsteps hcap h109 hbudget,
    _, ?_, hs, ht⟩
  obtain ⟨x, y, z, half, hh⟩ := hs
  exact (interval_three_pair_bounds _ _ _ x y z half hh).2.2.1

end ScholzBrauer.Clift109
