import ScholzBrauer.Clift109SparseChecks

/-! A 344-pair necessary domain, with every removal kernel checked.
Membership is not a claim of interval or cap feasibility. -/

namespace ScholzBrauer.Clift109

def sparseStepPairs : Finset (ℤ × ℤ) :=
  commonDivisorPairs.filter (fun p =>
    p ∉ sparseRejectedDirections ∧ (p.2, p.1) ∉ sparseRejectedDirections)

theorem card_sparseStepPairs : sparseStepPairs.card = 344 := by decide +kernel

theorem two_three_mem_sparseStepPairs : (2, 3) ∈ sparseStepPairs := by decide +kernel

theorem sparse_pairs_of_constraints (u d : ℤ) (hu : 0 < u) (hd : 0 < d)
    (hp : (u, d) ∈ commonDivisorPairs)
    (hs : threePairCompatible u d) (ht : threePairCompatible d u) :
    (u, d) ∈ sparseStepPairs := by
  have not_rejected (m e : ℤ) (hm : 0 < m) (hc : threePairCompatible m e) :
      (m, e) ∉ sparseRejectedDirections := by
    intro hmem
    have hf := sparseRejectedDirections_checked (m, e) hmem
    exact sparseExcluded_sound m e hm hf hc
  exact Finset.mem_filter.mpr ⟨hp, not_rejected u d hu hs, not_rejected d u hd ht⟩

/-- Every original selected-109 budget-108 labelling has its two normalized
halving steps in the kernel-checked 344-pair domain. -/
theorem sparse_pairs_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    (c.u, c.d1) ∈ sparseStepPairs := by
  have hpos := halving_of_budget B a b cap h1 hsteps hcap h109 hbudget
  obtain ⟨hp, hs, ht⟩ := three_pair_constraints_of_budget B a b cap h1 hsteps hcap h109 hbudget
  exact sparse_pairs_of_constraints _ _ hpos.1 hpos.2.1 hp hs ht

end ScholzBrauer.Clift109
