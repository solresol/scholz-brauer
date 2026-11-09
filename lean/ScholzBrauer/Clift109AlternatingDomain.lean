import ScholzBrauer.Clift109AlternatingChecks

/-! A 278-pair necessary domain for every original budget-108 labelling.
This excludes finite pairs, not all interval/cap configurations. -/

namespace ScholzBrauer.Clift109

def alternatingStepPairs : Finset (ℤ × ℤ) :=
  sparseStepPairs.filter (fun p =>
    p ∉ alternatingRejectedDirections ∧ (p.2, p.1) ∉ alternatingRejectedDirections ∧
    p ∉ alternatingDisjointPairs ∧ (p.2, p.1) ∉ alternatingDisjointPairs)

theorem card_alternatingStepPairs : alternatingStepPairs.card = 278 := by decide +kernel

theorem two_three_mem_alternatingStepPairs : (2, 3) ∈ alternatingStepPairs := by decide +kernel

theorem alternating_pairs_of_placements (u d s : ℤ)
    (hp : (u, d) ∈ sparseStepPairs) (hs : 0 ≤ s ∧ s < 109)
    (hu : intervalThreePairPlacement u d s)
    (hd : intervalThreePairPlacement d u s) :
    (u, d) ∈ alternatingStepPairs := by
  refine Finset.mem_filter.mpr ⟨hp, ?_, ?_, ?_, ?_⟩
  · intro h
    exact alternatingRejectedDirections_checked (u, d) h s hs hu
  · intro h
    exact alternatingRejectedDirections_checked (d, u) h s hs hd
  · intro h
    exact alternatingDisjointPairs_checked (u, d) h s hs ⟨hu, hd⟩
  · intro h
    exact alternatingDisjointPairs_checked (d, u) h s hs ⟨hd, hu⟩

/-- Every original selected-109 budget-108 labelling lies in the audited
278-pair domain. Membership is not sufficient for graph feasibility. -/
theorem alternating_pairs_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    (c.u, c.d1) ∈ alternatingStepPairs := by
  obtain ⟨hp, s, hs, hu, hd⟩ := placed_pairs_of_budget B a b cap h1 hsteps hcap h109 hbudget
  exact alternating_pairs_of_placements _ _ s hp hs hu hd

end ScholzBrauer.Clift109
