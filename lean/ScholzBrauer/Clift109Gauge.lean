import ScholzBrauer.Clift109Box

/-! Integer gauge coordinates for the selected 109 graph. The signed
coordinates avoid choosing orientations; nonnegative shifts are imposed on
the reconstructed labelling, not on its canonical representative. -/

namespace ScholzBrauer.CliftLabelling

/-- An integer vertex potential telescopes along every path. The original
and transformed edge shifts are natural, but the potential may be negative. -/
theorem weights_gauge (a b a' b' : ℕ → ℕ) (g : ℕ → ℤ) (hg : g 1 = 0) :
    ∀ L : List (ℕ × ℕ), valid L = true →
      (∀ s ∈ L,
        (a' (s.1 + s.2) : ℤ) = a (s.1 + s.2) + g (s.1 + s.2) - g s.1 ∧
        (b' (s.1 + s.2) : ℤ) = b (s.1 + s.2) + g (s.1 + s.2) - g s.2) →
      ∀ v ∈ vals L,
        (weights a' b' L v).map Int.ofNat =
          (weights a b L v).map (fun w : ℕ => (w : ℤ) + g v)
  | [], _, _, v, hv => by
    simp only [vals, List.mem_singleton] at hv
    subst v
    simp [weights, hg]
  | s :: rest, hL, hs, v, hv => by
    obtain ⟨hp, hq, hlt, hrest⟩ := valid_cons hL
    have hs' := fun t ht => hs t (List.mem_cons_of_mem s ht)
    simp only [vals, List.mem_cons] at hv
    rcases hv with rfl | hv
    · obtain ⟨ha, hb⟩ := hs s (List.mem_cons_self ..)
      simp only [weights, ite_true, Multiset.map_add]
      have transport (p c c' : ℕ) (hc : (c' : ℤ) = c + g (s.1 + s.2) - g p)
          (hp' : p ∈ vals rest) :
          ((weights a' b' rest p).map (· + c')).map Int.ofNat =
            ((weights a b rest p).map (· + c)).map
              (fun w : ℕ => (w : ℤ) + g (s.1 + s.2)) := by
        have ih := weights_gauge a b a' b' g hg rest hrest hs' p hp'
        have hi := congrArg (Multiset.map (fun w : ℤ => w + c')) ih
        simp only [Multiset.map_map, Function.comp_def] at hi ⊢
        simp only [Nat.cast_add] at hi ⊢
        convert hi using 1
        congr 1
        funext w
        omega
      rw [transport _ _ _ ha hp, transport _ _ _ hb hq]
    · have hne : v ≠ s.1 + s.2 := (hlt v hv).ne
      simp only [weights, if_neg hne]
      exact weights_gauge a b a' b' g hg rest hrest hs' v hv

end ScholzBrauer.CliftLabelling

namespace ScholzBrauer.Clift109

/-- Twelve signed invariants; the last three name the non-box components.
These are coordinates before absolute-value/minimum orientation normalization. -/
@[ext] structure GaugeCoordinates where
  u : ℤ
  v : ℤ
  w : ℤ
  d1 : ℤ
  d2 : ℤ
  d3 : ℤ
  t : ℤ
  p : ℤ
  q : ℤ
  A1 : ℤ
  A2 : ℤ
  A3 : ℤ

def gaugeCoordinates (a b : ℕ → ℤ) : GaugeCoordinates where
  u := a 2 - b 2
  v := a 4 - b 4
  w := a 8 - b 8
  d1 := a 58 + a 109 - b 109
  d2 := a 28 + a 51 - b 51
  d3 := a 15 + a 23 - b 23
  t := b 2 + b 4 + b 8 + b 23 + b 51 + b 109
  p := b 58 + a 109 - b 15 - a 23 - b 51 - b 109
  q := b 28 + a 51 - a 7 - b 15 - a 23 - b 51
  A1 := a 5 + b 2 + b 4 + a 7 + b 15 + a 23 + b 51 + b 109
  A2 := b 7 + b 2 + b 15 + a 23 + b 51 + b 109
  A3 := b 5 + a 7 + b 15 + a 23 + b 51 + b 109

def canonicalA (c : GaugeCoordinates) : ℕ → ℤ
  | 2 => c.u | 4 => c.v | 5 => c.A1 | 8 => c.w + c.t
  | 15 => c.d3 | 28 => c.d2 | 58 => c.d1 | _ => 0

def canonicalB (c : GaugeCoordinates) : ℕ → ℤ
  | 5 => c.A3 | 7 => c.A2 | 8 => c.t | 28 => c.q | 58 => c.p | _ => 0

/-- The ten interior potentials; both endpoints are pinned to zero. -/
def gaugePotential (a b : ℕ → ℤ) : ℕ → ℤ
  | 2 => b 2
  | 4 => b 2 + b 4
  | 5 => -b 109 - b 51 - a 23 - b 15 - a 7
  | 7 => -b 109 - b 51 - a 23 - b 15
  | 8 => -b 109 - b 51 - b 23
  | 15 => -b 109 - b 51 - a 23
  | 23 => -b 109 - b 51
  | 28 => -b 109 - a 51
  | 51 => -b 109
  | 58 => -a 109
  | _ => 0

/-- An explicit integral section: every twelve-tuple is realized exactly.
Its representative need not have nonnegative edge shifts. -/
theorem gaugeCoordinates_section (c : GaugeCoordinates) :
    gaugeCoordinates (canonicalA c) (canonicalB c) = c := by
  ext <;> simp [gaugeCoordinates, canonicalA, canonicalB]

/-- Every signed labelling is its canonical representative plus an integer
gauge. No divisibility, linear-programming or matrix assumption is needed. -/
theorem gauge_reconstruction (a b : ℕ → ℤ) :
    gaugePotential a b 1 = 0 ∧ gaugePotential a b 109 = 0 ∧
    ∀ s ∈ selectedSteps,
      a (s.1 + s.2) = canonicalA (gaugeCoordinates a b) (s.1 + s.2) +
        gaugePotential a b (s.1 + s.2) - gaugePotential a b s.1 ∧
      b (s.1 + s.2) = canonicalB (gaugeCoordinates a b) (s.1 + s.2) +
        gaugePotential a b (s.1 + s.2) - gaugePotential a b s.2 := by
  refine ⟨rfl, rfl, ?_⟩
  intro s hs
  simp only [selectedSteps, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [gaugeCoordinates, canonicalA, canonicalB, gaugePotential] <;> omega

/-- The twelve coordinates are invariant under every endpoint-fixed gauge. -/
theorem gaugeCoordinates_invariant (a b a' b' : ℕ → ℤ) (g : ℕ → ℤ)
    (h1 : g 1 = 0) (h109 : g 109 = 0)
    (hs : ∀ s ∈ selectedSteps,
      a' (s.1 + s.2) = a (s.1 + s.2) + g (s.1 + s.2) - g s.1 ∧
      b' (s.1 + s.2) = b (s.1 + s.2) + g (s.1 + s.2) - g s.2) :
    gaugeCoordinates a' b' = gaugeCoordinates a b := by
  have h2 := hs (1, 1) (by decide)
  have h4 := hs (2, 2) (by decide)
  have h5 := hs (4, 1) (by decide)
  have h7 := hs (5, 2) (by decide)
  have h8 := hs (4, 4) (by decide)
  have h15 := hs (8, 7) (by decide)
  have h23 := hs (15, 8) (by decide)
  have h28 := hs (23, 5) (by decide)
  have h51 := hs (28, 23) (by decide)
  have h58 := hs (51, 7) (by decide)
  have h := hs (58, 51) (by decide)
  norm_num at h2 h4 h5 h7 h8 h15 h23 h28 h51 h58 h
  ext <;> dsimp [gaugeCoordinates] <;> omega

/-- Equality of the signed coordinates is equivalent to integer gauge
equivalence. This is a complete description, not just an invariant. -/
theorem gaugeCoordinates_eq_iff (a b a' b' : ℕ → ℤ) :
    gaugeCoordinates a' b' = gaugeCoordinates a b ↔
    ∃ g : ℕ → ℤ, g 1 = 0 ∧ g 109 = 0 ∧
      ∀ s ∈ selectedSteps,
        a' (s.1 + s.2) = a (s.1 + s.2) + g (s.1 + s.2) - g s.1 ∧
        b' (s.1 + s.2) = b (s.1 + s.2) + g (s.1 + s.2) - g s.2 := by
  constructor
  · intro hc
    refine ⟨fun v => gaugePotential a' b' v - gaugePotential a b v,
      by rfl, by rfl, ?_⟩
    intro s hs
    obtain ⟨ha, hb⟩ := (gauge_reconstruction a b).2.2 s hs
    obtain ⟨ha', hb'⟩ := (gauge_reconstruction a' b').2.2 s hs
    rw [hc] at ha' hb'
    constructor <;> dsimp only <;> omega
  · rintro ⟨g, h1, h109, hs⟩
    exact gaugeCoordinates_invariant a b a' b' g h1 h109 hs

/-- The integral normal form preserves the existing natural path-weight
multiset whenever both reconstructed labellings have nonnegative shifts. -/
theorem weights_eq_of_gaugeCoordinates_eq (a b a' b' : ℕ → ℕ)
    (hc : gaugeCoordinates (fun v => a' v) (fun v => b' v) =
      gaugeCoordinates (fun v => a v) (fun v => b v)) :
    CliftLabelling.weights a' b' stepsRev 109 =
      CliftLabelling.weights a b stepsRev 109 := by
  obtain ⟨g, h1, h109, hs⟩ := (gaugeCoordinates_eq_iff _ _ _ _).mp hc
  have h := CliftLabelling.weights_gauge a b a' b' g h1 stepsRev stepsRev_valid
    (fun s hs' => hs s (List.mem_reverse.mp hs'))
    109 (by rw [vals_stepsRev]; decide)
  simp only [h109, add_zero] at h
  exact Multiset.map_injective Int.ofNat_injective h

end ScholzBrauer.Clift109
