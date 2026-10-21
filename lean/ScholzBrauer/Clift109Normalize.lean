import ScholzBrauer.Clift109Gauge

/-! The signed canonical representative may have negative edges. Integer path
weights supply the missing bridge to it. Absolute-value normalization preserves
all 109 weights, including multiplicities and the three remainder components. -/

namespace ScholzBrauer.CliftLabelling

/-- Integer version of `weights`, including signed canonical representatives. -/
def weightsZ (a b : ℕ → ℤ) : List (ℕ × ℕ) → ℕ → Multiset ℤ
  | [], v => if v = 1 then {0} else 0
  | s :: rest, v => if v = s.1 + s.2 then
      (weightsZ a b rest s.1).map (· + a v) +
      (weightsZ a b rest s.2).map (· + b v)
    else weightsZ a b rest v

/-- Casting the existing natural recursion gives exactly the integer recursion. -/
theorem weightsZ_cast (a b : ℕ → ℕ) (L : List (ℕ × ℕ)) (v : ℕ) :
    weightsZ (fun i => a i) (fun i => b i) L v =
      (weights a b L v).map Int.ofNat := by
  induction L generalizing v with
  | nil => by_cases hv : v = 1 <;> simp [weightsZ, weights, hv]
  | cons s L ih =>
    by_cases hv : v = s.1 + s.2
    · simp [weightsZ, weights, hv, ih, Multiset.map_map]
    · simp [weightsZ, weights, hv, ih]

/-- Signed gauges telescope without a nonnegativity assumption on either edge set. -/
theorem weightsZ_gauge (a b a' b' : ℕ → ℤ) (g : ℕ → ℤ) (hg : g 1 = 0) :
    ∀ L : List (ℕ × ℕ), valid L = true →
      (∀ s ∈ L,
        a' (s.1 + s.2) = a (s.1 + s.2) + g (s.1 + s.2) - g s.1 ∧
        b' (s.1 + s.2) = b (s.1 + s.2) + g (s.1 + s.2) - g s.2) →
      ∀ v ∈ vals L,
        weightsZ a' b' L v = (weightsZ a b L v).map (· + g v)
  | [], _, _, v, hv => by
    simp only [vals, List.mem_singleton] at hv
    subst v
    simp [weightsZ, hg]
  | s :: rest, hL, hs, v, hv => by
    obtain ⟨hp, hq, hlt, hrest⟩ := valid_cons hL
    have hs' := fun t ht => hs t (List.mem_cons_of_mem s ht)
    simp only [vals, List.mem_cons] at hv
    rcases hv with rfl | hv
    · obtain ⟨ha, hb⟩ := hs s (List.mem_cons_self ..)
      simp only [weightsZ, ite_true, Multiset.map_add]
      rw [weightsZ_gauge a b a' b' g hg rest hrest hs' _ hp,
        weightsZ_gauge a b a' b' g hg rest hrest hs' _ hq]
      simp only [Multiset.map_map, Function.comp_def]
      congr 1 <;> congr 1 <;> funext w <;> omega
    · have hne : v ≠ s.1 + s.2 := (hlt v hv).ne
      simp only [weightsZ, if_neg hne]
      exact weightsZ_gauge a b a' b' g hg rest hrest hs' v hv

end ScholzBrauer.CliftLabelling

namespace ScholzBrauer.Clift109

open CliftLabelling

/-- Signed translation and subset sums retain occurrences, not just support. -/
def zshift (s : Multiset ℤ) (c : ℤ) : Multiset ℤ := s.map (· + c)
def zbranch (s : Multiset ℤ) (d : ℤ) : Multiset ℤ := s + zshift s d

def zSS : List ℤ → Multiset ℤ
  | [] => {0}
  | d :: ds => zbranch (zSS ds) d

theorem zshift_add (s t : Multiset ℤ) (c : ℤ) :
    zshift (s + t) c = zshift s c + zshift t c := by simp [zshift]

theorem zshift_shift (s : Multiset ℤ) (c d : ℤ) :
    zshift (zshift s c) d = zshift s (c + d) := by
  simp [zshift, Multiset.map_map, add_assoc]

theorem zbranch_shift (s : Multiset ℤ) (c d : ℤ) :
    zbranch (zshift s c) d = zshift (zbranch s d) c := by
  simp only [zbranch, zshift_add, zshift_shift]
  rw [add_comm c d]

theorem zbranch_abs (s : Multiset ℤ) (d : ℤ) :
    zbranch s d = zshift (zbranch s |d|) (min d 0) := by
  by_cases hd : 0 ≤ d
  · simp [abs_of_nonneg hd, min_eq_right hd, zshift]
  · have hd' : d ≤ 0 := by omega
    simp only [abs_of_nonpos hd', min_eq_left hd', zbranch, zshift_add, zshift_shift]
    simp [zshift, add_comm]

/-- Normalize any signed subset-sum box by translating its minimum to zero. -/
theorem zSS_abs (ds : List ℤ) :
    zSS ds = zshift (zSS (ds.map (fun d => |d|)))
      ((ds.map (fun d => min d 0)).sum) := by
  induction ds with
  | nil => simp [zSS, zshift]
  | cons d ds ih =>
    rw [zSS, ih, zbranch_shift, zbranch_abs, zshift_shift]
    simp only [List.map_cons, List.sum_cons, zSS]

/-- Five and seven terminal offsets of the two repeated detour bases. -/
def rem7 (c : GaugeCoordinates) : Multiset ℤ := zSS [c.d1, c.d2] + {c.p}
def rem5 (c : GaugeCoordinates) : Multiset ℤ := rem7 c + zshift (zSS [c.d1]) c.q

def coordinateBox (c : GaugeCoordinates) : Multiset ℤ :=
  zshift (zSS [c.d3, c.d2, c.d1, c.w, c.v, c.u]) c.t

def coordinateRemainder (c : GaugeCoordinates) : Multiset ℤ :=
  zshift (zbranch (zbranch (rem5 c) c.u) c.v) c.A1 +
  zshift (zbranch (rem7 c) c.u) c.A2 + zshift (rem5 c) c.A3

def coordinateWeights (c : GaugeCoordinates) : Multiset ℤ :=
  coordinateBox c + coordinateRemainder c

/-- Factor the signed canonical graph into the 64-path box and 28+10+7 remainder. -/
theorem canonical_weights (c : GaugeCoordinates) :
    weightsZ (canonicalA c) (canonicalB c) stepsRev 109 = coordinateWeights c := by
  simp [weightsZ, stepsRev, selectedSteps, canonicalA, canonicalB,
    coordinateWeights, coordinateBox, coordinateRemainder, rem5, rem7, zSS,
    zbranch, zshift]
  simp only [Int.add_left_comm, Int.add_comm, ← Multiset.singleton_add]
  ac_rfl

/-- Every natural labelling has the signed coordinate decomposition, even when
its canonical representative has negative edges. -/
theorem weights_coordinates (a b : ℕ → ℕ) :
    (weights a b stepsRev 109).map Int.ofNat =
      coordinateWeights (gaugeCoordinates (fun i => a i) (fun i => b i)) := by
  let aZ : ℕ → ℤ := fun i => a i
  let bZ : ℕ → ℤ := fun i => b i
  obtain ⟨h1, h109, hs⟩ := gauge_reconstruction aZ bZ
  have h := weightsZ_gauge (canonicalA (gaugeCoordinates aZ bZ))
    (canonicalB (gaugeCoordinates aZ bZ)) aZ bZ (gaugePotential aZ bZ)
    h1 stepsRev stepsRev_valid (fun s hs' => hs s (List.mem_reverse.mp hs'))
    109 (by rw [vals_stepsRev]; decide)
  simp only [h109, add_zero, Multiset.map_id'] at h
  rw [canonical_weights] at h
  exact (weightsZ_cast a b stepsRev 109).symm.trans h

/-- The absolute differences and minimum offsets used by the finite experiment.
Only the six differences are forced nonnegative; p and q may remain signed. -/
def normalizeCoordinates (c : GaugeCoordinates) : GaugeCoordinates where
  u := |c.u|
  v := |c.v|
  w := |c.w|
  d1 := |c.d1|
  d2 := |c.d2|
  d3 := |c.d3|
  t := c.t + min c.d3 0 + min c.d2 0 + min c.d1 0 +
    min c.w 0 + min c.v 0 + min c.u 0
  p := c.p - (min c.d1 0 + min c.d2 0)
  q := c.q - min c.d2 0
  A1 := c.A1 + min c.u 0 + min c.v 0 + min c.d1 0 + min c.d2 0
  A2 := c.A2 + min c.u 0 + min c.d1 0 + min c.d2 0
  A3 := c.A3 + min c.d1 0 + min c.d2 0

theorem rem7_normalize (c : GaugeCoordinates) :
    rem7 c = zshift (rem7 (normalizeCoordinates c)) (min c.d1 0 + min c.d2 0) := by
  unfold rem7
  rw [zSS_abs [c.d1, c.d2]]
  simp [normalizeCoordinates, zshift, add_assoc]

theorem rem5_normalize (c : GaugeCoordinates) :
    rem5 c = zshift (rem5 (normalizeCoordinates c)) (min c.d1 0 + min c.d2 0) := by
  unfold rem5
  rw [rem7_normalize, zSS_abs [c.d1]]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    zshift_add, zshift_shift, normalizeCoordinates]
  congr 1
  congr 1
  omega

/-- Sign choices do not affect the translated box. -/
theorem coordinateBox_normalize (c : GaugeCoordinates) :
    coordinateBox c = coordinateBox (normalizeCoordinates c) := by
  unfold coordinateBox
  rw [zSS_abs, zshift_shift]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    normalizeCoordinates]
  congr 1
  omega

/-- The same minimum translations normalize all three remainder components. -/
theorem coordinateRemainder_normalize (c : GaugeCoordinates) :
    coordinateRemainder c = coordinateRemainder (normalizeCoordinates c) := by
  unfold coordinateRemainder
  simp only [rem5_normalize c, rem7_normalize c, zbranch_shift, zshift_shift]
  rw [zbranch_abs _ c.u, zbranch_shift, zbranch_abs _ c.v,
    zbranch_abs _ c.u]
  simp only [zshift_shift, normalizeCoordinates]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · exact congrArg (zshift _) (by omega)
    · exact congrArg (zshift _) (by omega)
  · exact congrArg (zshift _) (by omega)

/-- Full normalized 64+45 multiset identity for arbitrary natural edge shifts. -/
theorem weights_normalized (a b : ℕ → ℕ) :
    (weights a b stepsRev 109).map Int.ofNat =
      coordinateWeights (normalizeCoordinates
        (gaugeCoordinates (fun i => a i) (fun i => b i))) := by
  rw [weights_coordinates]
  unfold coordinateWeights
  rw [coordinateBox_normalize, coordinateRemainder_normalize]

/-- Direct minimum/absolute-value readout, matching `invariants` in the saved
109 experiment. This identifies the formulas, not execution of the Python code. -/
def minimumCoordinates (a b : ℕ → ℤ) : GaugeCoordinates :=
  let base7 := b 15 + a 23 + min (a 28 + a 51) (b 51) + min (a 58 + a 109) (b 109)
  { u := |a 2 - b 2|, v := |a 4 - b 4|, w := |a 8 - b 8|
    d1 := |a 58 + a 109 - b 109|, d2 := |a 28 + a 51 - b 51|
    d3 := |a 15 + a 23 - b 23|
    t := min (a 2) (b 2) + min (a 4) (b 4) + min (a 8) (b 8) +
      min (a 15 + a 23) (b 23) + min (a 28 + a 51) (b 51) +
      min (a 58 + a 109) (b 109)
    p := b 58 + a 109 - base7
    q := b 28 + a 51 + min (a 58 + a 109) (b 109) - a 7 - base7
    A1 := min (a 2) (b 2) + min (a 4) (b 4) + a 5 + a 7 + base7
    A2 := min (a 2) (b 2) + b 7 + base7
    A3 := b 5 + a 7 + base7 }

private theorem min_sub_zero (x y : ℤ) : min (x - y) 0 = min x y - y := by omega

/-- The signed normalization is exactly the minimum-based coordinate readout. -/
theorem normalize_gaugeCoordinates (a b : ℕ → ℤ) :
    normalizeCoordinates (gaugeCoordinates a b) = minimumCoordinates a b := by
  ext <;> simp only [normalizeCoordinates, gaugeCoordinates, minimumCoordinates,
    min_sub_zero] <;> omega

/-- A budget-108 labelling gives the exact normalized interval equation used
by the enumeration, with multiplicities preserved. No enumeration is assumed. -/
theorem normalized_interval_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    coordinateWeights (minimumCoordinates (fun i => a i) (fun i => b i)) =
      (Multiset.range 109).map Int.ofNat := by
  rw [← normalize_gaugeCoordinates, ← weights_normalized,
    weights_range_of_budget B a b cap h1 hsteps hcap h109 hbudget]

/-- Transport outgoing cap inequalities to the signed integral section.
These are exact integer difference constraints, with endpoint potentials fixed. -/
theorem canonical_cap_constraints (a b cap : ℕ → ℕ)
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2) :
    let c := gaugeCoordinates (fun i => a i) (fun i => b i)
    ∃ g : ℕ → ℤ, g 1 = 0 ∧ g 109 = 0 ∧ ∀ s ∈ selectedSteps,
      (0 ≤ canonicalA c (s.1 + s.2) + g (s.1 + s.2) - g s.1 ∧
        canonicalA c (s.1 + s.2) + g (s.1 + s.2) - g s.1 ≤ cap s.1) ∧
      (0 ≤ canonicalB c (s.1 + s.2) + g (s.1 + s.2) - g s.2 ∧
        canonicalB c (s.1 + s.2) + g (s.1 + s.2) - g s.2 ≤ cap s.2) := by
  dsimp only
  obtain ⟨h1, h109, hs⟩ := gauge_reconstruction (fun i => (a i : ℤ)) (fun i => (b i : ℤ))
  refine ⟨gaugePotential (fun i => a i) (fun i => b i), h1, h109, ?_⟩
  intro s hmem
  obtain ⟨ha, hb⟩ := hs s hmem
  obtain ⟨hca, hcb⟩ := hcap s hmem
  rw [← ha, ← hb]
  exact ⟨⟨Int.natCast_nonneg _, Int.ofNat_le.mpr hca⟩,
    ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr hcb⟩⟩

end ScholzBrauer.Clift109
