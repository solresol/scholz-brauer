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

/-- Six independent orientation bits; true selects the negative difference. -/
abbrev Orientations := Fin 6 → Bool

theorem card_orientations : Fintype.card Orientations = 64 := by
  decide +kernel

def signedDifference (negative : Bool) (d : ℤ) : ℤ := if negative then -d else d

/-- Invert minimum normalization after choosing the six signs. Offsets must
be restored as well; simply changing the signs would lose the remainder. -/
def orientCoordinates (c : GaugeCoordinates) (o : Orientations) : GaugeCoordinates :=
  let u := signedDifference (o 0) c.u
  let v := signedDifference (o 1) c.v
  let w := signedDifference (o 2) c.w
  let d1 := signedDifference (o 3) c.d1
  let d2 := signedDifference (o 4) c.d2
  let d3 := signedDifference (o 5) c.d3
  { u, v, w, d1, d2, d3
    t := c.t - min d3 0 - min d2 0 - min d1 0 - min w 0 - min v 0 - min u 0
    p := c.p + min d1 0 + min d2 0
    q := c.q + min d2 0
    A1 := c.A1 - min u 0 - min v 0 - min d1 0 - min d2 0
    A2 := c.A2 - min u 0 - min d1 0 - min d2 0
    A3 := c.A3 - min d1 0 - min d2 0 }

def coordinateSigns (c : GaugeCoordinates) : Orientations :=
  fun i => decide ((match i.val with
    | 0 => c.u | 1 => c.v | 2 => c.w | 3 => c.d1 | 4 => c.d2 | _ => c.d3) < 0)

private theorem signedDifference_abs (x : ℤ) :
    signedDifference (decide (x < 0)) |x| = x := by
  by_cases h : x < 0
  · simp [signedDifference, h, abs_of_neg h]
  · simp [signedDifference, h, abs_of_nonneg (by omega : 0 ≤ x)]

/-- Every signed tuple is recovered by one of the 64 orientations of its
normalized tuple, including zero differences. No positivity is assumed. -/
theorem orient_normalize (c : GaugeCoordinates) :
    orientCoordinates (normalizeCoordinates c) (coordinateSigns c) = c := by
  ext <;> simp only [orientCoordinates, coordinateSigns, normalizeCoordinates,
    signedDifference_abs] <;> omega

/-- Nonnegative normalized differences are the only condition needed for the
reverse identity. The other six coordinates may be arbitrary integers. -/
theorem normalize_orient (c : GaugeCoordinates) (o : Orientations)
    (hu : 0 ≤ c.u) (hv : 0 ≤ c.v) (hw : 0 ≤ c.w)
    (h1 : 0 ≤ c.d1) (h2 : 0 ≤ c.d2) (h3 : 0 ≤ c.d3) :
    normalizeCoordinates (orientCoordinates c o) = c := by
  have habs (b : Bool) (x : ℤ) (hx : 0 ≤ x) : |signedDifference b x| = x := by
    cases b <;> simp [signedDifference, abs_of_nonneg hx]
  ext <;> simp only [normalizeCoordinates, orientCoordinates,
    habs _ _ hu, habs _ _ hv, habs _ _ hw, habs _ _ h1, habs _ _ h2, habs _ _ h3] <;> omega

/-- Exact finite classification of the fibre of normalization. -/
theorem normalize_eq_iff (c n : GaugeCoordinates)
    (hu : 0 ≤ n.u) (hv : 0 ≤ n.v) (hw : 0 ≤ n.w)
    (h1 : 0 ≤ n.d1) (h2 : 0 ≤ n.d2) (h3 : 0 ≤ n.d3) :
    normalizeCoordinates c = n ↔ ∃ o : Orientations, c = orientCoordinates n o := by
  constructor
  · intro h
    exact ⟨coordinateSigns c, h ▸ (orient_normalize c).symm⟩
  · rintro ⟨o, rfl⟩
    exact normalize_orient n o hu hv hw h1 h2 h3

/-- Every orientation has exactly the normalized path-weight multiset. This
identity alone does not assert feasible nonnegative edges or a cap budget. -/
theorem oriented_weights (c : GaugeCoordinates) (o : Orientations)
    (hu : 0 ≤ c.u) (hv : 0 ≤ c.v) (hw : 0 ≤ c.w)
    (h1 : 0 ≤ c.d1) (h2 : 0 ≤ c.d2) (h3 : 0 ≤ c.d3) :
    weightsZ (canonicalA (orientCoordinates c o))
      (canonicalB (orientCoordinates c o)) stepsRev 109 = coordinateWeights c := by
  rw [canonical_weights]
  unfold coordinateWeights
  rw [coordinateBox_normalize, coordinateRemainder_normalize,
    normalize_orient c o hu hv hw h1 h2 h3]

/-- Cap feasibility transports to one of precisely six-bit oriented sections
of the minimum coordinates, preserving both endpoint potentials and every
lower/upper edge inequality. The original natural cap function is retained. -/
theorem oriented_cap_constraints (a b cap : ℕ → ℕ)
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2) :
    let n := minimumCoordinates (fun i => a i) (fun i => b i)
    ∃ o : Orientations, ∃ g : ℕ → ℤ, g 1 = 0 ∧ g 109 = 0 ∧ ∀ s ∈ selectedSteps,
      (0 ≤ canonicalA (orientCoordinates n o) (s.1 + s.2) + g (s.1 + s.2) - g s.1 ∧
        canonicalA (orientCoordinates n o) (s.1 + s.2) + g (s.1 + s.2) - g s.1 ≤ cap s.1) ∧
      (0 ≤ canonicalB (orientCoordinates n o) (s.1 + s.2) + g (s.1 + s.2) - g s.2 ∧
        canonicalB (orientCoordinates n o) (s.1 + s.2) + g (s.1 + s.2) - g s.2 ≤ cap s.2) := by
  dsimp only
  refine ⟨coordinateSigns (gaugeCoordinates (fun i => a i) (fun i => b i)), ?_⟩
  rw [← normalize_gaugeCoordinates, orient_normalize]
  exact canonical_cap_constraints a b cap hcap

end ScholzBrauer.Clift109
