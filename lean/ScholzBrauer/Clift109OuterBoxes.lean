import ScholzBrauer.Clift109SinkPositions
import ScholzBrauer.Clift109Packing
import ScholzBrauer.Clift109AlternatingDomain
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Permutation

/-! Complete outer box-role coverage. Sorted dissociated dimension lists are
enumerated once, then every permutation and every permitted translation is
retained. No saved list of interval fixtures is assumed. Evaluating the outer
branches and certifying their interval/cap outputs remain separate obligations. -/

namespace ScholzBrauer.CliftLabelling

private theorem length_mul_le_sum (lower : ℕ) (ds : List ℕ)
    (h : ∀ d ∈ ds, lower ≤ d) : lower * ds.length ≤ ds.sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem d hx))
    simp only [List.length_cons, List.sum_cons, Nat.mul_succ]
    omega

/-- Subset sums retain their multiplicities under a permutation of dimensions. -/
theorem subsetSums_perm {xs ys : List ℕ} (h : xs.Perm ys) :
    subsetSums xs = subsetSums ys := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [subsetSums, ih]
  | swap a b xs =>
    simp only [subsetSums, shift_add, shift_shift]
    rw [Nat.add_comm b a]
    ac_rfl
  | trans h h' ih ih' => exact ih.trans ih'

/-- Increasing (weakly, before dissociation) dimension lists within a span
budget. Reject repeated subset sums at every stage, retaining multiplicity. -/
def dissociatedDimensions : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => [[]]
  | n + 1, lower, budget =>
      ((List.range (budget / (n + 1) + 1)).filter (lower ≤ ·)).flatMap fun d =>
        ((dissociatedDimensions n d (budget - d)).filter fun ds =>
          (subsetSums (d :: ds)).Nodup).map (d :: ·)

/-- Exact specification of the dimension generator, at arbitrary bounds. -/
theorem mem_dissociatedDimensions (n lower budget : ℕ) (ds : List ℕ) :
    ds ∈ dissociatedDimensions n lower budget ↔
      ds.length = n ∧ ds.Pairwise (· ≤ ·) ∧
      (∀ d ∈ ds, lower ≤ d) ∧ ds.sum ≤ budget ∧ (subsetSums ds).Nodup := by
  induction n generalizing lower budget ds with
  | zero =>
    cases ds <;> simp [dissociatedDimensions, subsetSums]
  | succ n ih =>
    cases ds with
    | nil => simp [dissociatedDimensions]
    | cons d ds =>
      simp only [dissociatedDimensions, List.mem_flatMap, List.mem_filter,
        List.mem_range, List.mem_map, decide_eq_true_eq]
      constructor
      · rintro ⟨e, ⟨he, hlow⟩, tail, ⟨ht, hnd⟩, heq⟩
        cases heq
        have hed := (Nat.le_div_iff_mul_le (by omega : 0 < n + 1)).mp
          (by omega : d ≤ budget / (n + 1))
        rw [Nat.mul_succ] at hed
        obtain ⟨hlen, hsort, htail, hsum, hndtail⟩ := (ih _ _ _).mp ht
        refine ⟨by simp [hlen], List.pairwise_cons.mpr ⟨htail, hsort⟩,
          ?_, ?_, hnd⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hlow
          · exact hlow.trans (htail x hx)
        · simp only [List.sum_cons]
          omega
      · rintro ⟨hlen, hsort, hlow, hsum, hnd⟩
        obtain ⟨htail, hsort⟩ := List.pairwise_cons.mp hsort
        have hd : d ≤ budget := by simp only [List.sum_cons] at hsum; omega
        have hmul := length_mul_le_sum d (d :: ds) (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_rfl
          · exact htail x hx)
        have hdiv := (Nat.le_div_iff_mul_le (by omega : 0 < n + 1)).mpr
          (by simpa only [hlen] using hmul.trans hsum)
        refine ⟨d, ⟨by omega, hlow d (by simp)⟩, ds, ⟨?_, hnd⟩, rfl⟩
        apply (ih _ _ _).mpr
        refine ⟨by simpa using hlen, hsort, htail, ?_, ?_⟩
        · simp only [List.sum_cons] at hsum
          omega
        · exact Multiset.nodup_of_le (Multiset.le_add_right _ _) hnd

/-- Sorting loses no dissociated positive box, including its dimension roles
once the accompanying permutation is retained. -/
theorem sorted_dimensions_complete (ds : List ℕ) (hn : ds.length = 6)
    (hnd : (subsetSums ds).Nodup) (hp : ∀ d ∈ ds, 0 < d)
    (hb : ds.sum ≤ 108) :
    ds.mergeSort (· ≤ ·) ∈ dissociatedDimensions 6 1 108 ∧
      ds ∈ (ds.mergeSort (· ≤ ·)).permutations := by
  have hperm := List.mergeSort_perm ds (· ≤ ·)
  refine ⟨(mem_dissociatedDimensions _ _ _ _).mpr ⟨hperm.length_eq.trans hn,
    List.pairwise_mergeSort' (· ≤ ·) ds, ?_, ?_, ?_⟩,
    List.mem_permutations.mpr hperm.symm⟩
  · intro d hd
    exact hp d (hperm.mem_iff.mp hd)
  · simpa only [hperm.sum_eq] using hb
  · rw [subsetSums_perm hperm]
    exact hnd

end ScholzBrauer.CliftLabelling

namespace ScholzBrauer.Clift109
open CliftLabelling

/-- The original box-pair order is d1,d2,d3,w,v,u; do not forget these roles. -/
def boxRolePrototype (ds : List ℕ) (t : ℕ) : GaugeCoordinates :=
  match ds with
  | [d1,d2,d3,w,v,u] => ⟨u,v,w,d1,d2,d3,t,0,0,0,0,0⟩
  | _ => ⟨0,0,0,0,0,0,t,0,0,0,0,0⟩

/-- A staged outer branch: ALL ordered roles and translations of one sorted
dimension set. The other five coordinates are filled by the sink classifier. -/
def outerBoxRolesAt (sorted : List ℕ) : List GaugeCoordinates :=
  sorted.permutations.flatMap fun ds =>
    (List.range (109 - ds.sum)).map (boxRolePrototype ds)

/-- Complete outer domain, kept staged for context-specific kernel checks. -/
def outerBoxRoles : List GaugeCoordinates :=
  (dissociatedDimensions 6 1 108).flatMap outerBoxRolesAt

/-- Every positive dissociated six-box with translated span at most 108 is
covered. No interval-completion or cap-feasibility claim is made. -/
theorem outerBoxRoles_complete (ds : List ℕ) (t : ℕ) (hn : ds.length = 6)
    (hnd : (subsetSums ds).Nodup) (hp : ∀ d ∈ ds, 0 < d)
    (hb : t + ds.sum ≤ 108) :
    ds.mergeSort (· ≤ ·) ∈ dissociatedDimensions 6 1 108 ∧
      boxRolePrototype ds t ∈ outerBoxRolesAt (ds.mergeSort (· ≤ ·)) ∧
      boxRolePrototype ds t ∈ outerBoxRoles := by
  obtain ⟨hsorted, hroles⟩ := sorted_dimensions_complete ds hn hnd hp (by omega)
  have ht : t ∈ List.range (109 - ds.sum) := List.mem_range.mpr (by omega)
  have hm : boxRolePrototype ds t ∈ outerBoxRolesAt (ds.mergeSort (· ≤ ·)) :=
    List.mem_flatMap.mpr ⟨ds, hroles, List.mem_map.mpr ⟨t, ht, rfl⟩⟩
  exact ⟨hsorted, hm, List.mem_flatMap.mpr ⟨_, hsorted, hm⟩⟩

/-- Conversely, every generated role input has exactly the stated box
conditions. Thus outer coverage adds no malformed dimensions or translations. -/
theorem outerBoxRoles_sound (box : GaugeCoordinates) (h : box ∈ outerBoxRoles) :
    ∃ ds : List ℕ, ∃ t : ℕ, ds.length = 6 ∧ (subsetSums ds).Nodup ∧
      (∀ d ∈ ds, 0 < d) ∧ t + ds.sum ≤ 108 ∧ box = boxRolePrototype ds t := by
  obtain ⟨sorted, hs, hr⟩ := List.mem_flatMap.mp h
  obtain ⟨ds, hd, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hn, _, hp, hb, hnd⟩ := (mem_dissociatedDimensions _ _ _ _).mp hs
  have hperm := List.mem_permutations.mp hd
  refine ⟨ds, t, hperm.length_eq.trans hn, ?_, ?_, ?_, rfl⟩
  · rw [subsetSums_perm hperm]
    exact hnd
  · intro d hd
    exact hp d (hperm.mem_iff.mp hd)
  · have := List.mem_range.mp ht
    rw [hperm.sum_eq] at this ⊢
    omega

private theorem pairGap_int (x y : ℕ) :
    ((pairGap (x,y) : ℕ) : ℤ) = |(x : ℤ) - y| := by
  rcases le_total x y with h | h
  · simp [pairGap, max_eq_right h, min_eq_left h,
      abs_of_nonpos (show (x : ℤ) - y ≤ 0 by omega)]
    omega
  · simp [pairGap, max_eq_left h, min_eq_right h,
      abs_of_nonneg (show 0 ≤ (x : ℤ) - y by omega)]
    omega

/-- Match the natural box data already proved for the original labelling
to the seven signed minimum coordinates; the other five stay arbitrary. -/
theorem minimumCoordinates_same_outer_box (a b : ℕ → ℕ) :
    SameSinkBox (minimumCoordinates (fun i => a i) (fun i => b i))
      (boxRolePrototype ((boxPairs a b).map pairGap) (pairOffset (boxPairs a b))) := by
  simp [SameSinkBox, minimumCoordinates, boxRolePrototype, boxPairs, pairOffset,
    pairGap_int, Nat.cast_add, Nat.cast_min]
  omega

/-- The translated box span is the same in the natural and signed readouts. -/
theorem minimumCoordinates_box_span (a b : ℕ → ℕ) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    c.t + c.u + c.v + c.w + c.d1 + c.d2 + c.d3 =
      ((pairOffset (boxPairs a b) + ((boxPairs a b).map pairGap).sum : ℕ) : ℤ) := by
  simp [minimumCoordinates, pairOffset, boxPairs, pairGap_int, Nat.cast_add, Nat.cast_min]
  omega

/-- Every original budget-108 labelling reaches a certified outer branch,
then its ACTUAL sink positions and the full prescribed nineteen-weight shape.
This closes logical outer-input coverage, not evaluation of those branches. -/
theorem outer_sink_coverage_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    ∃ sorted ∈ dissociatedDimensions 6 1 108,
      ∃ box ∈ outerBoxRolesAt sorted, SameSinkBox c box ∧
        (c.A1 + c.p, c.A2 + c.p, c.A3 + c.p) ∈ sinkPositionChoices box ∧
        c.A3 ∈ sinkIntervalAnchors box (c.A1 + c.p) (c.A2 + c.p) (c.A3 + c.p) := by
  dsimp only
  obtain ⟨hn, hnd, _, hp, hb⟩ :=
    box_constraints_of_budget B a b cap h1 hsteps hcap h109 hbudget
  obtain ⟨hs, hr, _⟩ := outerBoxRoles_complete _ _ hn hnd hp hb
  have hm := minimumCoordinates_same_outer_box a b
  exact ⟨_, hs, _, hr, hm, sink_outer_positions_complete _ _ hm
    (halving_of_budget B a b cap h1 hsteps hcap h109 hbudget).2.1
    (normalized_interval_of_budget B a b cap h1 hsteps hcap h109 hbudget)⟩

/-- Apply only the already kernel-checked 278-pair restriction. The stronger
246-pair computational domain is not assumed in this enumeration. -/
def outerPairRolesAt (sorted : List ℕ) : List GaugeCoordinates :=
  (outerBoxRolesAt sorted).filter (fun box => (box.u, box.d1) ∈ alternatingStepPairs)

/-- Outer coverage survives the checked pair domain and BOTH odd-run bounds,
and still reaches the actual positions and prescribed nineteen-weight half.
Critical families, orientations and signed caps are subsequent obligations. -/
theorem pruned_outer_sink_coverage_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    ∃ sorted ∈ dissociatedDimensions 6 1 108,
      ∃ box ∈ outerPairRolesAt sorted, SameSinkBox c box ∧
        oddRunCount box.d1 ((Multiset.range 109).map Int.ofNat - coordinateBox box) ≤ 7 ∧
        oddRunCount box.u ((Multiset.range 109).map Int.ofNat - coordinateBox box) ≤ 7 ∧
        (c.A1 + c.p, c.A2 + c.p, c.A3 + c.p) ∈ sinkPositionChoices box ∧
        c.A3 ∈ sinkIntervalAnchors box (c.A1 + c.p) (c.A2 + c.p) (c.A3 + c.p) := by
  dsimp only
  obtain ⟨sorted, hs, box, hb, hm, hpos, ha⟩ :=
    outer_sink_coverage_of_budget B a b cap h1 hsteps hcap h109 hbudget
  have hp := alternating_pairs_of_budget B a b cap h1 hsteps hcap h109 hbudget
  have ho := odd_runs_of_budget B a b cap h1 hsteps hcap h109 hbudget
  dsimp only at hp ho
  have hbox : coordinateBox (minimumCoordinates (fun i => a i) (fun i => b i)) =
      coordinateBox box := by
    obtain ⟨hu, hv, hw, hd1, hd2, hd3, ht⟩ := hm
    simp only [coordinateBox, hu, hv, hw, hd1, hd2, hd3, ht]
  rw [hm.1, hm.2.2.2.1] at hp
  have hb' : box ∈ outerPairRolesAt sorted :=
    List.mem_filter.mpr ⟨hb, by simpa only [decide_eq_true_eq] using hp⟩
  refine ⟨sorted, hs, box, hb', hm, ?_, ?_, hpos, ha⟩
  · simpa only [hbox, hm.2.2.2.1] using ho.2.2.2.1
  · simpa only [hbox, hm.1] using ho.2.2.2.2.1

/-- Carry the twelve critical families to ANY covered outer box. The branch
through 8 is top-pinned; the other branch retains 5,7,15. Cap saturation and
zero caps away from the critical path remain explicit. -/
theorem outer_critical_branch_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108)
    (box : GaugeCoordinates)
    (hm : SameSinkBox (minimumCoordinates (fun i => a i) (fun i => b i)) box) :
    ∃ es, Path a b stepsRev 109 es ∧ es.map Prod.fst ∈ prunedCriticalFamilies ∧
      (es.map Prod.snd).sum = 108 ∧ (∀ e ∈ es, e.2 = cap e.1) ∧
      (∀ u ∈ source, u < 109 → u ∉ es.map Prod.fst → cap u = 0) ∧
      (8 ∈ es.map Prod.fst →
        box.t + box.u + box.v + box.w + box.d1 + box.d2 + box.d3 = 108) ∧
      (8 ∉ es.map Prod.fst → 5 ∈ es.map Prod.fst ∧
        7 ∈ es.map Prod.fst ∧ 15 ∈ es.map Prod.fst) := by
  obtain ⟨es, hp, hf, hw, hs, hz, ht, hm8⟩ :=
    critical_twelve_of_budget B a b cap h1 hsteps hcap h109 hbudget
  refine ⟨es, hp, hf, hw, hs, hz, ?_, hm8⟩
  intro h8
  have hspan := minimumCoordinates_box_span a b
  dsimp only at hspan
  rw [hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1,
    hm.2.2.2.2.2.1, hm.2.2.2.2.2.2] at hspan
  rw [hspan, ht h8]
  rfl

end ScholzBrauer.Clift109
