import ScholzBrauer.CliftLabelling

/-! The 64 paths through vertex 8 in Clift's selected 109 graph form a
translated six-dimensional subset-sum multiset. Multiplicities are retained:
distinctness is a consequence of the terminal Mersenne equation, not assumed.
The remaining finite classification and gauge reduction are separate obligations. -/

namespace ScholzBrauer.CliftLabelling

/-- Translate every weight, retaining multiplicities. -/
def shift (s : Multiset ℕ) (c : ℕ) : Multiset ℕ := s.map (· + c)

/-- Choose either of two route weights. -/
def branch (s : Multiset ℕ) (x y : ℕ) : Multiset ℕ := shift s x + shift s y

theorem shift_shift (s : Multiset ℕ) (x y : ℕ) :
    shift (shift s x) y = shift s (x + y) := by
  simp [shift, Multiset.map_map, Nat.add_assoc]

theorem shift_add (s t : Multiset ℕ) (x : ℕ) :
    shift (s + t) x = shift s x + shift t x := by simp [shift]

theorem branch_add (s t : Multiset ℕ) (x y : ℕ) :
    branch (s + t) x y = branch s x y + branch t x y := by
  simp only [branch, shift_add]
  ac_rfl

/-- All choices of one entry from each pair. -/
def choices : List (ℕ × ℕ) → Multiset ℕ
  | [] => {0}
  | p :: ps => branch (choices ps) p.1 p.2

/-- All subset sums, with one occurrence per subset of positions. -/
def subsetSums : List ℕ → Multiset ℕ
  | [] => {0}
  | d :: ds => subsetSums ds + shift (subsetSums ds) d

def pairGap (p : ℕ × ℕ) : ℕ := max p.1 p.2 - min p.1 p.2

def pairOffset (ps : List (ℕ × ℕ)) : ℕ := (ps.map (fun p => min p.1 p.2)).sum

theorem branch_normalize (s : Multiset ℕ) (x y : ℕ) :
    branch s x y = shift (s + shift s (max x y - min x y)) (min x y) := by
  rw [shift_add, shift_shift]
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h, Nat.sub_add_cancel h]
    rfl
  · rw [min_eq_right h, max_eq_left h, Nat.sub_add_cancel h]
    exact add_comm _ _

/-- Every product of binary choices is a translated subset-sum multiset. -/
theorem choices_normalize (ps : List (ℕ × ℕ)) :
    choices ps = shift (subsetSums (ps.map pairGap)) (pairOffset ps) := by
  induction ps with
  | nil => simp [choices, subsetSums, pairOffset, shift]
  | cons p ps ih =>
    rw [choices, branch_normalize, ih]
    simp only [List.map_cons, subsetSums, pairGap, pairOffset, List.sum_cons]
    simp only [shift_add, shift_shift]
    congr 1 <;> congr 1 <;> omega

theorem card_subsetSums (ds : List ℕ) : (subsetSums ds).card = 2 ^ ds.length := by
  induction ds with
  | nil => simp [subsetSums]
  | cons d ds ih => simp [subsetSums, shift, ih, pow_succ, Nat.mul_two]

theorem zero_mem_subsetSums (ds : List ℕ) : 0 ∈ subsetSums ds := by
  induction ds with
  | nil => simp [subsetSums]
  | cons d ds ih => exact Multiset.mem_add.mpr (Or.inl ih)

theorem sum_mem_subsetSums (ds : List ℕ) : ds.sum ∈ subsetSums ds := by
  induction ds with
  | nil => simp [subsetSums]
  | cons d ds ih =>
    apply Multiset.mem_add.mpr
    right
    exact Multiset.mem_map.mpr ⟨ds.sum, ih, Nat.add_comm _ _⟩

/-- Distinct subset sums force every listed difference to be positive. -/
theorem positive_of_subsetSums_nodup (ds : List ℕ) (h : (subsetSums ds).Nodup) :
    ∀ d ∈ ds, 0 < d := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have ht : (subsetSums ds).Nodup :=
      Multiset.nodup_of_le (Multiset.le_add_right _ _) h
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · by_contra hn
      have hd : e = 0 := by omega
      have hz := zero_mem_subsetSums ds
      simp only [subsetSums, hd, shift, Nat.add_zero] at h
      exact Multiset.disjoint_left.mp (Multiset.nodup_add.mp h).2.2 hz
        (Multiset.mem_map.mpr ⟨0, hz, rfl⟩)
    · exact ih ht e he

theorem mem_subsetSums_of_mem {d : ℕ} {ds : List ℕ} (h : d ∈ ds) :
    d ∈ subsetSums ds := by
  induction ds with
  | nil => simp at h
  | cons e ds ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Multiset.mem_add.mpr (Or.inr
        (Multiset.mem_map.mpr ⟨0, zero_mem_subsetSums ds, Nat.zero_add _⟩))
    · exact Multiset.mem_add.mpr (Or.inl (ih h))

/-- In particular, the differences themselves are pairwise distinct. -/
theorem nodup_of_subsetSums_nodup (ds : List ℕ) (h : (subsetSums ds).Nodup) :
    ds.Nodup := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    obtain ⟨ht, -, hd⟩ := Multiset.nodup_add.mp h
    refine List.nodup_cons.mpr ⟨?_, ih ht⟩
    intro hmem
    exact Multiset.disjoint_left.mp hd (mem_subsetSums_of_mem hmem)
      (Multiset.mem_map.mpr ⟨0, zero_mem_subsetSums ds, Nat.zero_add _⟩)

end ScholzBrauer.CliftLabelling

namespace ScholzBrauer.Clift109

open ScholzBrauer.CliftLabelling

/-- The three parallel pairs below 8 and the three binary routes above 8,
listed from the sink back toward the seed. -/
def boxPairs (a b : ℕ → ℕ) : List (ℕ × ℕ) :=
  [(a 58 + a 109, b 109), (a 28 + a 51, b 51), (a 15 + a 23, b 23),
   (a 8, b 8), (a 4, b 4), (a 2, b 2)]

def box (a b : ℕ → ℕ) : Multiset ℕ := choices (boxPairs a b)

/-- The 45 paths that avoid vertex 8, grouped by their last exit toward the sink. -/
def boxRemainder (a b : ℕ → ℕ) : Multiset ℕ :=
  branch (branch (shift (weights a b stepsRev 7) (b 15 + a 23))
    (a 28 + a 51) (b 51)) (a 58 + a 109) (b 109) +
  branch (shift (weights a b stepsRev 5) (b 28 + a 51))
    (a 58 + a 109) (b 109) +
  shift (weights a b stepsRev 7) (b 58 + a 109)

private theorem weights8 (a b : ℕ → ℕ) :
    weights a b stepsRev 8 = choices [(a 8, b 8), (a 4, b 4), (a 2, b 2)] := by
  rfl

private theorem weights23 (a b : ℕ → ℕ) :
    weights a b stepsRev 23 =
      branch (weights a b stepsRev 8) (a 15 + a 23) (b 23) +
      shift (weights a b stepsRev 7) (b 15 + a 23) := by
  change shift (shift (weights a b stepsRev 8) (a 15) +
    shift (weights a b stepsRev 7) (b 15)) (a 23) +
    shift (weights a b stepsRev 8) (b 23) = _
  simp only [shift_add, shift_shift, branch]
  ac_rfl

private theorem weights51 (a b : ℕ → ℕ) :
    weights a b stepsRev 51 =
      branch (weights a b stepsRev 23) (a 28 + a 51) (b 51) +
      shift (weights a b stepsRev 5) (b 28 + a 51) := by
  change shift (shift (weights a b stepsRev 23) (a 28) +
    shift (weights a b stepsRev 5) (b 28)) (a 51) +
    shift (weights a b stepsRev 23) (b 51) = _
  simp only [shift_add, shift_shift, branch]
  ac_rfl

private theorem weights109 (a b : ℕ → ℕ) :
    weights a b stepsRev 109 =
      branch (weights a b stepsRev 51) (a 58 + a 109) (b 109) +
      shift (weights a b stepsRev 7) (b 58 + a 109) := by
  change shift (shift (weights a b stepsRev 51) (a 58) +
    shift (weights a b stepsRev 7) (b 58)) (a 109) +
    shift (weights a b stepsRev 51) (b 109) = _
  simp only [shift_add, shift_shift, branch]
  ac_rfl

/-- Exact multiset partition into the 64 paths through 8 and the 45 avoiding it. -/
theorem weights_box_partition (a b : ℕ → ℕ) :
    weights a b stepsRev 109 = box a b + boxRemainder a b := by
  rw [weights109, weights51, weights23]
  simp only [branch_add, weights8, box, boxPairs, choices, boxRemainder]
  ac_rfl

theorem box_normalize (a b : ℕ → ℕ) :
    box a b = shift (subsetSums ((boxPairs a b).map pairGap))
      (pairOffset (boxPairs a b)) := choices_normalize _

theorem card_box (a b : ℕ → ℕ) : (box a b).card = 64 := by
  rw [box_normalize]
  simp [shift, card_subsetSums, boxPairs]

theorem card_boxRemainder (a b : ℕ → ℕ) : (boxRemainder a b).card = 45 := by
  have h := card_weights a b stepsRev stepsRev_valid 109 (by rw [vals_stepsRev]; decide)
  rw [weights_box_partition, Multiset.card_add, card_box] at h
  omega

/-- Mersenne termination forces all 64 subset sums to be distinct, even
without a cost hypothesis or a restriction on intermediate bases. -/
theorem box_dissociated (B a b : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (h109 : B 109 = 2 ^ 109 - 1) :
    (subsetSums ((boxPairs a b).map pairGap)).Nodup := by
  have h := weights_nodup a b B stepsRev stepsRev_valid h1
    (fun s hs => hsteps s (List.mem_reverse.mp hs))
    (by rw [vals_stepsRev]; decide) h109
  rw [weights_box_partition] at h
  have hb := (Multiset.nodup_add.mp h).1
  rw [box_normalize] at hb
  exact Multiset.Nodup.of_map _ hb

/-- The complete necessary box conditions used in the interval enumeration:
six positive differences, 64 distinct subset sums, and translated maximum
at most 108. This does not assume the finite classification. -/
theorem box_constraints_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let ds := (boxPairs a b).map pairGap
    ds.length = 6 ∧ (subsetSums ds).Nodup ∧ ds.Nodup ∧ (∀ d ∈ ds, 0 < d) ∧
      pairOffset (boxPairs a b) + ds.sum ≤ 108 := by
  dsimp only
  have hnd := box_dissociated B a b h1 hsteps h109
  refine ⟨by simp [boxPairs], hnd, nodup_of_subsetSums_nodup _ hnd,
    positive_of_subsetSums_nodup _ hnd, ?_⟩
  have hmem : ((boxPairs a b).map pairGap).sum + pairOffset (boxPairs a b) ∈
      box a b := by
    rw [box_normalize]
    exact Multiset.mem_map.mpr ⟨_, sum_mem_subsetSums _, rfl⟩
  have hw := (Multiset.subset_add_left hmem :
    _ ∈ box a b + boxRemainder a b)
  rw [← weights_box_partition,
    weights_range_of_budget B a b cap h1 hsteps hcap h109 hbudget,
    Multiset.mem_range] at hw
  omega

end ScholzBrauer.Clift109
