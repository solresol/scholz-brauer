import ScholzBrauer.Clift109SparseResidues

/-! A kernel-evaluated necessary domain for the sparse residue fingerprints.
The mask is proved to preserve multiplicity parity before finite evaluation. -/

namespace ScholzBrauer.Clift109

private theorem xor_left_comm (a b c : ℕ) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  ac_rfl

private theorem xor_cancel (a b : ℕ) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

def parityMask : List ℤ → ℕ
  | [] => 0
  | x :: xs => 2 ^ x.toNat ^^^ parityMask xs

theorem testBit_parityMask (xs : List ℤ) (h : ∀ x ∈ xs, 0 ≤ x) (q : ℕ) :
    (parityMask xs).testBit q = decide (((xs : Multiset ℤ).count (q : ℤ)) % 2 = 1) := by
  induction xs with
  | nil => simp [parityMask]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hi := ih (fun x hx => h x (by simp [hx]))
    change (2 ^ x.toNat ^^^ parityMask xs).testBit q =
      decide (((x ::ₘ (xs : Multiset ℤ)).count (q : ℤ)) % 2 = 1)
    simp only [Nat.testBit_xor, Nat.testBit_two_pow, hi,
      Multiset.count_cons]
    by_cases hq : (q : ℤ) = x
    · have hxq : x.toNat = q := by omega
      simp only [hxq, decide_true, Bool.true_xor, hq, ↓reduceIte]
      have toggle (n : ℕ) : (!decide (n % 2 = 1)) = decide ((n + 1) % 2 = 1) := by
        have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases hn with hn | hn <;> simp [Nat.add_mod, hn]
      simpa only [hq] using toggle ((xs : Multiset ℤ).count (q : ℤ))
    · have hxq : x.toNat ≠ q := by omega
      simp [hq, hxq]

theorem parityMask_eq_of_oddLabels (xs ys : List ℤ)
    (hx : ∀ x ∈ xs, 0 ≤ x) (hy : ∀ y ∈ ys, 0 ≤ y)
    (h : oddLabels (xs : Multiset ℤ) = oddLabels (ys : Multiset ℤ)) :
    parityMask xs = parityMask ys := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_parityMask _ hx, testBit_parityMask _ hy]
  congr 1
  have mem_odd (s : Multiset ℤ) :
      (q : ℤ) ∈ oddLabels s ↔ s.count (q : ℤ) % 2 = 1 := by
    simp only [oddLabels, Finset.mem_filter, Multiset.mem_toFinset]
    exact ⟨And.right, fun hc => ⟨Multiset.count_pos.mp (by omega), hc⟩⟩
  exact propext (by rw [← mem_odd, ← mem_odd, h])

def intervalParityMask (m : ℤ) : ℕ :=
  parityMask ((List.range 109).map (fun i : ℕ => (i : ℤ) % m))

def residueEdgeMask (m d x : ℤ) : ℕ :=
  2 ^ x.toNat ^^^ 2 ^ ((x + d) % m).toNat

/-- The sparse predicate forces equality of a two-edge syndrome and a
single-edge-plus-singleton syndrome. -/
theorem threePairCompatible_mask (m d : ℤ) (hm : 0 < m)
    (h : threePairCompatible m d) :
    ∃ x y z s : ℤ, (0 ≤ x ∧ x < m) ∧ (0 ≤ y ∧ y < m) ∧
      (0 ≤ z ∧ z < m) ∧ (0 ≤ s ∧ s < m) ∧
      residueEdgeMask m d x ^^^ residueEdgeMask m d y =
        intervalParityMask m ^^^ residueEdgeMask m d z ^^^ 2 ^ s.toNat := by
  obtain ⟨x, y, z, s, hx, hy, hz, hs, hf⟩ := h
  let xs := (List.range 109).map (fun i : ℕ => (i : ℤ) % m)
  let ys := [(x + d) % m, (y + d) % m, x % m, y % m, z % m, (z + d) % m, s % m]
  have hxs : ∀ a ∈ xs, 0 ≤ a := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact Int.emod_nonneg _ (ne_of_gt hm)
  have hys : ∀ a ∈ ys, 0 ≤ a := by
    intro a ha
    simp only [ys, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Int.emod_nonneg _ (ne_of_gt hm)
  have he : oddLabels (xs : Multiset ℤ) = oddLabels (ys : Multiset ℤ) := by
    simpa [xs, ys, intervalOddResidues, threePairWeights, zbranch, zshift,
      Multiset.range, Multiset.map_add, Multiset.map_cons] using hf
  have heq := parityMask_eq_of_oddLabels xs ys hxs hys he
  have hxmod := Int.emod_eq_of_lt hx.1 hx.2
  have hymod := Int.emod_eq_of_lt hy.1 hy.2
  have hzmod := Int.emod_eq_of_lt hz.1 hz.2
  have hsmod := Int.emod_eq_of_lt hs.1 hs.2
  have heq' : intervalParityMask m = residueEdgeMask m d x ^^^
      residueEdgeMask m d y ^^^ residueEdgeMask m d z ^^^ 2 ^ s.toNat := by
    simpa [intervalParityMask, xs, ys, parityMask, residueEdgeMask,
      hxmod, hymod, hzmod, hsmod, Nat.xor_assoc, Nat.xor_comm, xor_left_comm] using heq
  refine ⟨x, y, z, s, hx, hy, hz, hs, ?_⟩
  rw [heq']
  simp [Nat.xor_assoc, Nat.xor_comm, xor_left_comm, xor_cancel]

/-- A bounded structural scan avoids reducing the logarithm inside the kernel. -/
def topBit : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => if n.testBit k then k else topBit k n

@[simp] theorem topBit_zero (k : ℕ) : topBit k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [topBit] using ih

theorem topBit_testBit (k n : ℕ) (hn : n ≠ 0) (hbound : n < 2 ^ k) :
    n.testBit (topBit k n) = true := by
  induction k with
  | zero => simp at hbound; omega
  | succ k ih =>
    simp only [topBit]
    split
    · assumption
    · rename_i ht
      have hd : n / 2 ^ k < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr
        (by simpa [Nat.pow_succ, Nat.mul_comm] using hbound)
      have hbit : ¬n / 2 ^ k % 2 = 1 := by
        simpa [Nat.testBit_eq_decide_div_mod_eq] using ht
      rw [Nat.mod_eq_of_lt hd] at hbit
      have small (v : ℕ) (hv : v < 2) : v = 0 ∨ v = 1 := by omega
      exact ih (Nat.lt_of_div_eq_zero (Nat.two_pow_pos k) ((small _ hd).resolve_right hbit))

theorem residueEdgeMask_lt (m d x : ℤ) (hm : 0 < m)
    (hx : 0 ≤ x ∧ x < m) : residueEdgeMask m d x < 2 ^ m.toNat := by
  have hz0 := Int.emod_nonneg (x + d) (ne_of_gt hm)
  have hzlt := Int.emod_lt_of_pos (x + d) hm
  exact Nat.xor_lt_two_pow
    (Nat.pow_lt_pow_right (by decide) (by omega))
    (Nat.pow_lt_pow_right (by decide) (by omega))

/-- An edge with a set bit at q must start at q or at q-d modulo m. -/
theorem residueEdgeMask_at_bit (m d x : ℤ) (hm : 0 < m)
    (hx : 0 ≤ x ∧ x < m) (q : ℕ)
    (ht : (residueEdgeMask m d x).testBit q = true) :
    residueEdgeMask m d x = residueEdgeMask m d q ∨
      residueEdgeMask m d x = residueEdgeMask m d (((q : ℤ) - d) % m) := by
  have hq : x.toNat = q ∨ ((x + d) % m).toNat = q := by
    by_contra! hh
    simp [residueEdgeMask, Nat.testBit_xor, hh.1, hh.2] at ht
  rcases hq with hq | hq
  · left
    congr 1
    omega
  · right
    have hmod := Int.emod_nonneg (x + d) (ne_of_gt hm)
    have hq' : (q : ℤ) = (x + d) % m := by omega
    have hstart : ((q : ℤ) - d) % m = x := by
      rw [hq', Int.emod_sub_emod]
      simpa using Int.emod_eq_of_lt hx.1 hx.2
    rw [hstart]

/-- Constant-size recognition of the only two possible edges at the top bit.
Its completeness suffices for the exclusion; no unproved lookup data are used. -/
def edgeLookup (m d : ℤ) (n : ℕ) : Bool :=
  let q := topBit m.toNat n
  n == residueEdgeMask m d q || n == residueEdgeMask m d (((q : ℤ) - d) % m)

theorem edgeLookup_of_edge (m d x : ℤ) (hm : 0 < m)
    (hx : 0 ≤ x ∧ x < m) : edgeLookup m d (residueEdgeMask m d x) = true := by
  by_cases hz : residueEdgeMask m d x = 0
  · have hp : 2 ^ x.toNat = 2 ^ ((x + d) % m).toNat := by
      have he := congrArg (fun n : ℕ => 2 ^ x.toNat ^^^ n) hz
      simpa [residueEdgeMask, xor_cancel] using he.symm
    have ht := congrArg (fun n : ℕ => n.testBit x.toNat) hp
    have he : ((x + d) % m).toNat = x.toNat := by
      simpa [Nat.testBit_two_pow] using ht
    have hm0 := Int.emod_nonneg (x + d) (ne_of_gt hm)
    have he' : (x + d) % m = x := by omega
    have hd : d % m = 0 := by
      have hs := congrArg (fun y : ℤ => (y - x) % m) he'
      simpa using hs
    simp only [edgeLookup]
    rw [hz]
    simp [residueEdgeMask, hd]
  · have ht := topBit_testBit m.toNat _ hz (residueEdgeMask_lt m d x hm hx)
    have he := residueEdgeMask_at_bit m d x hm hx _ ht
    simpa only [edgeLookup, Bool.or_eq_true, beq_iff_eq] using he

/-- Two edges are recognized by removing one of the two possible edges
at any top bit of their nonzero XOR. -/
def pairLookup (m d : ℤ) (n : ℕ) : Bool :=
  if n == 0 then true else
    let q := topBit m.toNat n
    edgeLookup m d (n ^^^ residueEdgeMask m d q) ||
      edgeLookup m d (n ^^^ residueEdgeMask m d (((q : ℤ) - d) % m))

theorem pairLookup_of_edges (m d x y : ℤ) (hm : 0 < m)
    (hx : 0 ≤ x ∧ x < m) (hy : 0 ≤ y ∧ y < m) :
    pairLookup m d (residueEdgeMask m d x ^^^ residueEdgeMask m d y) = true := by
  let a := residueEdgeMask m d x
  let b := residueEdgeMask m d y
  change pairLookup m d (a ^^^ b) = true
  by_cases hz : a ^^^ b = 0
  · simp [pairLookup, a, b, hz]
  · have ht := topBit_testBit m.toNat (a ^^^ b) hz
      (Nat.xor_lt_two_pow (residueEdgeMask_lt m d x hm hx) (residueEdgeMask_lt m d y hm hy))
    have hor : a.testBit (topBit m.toNat (a ^^^ b)) = true ∨ b.testBit (topBit m.toNat (a ^^^ b)) = true := by
      by_contra! hh
      simp [Nat.testBit_xor, hh.1, hh.2] at ht
    have hxa := edgeLookup_of_edge m d x hm hx
    have hyb := edgeLookup_of_edge m d y hm hy
    simp only [pairLookup, beq_iff_eq, if_neg hz, Bool.or_eq_true]
    rcases hor with ht | ht
    · rcases residueEdgeMask_at_bit m d x hm hx _ ht with he | he
      · left
        rw [← he]
        simpa [a, b, Nat.xor_assoc, Nat.xor_comm, xor_left_comm, xor_cancel] using hyb
      · right
        rw [← he]
        simpa [a, b, Nat.xor_assoc, Nat.xor_comm, xor_left_comm, xor_cancel] using hyb
    · rcases residueEdgeMask_at_bit m d y hm hy _ ht with he | he
      · left
        rw [← he]
        simpa [a, b, Nat.xor_assoc, Nat.xor_comm, xor_left_comm, xor_cancel] using hxa
      · right
        rw [← he]
        simpa [a, b, Nat.xor_assoc, Nat.xor_comm, xor_left_comm, xor_cancel] using hxa

def targetMasks (m d : ℤ) : List ℕ :=
  let f := intervalParityMask m
  (List.range m.toNat).flatMap (fun z : ℕ =>
    (List.range m.toNat).map (fun s : ℕ => f ^^^ residueEdgeMask m d z ^^^ 2 ^ s))

/-- Only m squared targets are tested; the other two edges are recognized
using the proved top-bit restriction. -/
def sparseExcluded (m d : ℤ) : Bool :=
  (targetMasks m d).all (fun n => !pairLookup m d n)

theorem sparseExcluded_sound (m d : ℤ) (hm : 0 < m)
    (h : sparseExcluded m d = true) : ¬ threePairCompatible m d := by
  intro hc
  obtain ⟨x, y, z, s, hx, hy, hz, hs, he⟩ := threePairCompatible_mask m d hm hc
  have ht : intervalParityMask m ^^^ residueEdgeMask m d z ^^^ 2 ^ s.toNat ∈
      targetMasks m d := by
    apply List.mem_flatMap.mpr
    refine ⟨z.toNat, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨s.toNat, List.mem_range.mpr (by omega), by rw [Int.toNat_of_nonneg hz.1]⟩
  have hn := List.all_eq_true.mp h _ ht
  have hp := pairLookup_of_edges m d x y hm hx hy
  rw [← he, hp] at hn
  contradiction


end ScholzBrauer.Clift109
