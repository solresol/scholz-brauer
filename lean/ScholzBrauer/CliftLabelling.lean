import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Multiset.Range
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import ScholzBrauer.Clift109
import ScholzBrauer.NonHansen29

/-! # Path weights of Clift edge labellings

A source chain is given by its steps `(p, q)`, *latest first*; each step adds
the vertex `p + q` with parents `p` and `q`. A labelling gives the two parent
edges of vertex `v` the shifts `a v` and `b v`; with seed `B 1 = 1`, every base
`B v` is the sum of `2 ^ w` over the weights `w` of all paths from 1 to `v`.

Binary weight then forces the `n` path weights of `B n = 2^n - 1` to be
distinct, and each path weight is at most the sum of the outgoing caps of the
earlier vertices. Hence every labelling of every chain for `n` has cap sum at
least `n - 1`, and cap sum `n - 1` forces the weights to be exactly
`0, ..., n - 1`. These general facts are instantiated for Clift's selected 109
graph; the classification of its interval labellings remains computational
(`results/2026-10-18-clift109-box-exclusion.md`). -/

namespace ScholzBrauer.CliftLabelling

open Nat

/-! ## Binary weight -/

/-- The number of one bits of `n`. -/
def bw (n : ℕ) : ℕ := (Nat.digits 2 n).sum

theorem padicValNat_factorial_add_bw (n : ℕ) : padicValNat 2 n ! + bw n = n := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  have hle := Nat.digit_sum_le 2 n
  unfold bw
  norm_num at h
  omega

/-- Binary weight is subadditive (Legendre's formula and `m! n! ∣ (m+n)!`). -/
theorem bw_add_le (m n : ℕ) : bw (m + n) ≤ bw m + bw n := by
  have hm := padicValNat_factorial_add_bw m
  have hn := padicValNat_factorial_add_bw n
  have hmn := padicValNat_factorial_add_bw (m + n)
  have hd : 2 ^ padicValNat 2 (m ! * n !) ∣ (m + n)! :=
    pow_padicValNat_dvd.trans (Nat.factorial_mul_factorial_dvd_factorial_add m n)
  have hv := (padicValNat_dvd_iff_le (p := 2) (Nat.factorial_ne_zero _)).mp hd
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at hv
  omega

theorem bw_double (m : ℕ) : bw (2 * m) = bw m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · unfold bw
    rw [Nat.digits_def' (by decide) (by omega)]
    simp [Nat.mul_mod_right, Nat.mul_div_cancel_left m (by decide : 0 < 2)]

theorem bw_double_add_one (m : ℕ) : bw (2 * m + 1) = bw m + 1 := by
  unfold bw
  rw [Nat.digits_def' (by decide) (by omega)]
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2, List.sum_cons]
  omega

theorem bw_two_pow (k : ℕ) : bw (2 ^ k) = 1 := by
  induction k with
  | zero => simp [bw]
  | succ k ih => rw [pow_succ, mul_comm, bw_double, ih]

theorem bw_mersenne (n : ℕ) : bw (2 ^ n - 1) = n := by
  induction n with
  | zero => simp [bw]
  | succ n ih =>
    have hpos := Nat.one_le_two_pow (n := n)
    have : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by rw [pow_succ]; omega
    rw [this, bw_double_add_one, ih]

/-- A sum of `card s` powers of two has at most `card s` one bits. -/
theorem bw_sum_le (s : Multiset ℕ) : bw ((s.map (2 ^ ·)).sum) ≤ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp [bw]
  | cons x s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have := bw_add_le (2 ^ x) ((s.map (2 ^ ·)).sum)
    rw [bw_two_pow] at this
    omega

/-- If the binary weight of a sum of powers of two equals the number of terms,
the exponents are distinct. -/
theorem nodup_of_bw_eq (s : Multiset ℕ)
    (h : bw ((s.map (2 ^ ·)).sum) = Multiset.card s) : s.Nodup := by
  classical
  by_contra hnd
  rw [Multiset.nodup_iff_count_le_one] at hnd
  push_neg at hnd
  obtain ⟨x, hx⟩ := hnd
  have hx1 : x ∈ s := Multiset.count_pos.mp (by omega)
  have hx2 : x ∈ s.erase x := by
    rw [← Multiset.count_pos, Multiset.count_erase_self]
    omega
  set t := (s.erase x).erase x
  have hs : s = x ::ₘ x ::ₘ t := by
    rw [Multiset.cons_erase hx2, Multiset.cons_erase hx1]
  have hsum : (s.map (2 ^ ·)).sum = 2 ^ (x + 1) + (t.map (2 ^ ·)).sum := by
    rw [hs]
    simp only [Multiset.map_cons, Multiset.sum_cons, pow_succ]
    ring
  have hcard : Multiset.card s = Multiset.card t + 2 := by
    rw [hs]; simp
  have hle := bw_add_le (2 ^ (x + 1)) ((t.map (2 ^ ·)).sum)
  rw [bw_two_pow] at hle
  have := bw_sum_le t
  rw [hsum] at h
  omega

/-- `n` distinct naturals below `n` are exactly `0, ..., n - 1`. -/
theorem eq_range_of_nodup (s : Multiset ℕ) (n : ℕ) (hnd : s.Nodup)
    (hcard : Multiset.card s = n) (hlt : ∀ x ∈ s, x < n) : s = Multiset.range n := by
  classical
  have hsub : s.toFinset ⊆ Finset.range n := by
    intro x hx
    simpa using hlt x (Multiset.mem_toFinset.mp hx)
  have hc : s.toFinset.card = (Finset.range n).card := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard, Finset.card_range]
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [← Multiset.dedup_eq_self.mpr hnd, ← Multiset.toFinset_val, heq, Finset.range_val]

/-- `n >= 1` distinct naturals contain one at least `n - 1`. -/
theorem exists_ge_of_nodup (s : Multiset ℕ) (n : ℕ) (hnd : s.Nodup)
    (hcard : Multiset.card s = n) (hn : 0 < n) : ∃ x ∈ s, n - 1 ≤ x := by
  classical
  by_contra hno
  push_neg at hno
  have hsub : s.toFinset ⊆ Finset.range (n - 1) := by
    intro x hx
    simpa using hno x (Multiset.mem_toFinset.mp hx)
  have := Finset.card_le_card hsub
  rw [Multiset.toFinset_card_of_nodup hnd, hcard, Finset.card_range] at this
  omega

/-! ## Labelled chains -/

/-- Chain values, latest first, for steps listed latest first. -/
def vals : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | s :: rest => (s.1 + s.2) :: vals rest

/-- Each step adds two earlier values and exceeds every earlier value. -/
def valid : List (ℕ × ℕ) → Bool
  | [] => true
  | s :: rest => s.1 ∈ vals rest && s.2 ∈ vals rest &&
      (vals rest).all (· < s.1 + s.2) && valid rest

/-- `weights a b L v` is the multiset of shift sums of all paths from 1 to `v`;
the parent edges `p` and `q` of `v = p + q` carry the shifts `a v` and `b v`. -/
def weights (a b : ℕ → ℕ) : List (ℕ × ℕ) → ℕ → Multiset ℕ
  | [], v => if v = 1 then {0} else 0
  | s :: rest, v =>
      if v = s.1 + s.2 then
        (weights a b rest s.1).map (· + a v) + (weights a b rest s.2).map (· + b v)
      else weights a b rest v

/-- The caps of all chain values below `v`. -/
def capBelow (cap : ℕ → ℕ) (L : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (((vals L).filter (· < v)).map cap).sum

theorem valid_cons {s : ℕ × ℕ} {rest : List (ℕ × ℕ)} (h : valid (s :: rest) = true) :
    s.1 ∈ vals rest ∧ s.2 ∈ vals rest ∧ (∀ u ∈ vals rest, u < s.1 + s.2) ∧
      valid rest = true := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem one_le_of_mem_vals : ∀ L : List (ℕ × ℕ), valid L = true → ∀ v ∈ vals L, 1 ≤ v
  | [], _, v, hv => by simp [vals] at hv; omega
  | s :: rest, hL, v, hv => by
    obtain ⟨h1, -, -, hrest⟩ := valid_cons hL
    simp only [vals, List.mem_cons] at hv
    rcases hv with rfl | hv
    · have := one_le_of_mem_vals rest hrest _ h1
      omega
    · exact one_le_of_mem_vals rest hrest v hv

/-- A vertex of value `v` has exactly `v` paths from the seed. -/
theorem card_weights (a b : ℕ → ℕ) :
    ∀ L : List (ℕ × ℕ), valid L = true → ∀ v ∈ vals L,
      Multiset.card (weights a b L v) = v
  | [], _, v, hv => by
    simp only [vals, List.mem_singleton] at hv
    subst hv; simp [weights]
  | s :: rest, hL, v, hv => by
    obtain ⟨h1, h2, hlt, hrest⟩ := valid_cons hL
    simp only [vals, List.mem_cons] at hv
    rcases hv with rfl | hv
    · simp [weights, card_weights a b rest hrest _ h1, card_weights a b rest hrest _ h2]
    · have hne : v ≠ s.1 + s.2 := (hlt v hv).ne
      simp [weights, hne, card_weights a b rest hrest v hv]

/-- With seed 1, each base is the sum of `2 ^ w` over its path weights. -/
theorem base_eq_sum (a b B : ℕ → ℕ) (h1 : B 1 = 1) :
    ∀ L : List (ℕ × ℕ), valid L = true →
      (∀ s ∈ L, B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2)) →
      ∀ v ∈ vals L, B v = ((weights a b L v).map (2 ^ ·)).sum
  | [], _, _, v, hv => by
    simp only [vals, List.mem_singleton] at hv
    subst hv; simp [weights, h1]
  | s :: rest, hL, hs, v, hv => by
    obtain ⟨h1', h2', hlt, hrest⟩ := valid_cons hL
    have hs' : ∀ t ∈ rest, B t.1 * 2 ^ a (t.1 + t.2) + B t.2 * 2 ^ b (t.1 + t.2) =
        B (t.1 + t.2) := fun t ht => hs t (List.mem_cons_of_mem _ ht)
    simp only [vals, List.mem_cons] at hv
    rcases hv with rfl | hv
    · rw [← hs s (List.mem_cons_self ..), base_eq_sum a b B h1 rest hrest hs' _ h1',
        base_eq_sum a b B h1 rest hrest hs' _ h2']
      rw [weights, if_pos rfl]
      simp only [Multiset.map_add, Multiset.map_map, Multiset.sum_add, Function.comp_def,
        pow_add, Multiset.sum_map_mul_right]
    · have hne : v ≠ s.1 + s.2 := (hlt v hv).ne
      simp only [weights, if_neg hne]
      exact base_eq_sum a b B h1 rest hrest hs' v hv

theorem sum_filter_add_le (cap : ℕ → ℕ) (x : ℕ) :
    ∀ l : List ℕ, x ∈ l → ((l.filter (· < x)).map cap).sum + cap x ≤ (l.map cap).sum
  | [], h => by simp at h
  | y :: l, h => by
    have hle : ∀ m : List ℕ, ((m.filter (· < x)).map cap).sum ≤ (m.map cap).sum := by
      intro m
      induction m with
      | nil => simp
      | cons z m ih =>
        by_cases hz : z < x <;> simp [hz] <;> omega
    by_cases hyx : y = x
    · subst hyx
      have := hle l
      simp
      omega
    · have hx : x ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hyx
        · exact h
      have := sum_filter_add_le cap x l hx
      by_cases hy : y < x <;> simp [hy] <;> omega

/-- Every path weight is at most the caps of the earlier vertices. -/
theorem weight_le_capBelow (a b cap : ℕ → ℕ) :
    ∀ L : List (ℕ × ℕ), valid L = true →
      (∀ s ∈ L, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2) →
      ∀ v ∈ vals L, ∀ x ∈ weights a b L v, x ≤ capBelow cap L v
  | [], _, _, v, hv, x, hx => by
    simp only [vals, List.mem_singleton] at hv
    subst hv
    simp [weights] at hx
    omega
  | s :: rest, hL, hc, v, hv, x, hx => by
    obtain ⟨h1, h2, hlt, hrest⟩ := valid_cons hL
    have hc' : ∀ t ∈ rest, a (t.1 + t.2) ≤ cap t.1 ∧ b (t.1 + t.2) ≤ cap t.2 :=
      fun t ht => hc t (List.mem_cons_of_mem _ ht)
    have ih := weight_le_capBelow a b cap rest hrest hc'
    simp only [vals, List.mem_cons] at hv
    rcases hv with rfl | hv
    · -- the newest vertex: every earlier value lies below it
      have hall : (vals rest).filter (· < s.1 + s.2) = vals rest :=
        List.filter_eq_self.mpr (fun u hu => by simpa using hlt u hu)
      have hcap : capBelow cap (s :: rest) (s.1 + s.2) = ((vals rest).map cap).sum := by
        simp [capBelow, vals, hall]
      rw [hcap]
      obtain ⟨ha, hb⟩ := hc s (List.mem_cons_self ..)
      rw [weights, if_pos rfl] at hx
      simp only [Multiset.mem_add, Multiset.mem_map] at hx
      rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · have := ih _ h1 y hy
        have := sum_filter_add_le cap s.1 (vals rest) h1
        unfold capBelow at *
        omega
      · have := ih _ h2 y hy
        have := sum_filter_add_le cap s.2 (vals rest) h2
        unfold capBelow at *
        omega
    · have hne : v ≠ s.1 + s.2 := (hlt v hv).ne
      have hnlt : ¬ s.1 + s.2 < v := by have := hlt v hv; omega
      simp only [weights, if_neg hne] at hx
      have := ih v hv x hx
      simpa [capBelow, vals, List.filter_cons, hnlt] using this

section Bounds

variable (a b B cap : ℕ → ℕ) (L : List (ℕ × ℕ)) (hL : valid L = true) (h1 : B 1 = 1)
  (hsteps : ∀ s ∈ L, B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
  (hcap : ∀ s ∈ L, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
  {n : ℕ} (hn : n ∈ vals L) (hB : B n = 2 ^ n - 1)
include hL h1 hsteps hn hB

/-- The `n` path weights of a labelling with `B n = 2^n - 1` are distinct. -/
theorem weights_nodup : (weights a b L n).Nodup := by
  apply nodup_of_bw_eq
  rw [← base_eq_sum a b B h1 L hL hsteps n hn, hB, bw_mersenne, card_weights a b L hL n hn]

include hcap

/-- **Lower bound.** Every labelling of every chain for `n` has cap sum at
least `n - 1`: the largest of `n` distinct path weights is at least `n - 1`. -/
theorem capBelow_ge : n - 1 ≤ capBelow cap L n := by
  obtain ⟨x, hx, hle⟩ := exists_ge_of_nodup _ n (weights_nodup a b B L hL h1 hsteps hn hB)
    (card_weights a b L hL n hn) (one_le_of_mem_vals L hL n hn)
  exact hle.trans (weight_le_capBelow a b cap L hL hcap n hn x hx)

/-- **Interval labellings.** Cap sum `n - 1` forces path weights `0, ..., n - 1`. -/
theorem weights_eq_range (hbudget : capBelow cap L n ≤ n - 1) :
    weights a b L n = Multiset.range n := by
  have hpos := one_le_of_mem_vals L hL n hn
  apply eq_range_of_nodup _ n (weights_nodup a b B L hL h1 hsteps hn hB)
    (card_weights a b L hL n hn)
  intro x hx
  have := weight_le_capBelow a b cap L hL hcap n hn x hx
  omega

end Bounds

end ScholzBrauer.CliftLabelling

namespace ScholzBrauer.Clift109

open ScholzBrauer.CliftLabelling

/-- The selected 109 graph with its steps latest first. -/
def stepsRev : List (ℕ × ℕ) := selectedSteps.reverse

theorem stepsRev_valid : valid stepsRev = true := by decide

theorem vals_stepsRev : vals stepsRev = source.reverse := by decide

theorem capBelow_stepsRev (cap : ℕ → ℕ) :
    capBelow cap stepsRev 109 = cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 := by
  simp only [capBelow, vals_stepsRev, source]
  simp
  omega

/-- Every labelling of the selected graph, with seed 1 and target `M109`,
uses at least 108 doublings. No base, shift or carry assumption is needed. -/
theorem cost_ge_108 (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1) :
    108 ≤ cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 := by
  have := capBelow_ge a b B cap stepsRev stepsRev_valid h1
    (fun s hs => hsteps s (List.mem_reverse.mp hs))
    (fun s hs => hcap s (List.mem_reverse.mp hs))
    (by rw [vals_stepsRev]; decide) h109
  rw [capBelow_stepsRev] at this
  omega

/-- A labelling within the 108-doubling budget has path weights exactly
`0, ..., 108` (an interval labelling). Their classification is computational. -/
theorem weights_range_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    weights a b stepsRev 109 = Multiset.range 109 :=
  weights_eq_range a b B cap stepsRev stepsRev_valid h1
    (fun s hs => hsteps s (List.mem_reverse.mp hs))
    (fun s hs => hcap s (List.mem_reverse.mp hs))
    (by rw [vals_stepsRev]; decide) h109 (by rw [capBelow_stepsRev]; omega)

end ScholzBrauer.Clift109

namespace ScholzBrauer.NonHansen29

open ScholzBrauer.CliftLabelling

/-- Clift's selected parents for the non-Hansen 29 source, latest first. -/
def stepsRev : List (ℕ × ℕ) :=
  [(16, 13), (8, 8), (9, 4), (8, 1), (4, 4), (2, 2), (1, 1)]

theorem stepsRev_valid : valid stepsRev = true := by decide

theorem vals_stepsRev : vals stepsRev = source.reverse := by decide

/-- Every labelling of Clift's 29 graph needs at least 28 doublings, so the
one-base repair (caps 1,2,4,8,0,0,13, i.e. 35 additions) is optimal among
labellings of this parent graph. This is not an addition-chain optimum. -/
theorem cost_ge_28 (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ stepsRev,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ stepsRev, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h29 : B 29 = 2 ^ 29 - 1) :
    28 ≤ cap 1 + cap 2 + cap 4 + cap 8 + cap 9 + cap 13 + cap 16 := by
  have := capBelow_ge a b B cap stepsRev stepsRev_valid h1 hsteps hcap
    (by rw [vals_stepsRev]; decide) h29
  simp only [capBelow, vals_stepsRev, source] at this
  simp at this
  omega

end ScholzBrauer.NonHansen29
