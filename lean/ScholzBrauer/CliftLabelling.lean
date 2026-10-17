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
graph. A budget-attaining labelling has a critical path: each selected edge
attains its tail cap, and skipped vertices have cap zero. The classification
of the interval labellings remains computational
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

/-! ## Critical paths

A path records its edges latest first as `(tail vertex, shift)`. The constructors
retain the selected parent even when two parents coincide. This small witness
relation is needed because the existing multiset records weights, not paths.
-/

/-- A selected-parent path from seed 1, with edges recorded latest first. -/
inductive Path (a b : ℕ → ℕ) : List (ℕ × ℕ) → ℕ → List (ℕ × ℕ) → Prop
  | seed : Path a b [] 1 []
  | older {s rest v es} : v ≠ s.1 + s.2 → Path a b rest v es →
      Path a b (s :: rest) v es
  | left {s rest es} : Path a b rest s.1 es →
      Path a b (s :: rest) (s.1 + s.2) ((s.1, a (s.1 + s.2)) :: es)
  | right {s rest es} : Path a b rest s.2 es →
      Path a b (s :: rest) (s.1 + s.2) ((s.2, b (s.1 + s.2)) :: es)

/-- Every path witness has its recorded shift sum in the existing weight multiset. -/
theorem Path.weight_mem {a b : ℕ → ℕ} {L v es} (h : Path a b L v es) :
    (es.map Prod.snd).sum ∈ weights a b L v := by
  induction h with
  | seed => simp [weights]
  | older hne _ ih => simpa [weights, hne] using ih
  | left _ ih =>
    simp only [List.map_cons, List.sum_cons, weights, ite_true, Multiset.mem_add]
    exact Or.inl (Multiset.mem_map.mpr ⟨_, ih, by omega⟩)
  | right _ ih =>
    simp only [List.map_cons, List.sum_cons, weights, ite_true, Multiset.mem_add]
    exact Or.inr (Multiset.mem_map.mpr ⟨_, ih, by omega⟩)

/-- A saturated prefix-plus-parent budget leaves no cap above that parent. -/
private theorem cap_zero_above (cap : ℕ → ℕ) (l : List ℕ) (p u : ℕ)
    (hp : p ∈ l) (hu : u ∈ l) (hpu : p < u)
    (heq : ((l.filter (· < p)).map cap).sum + cap p = (l.map cap).sum) :
    cap u = 0 := by
  have hp' : p ∈ l.filter (· < u) := List.mem_filter.mpr ⟨hp, by simpa using hpu⟩
  have hfilter : (l.filter (· < u)).filter (· < p) = l.filter (· < p) := by
    rw [List.filter_filter]
    congr 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hlow := sum_filter_add_le cap p (l.filter (· < u)) hp'
  rw [hfilter] at hlow
  have hhigh := sum_filter_add_le cap u l hu
  omega

/-- If a weight attains the entire cap budget, it has a path witness using a
maximum shift at every visited tail, and every skipped earlier vertex has cap 0. -/
theorem critical_path_of_weight (a b cap : ℕ → ℕ) :
    ∀ L : List (ℕ × ℕ), valid L = true →
      (∀ s ∈ L, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2) →
      ∀ v ∈ vals L, capBelow cap L v ∈ weights a b L v →
      ∃ es, Path a b L v es ∧ (es.map Prod.snd).sum = capBelow cap L v ∧
        (∀ e ∈ es, e.2 = cap e.1) ∧
        (∀ u ∈ vals L, u < v → u ∉ es.map Prod.fst → cap u = 0)
  | [], _, _, v, hv, _ => by
    simp only [vals, List.mem_singleton] at hv
    subst v
    refine ⟨[], Path.seed, ?_, ?_, ?_⟩
    · simp [capBelow, vals]
    · simp
    · simp [vals]
  | s :: rest, hL, hc, v, hv, hw => by
    obtain ⟨hp, hq, hlt, hr⟩ := valid_cons hL
    have hc' : ∀ t ∈ rest, a (t.1 + t.2) ≤ cap t.1 ∧ b (t.1 + t.2) ≤ cap t.2 :=
      fun t ht => hc t (List.mem_cons_of_mem _ ht)
    have ih := critical_path_of_weight a b cap rest hr hc'
    rcases List.mem_cons.mp hv with rfl | hv
    · have hall : (vals rest).filter (· < s.1 + s.2) = vals rest :=
        List.filter_eq_self.mpr (fun u hu => by simpa using hlt u hu)
      have htotal : capBelow cap (s :: rest) (s.1 + s.2) = ((vals rest).map cap).sum := by
        simp [capBelow, vals, hall]
      rw [htotal, weights, if_pos rfl] at hw
      simp only [Multiset.mem_add, Multiset.mem_map] at hw
      have branch (p shift : ℕ) (hp : p ∈ vals rest) (hshift : shift ≤ cap p)
          (hw : ∃ y ∈ weights a b rest p, y + shift = ((vals rest).map cap).sum)
          (extend : ∀ es, Path a b rest p es →
            Path a b (s :: rest) (s.1 + s.2) ((p, shift) :: es)) :
          ∃ es, Path a b (s :: rest) (s.1 + s.2) es ∧
            (es.map Prod.snd).sum = capBelow cap (s :: rest) (s.1 + s.2) ∧
            (∀ e ∈ es, e.2 = cap e.1) ∧
            (∀ u ∈ vals (s :: rest), u < s.1 + s.2 →
              u ∉ es.map Prod.fst → cap u = 0) := by
        obtain ⟨y, hy, heq⟩ := hw
        have hbound := weight_le_capBelow a b cap rest hr hc' p hp y hy
        have hsum := sum_filter_add_le cap p (vals rest) hp
        have hycap : y = capBelow cap rest p := by unfold capBelow at *; omega
        have hmax : shift = cap p := by unfold capBelow at *; omega
        have hfull : capBelow cap rest p + cap p = ((vals rest).map cap).sum := by omega
        rw [hycap] at hy
        obtain ⟨es, hpath, hweight, hsat, hzero⟩ := ih p hp hy
        refine ⟨(p, shift) :: es, extend es hpath, ?_, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, htotal]
          omega
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hmax
          · exact hsat e he
        · intro u hu huv hnot
          have hu' : u ∈ vals rest := by
            rcases List.mem_cons.mp hu with rfl | hu
            · omega
            · exact hu
          have hne : u ≠ p := by
            intro he
            apply hnot
            simp [he]
          have hnot' : u ∉ es.map Prod.fst := fun hm =>
            hnot (List.mem_cons_of_mem _ hm)
          rcases lt_or_gt_of_ne hne with hup | hpu
          · exact hzero u hu' hup hnot'
          · exact cap_zero_above cap (vals rest) p u hp hu' hpu hfull
      rcases hw with hw | hw
      · exact branch s.1 _ hp (hc s (List.mem_cons_self ..)).1 hw
          (fun _ h => Path.left h)
      · exact branch s.2 _ hq (hc s (List.mem_cons_self ..)).2 hw
          (fun _ h => Path.right h)
    · have hne : v ≠ s.1 + s.2 := (hlt v hv).ne
      have hnlt : ¬ s.1 + s.2 < v := by have := hlt v hv; omega
      have hsame : capBelow cap (s :: rest) v = capBelow cap rest v := by
        simp [capBelow, vals, hnlt]
      rw [hsame, weights, if_neg hne] at hw
      obtain ⟨es, hpath, hweight, hsat, hzero⟩ := ih v hv hw
      refine ⟨es, Path.older hne hpath, by simpa [hsame] using hweight, hsat, ?_⟩
      intro u hu huv hnot
      rcases List.mem_cons.mp hu with rfl | hu
      · omega
      · exact hzero u hu huv hnot

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

/-- An interval labelling has a critical path of weight `n-1`: each selected
edge attains its tail's cap, and every skipped vertex below `n` has cap zero. -/
theorem critical_path_of_budget (hbudget : capBelow cap L n ≤ n - 1) :
    ∃ es, Path a b L n es ∧ (es.map Prod.snd).sum = n - 1 ∧
      (∀ e ∈ es, e.2 = cap e.1) ∧
      (∀ u ∈ vals L, u < n → u ∉ es.map Prod.fst → cap u = 0) := by
  have hcost : capBelow cap L n = n - 1 :=
    Nat.le_antisymm hbudget (capBelow_ge a b B cap L hL h1 hsteps hcap hn hB)
  have hrange := weights_eq_range a b B cap L hL h1 hsteps hcap hn hB hbudget
  have hpos := one_le_of_mem_vals L hL n hn
  have hw : capBelow cap L n ∈ weights a b L n := by
    rw [hcost, hrange, Multiset.mem_range]
    omega
  obtain ⟨es, hp, hw, hs, hz⟩ := critical_path_of_weight a b cap L hL hcap n hn hw
  exact ⟨es, hp, by omega, hs, hz⟩

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

/-- The critical-path conditions for the selected 109 graph: a weight-108
path attains every visited cap and every outgoing edge from an unvisited tail
has shift zero. This is step 4 of the computational box reduction. -/
theorem critical_path_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    ∃ es, Path a b stepsRev 109 es ∧ (es.map Prod.snd).sum = 108 ∧
      (∀ e ∈ es, e.2 = cap e.1) ∧
      (∀ u ∈ source, u < 109 → u ∉ es.map Prod.fst → cap u = 0) ∧
      (∀ s ∈ selectedSteps,
        (s.1 ∉ es.map Prod.fst → a (s.1 + s.2) = 0) ∧
        (s.2 ∉ es.map Prod.fst → b (s.1 + s.2) = 0)) := by
  obtain ⟨es, hp, hw, hs, hz⟩ := CliftLabelling.critical_path_of_budget a b B cap
    stepsRev stepsRev_valid h1
    (fun s hs => hsteps s (List.mem_reverse.mp hs))
    (fun s hs => hcap s (List.mem_reverse.mp hs))
    (by rw [vals_stepsRev]; decide) h109 (by rw [capBelow_stepsRev]; omega)
  have hz' : ∀ u ∈ source, u < 109 → u ∉ es.map Prod.fst → cap u = 0 := by
    simpa only [vals_stepsRev, List.mem_reverse] using hz
  refine ⟨es, hp, hw, hs, hz', ?_⟩
  have hparents : ∀ s ∈ selectedSteps,
      s.1 ∈ source ∧ s.1 < 109 ∧ s.2 ∈ source ∧ s.2 < 109 := by decide
  intro s hmem
  obtain ⟨hp, hp_lt, hq, hq_lt⟩ := hparents s hmem
  obtain ⟨ha, hb⟩ := hcap s hmem
  constructor
  · intro hnot
    have := hz' s.1 hp hp_lt hnot
    omega
  · intro hnot
    have := hz' s.2 hq hq_lt hnot
    omega

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
