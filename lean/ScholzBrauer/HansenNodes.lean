import ScholzBrauer.BrauerBlock
import Mathlib.Data.List.Nodup

/-! Values for the nodes in a Hansen lift. A node `(a,k)` represents the
Mersenne value for a positive source exponent `a`, doubled `k` times.
Unique odd parts make this representation injective, independently of any
marking or shift cap. This file does not yet construct a sorted replay. -/
namespace ScholzBrauer

/-- The numerical value of a source exponent and a stored shift. -/
def shiftedMersenne (a k : ℕ) : ℕ := 2 ^ k * (2 ^ a - 1)

/-- Positive Mersenne values have odd remainder, including the base `a=1`. -/
theorem mersenne_mod_two {a : ℕ} (ha : 0 < a) : (2 ^ a - 1) % 2 = 1 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  rw [pow_succ]
  have hp := Nat.two_pow_pos a
  omega

/-- Uniqueness of a power of two times an odd natural number. Repeatedly
cancel a common factor two; unequal shifts would equate odd and even values. -/
theorem two_pow_mul_odd_unique {u v k l : ℕ} (hu : u % 2 = 1)
    (hv : v % 2 = 1) (h : 2 ^ k * u = 2 ^ l * v) : k = l ∧ u = v := by
  induction k generalizing l with
  | zero =>
    cases l with
    | zero => simpa using h
    | succ l =>
      have hm := congrArg (· % 2) h
      simp [pow_succ, Nat.mul_mod, hu] at hm
  | succ k ih =>
    cases l with
    | zero =>
      have hm := congrArg (· % 2) h
      simp [pow_succ, Nat.mul_mod, hv] at hm
    | succ l =>
      have hc : 2 ^ k * u = 2 ^ l * v := by
        apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
        simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
      obtain ⟨hkl, huv⟩ := ih hc
      exact ⟨congrArg Nat.succ hkl, huv⟩

/-- No two positive source exponents and shifts represent the same node. -/
theorem shiftedMersenne_eq_iff {a b k l : ℕ} (ha : 0 < a) (hb : 0 < b) :
    shiftedMersenne a k = shiftedMersenne b l ↔ a = b ∧ k = l := by
  constructor
  · intro h
    obtain ⟨hkl, hab⟩ := two_pow_mul_odd_unique (k := k) (l := l)
      (mersenne_mod_two ha) (mersenne_mod_two hb) h
    have hpa := Nat.two_pow_pos a
    have hpb := Nat.two_pow_pos b
    have he : 2 ^ a = 2 ^ b := by omega
    exact ⟨Nat.pow_right_injective (by decide : 2 ≤ 2) he, hkl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A positive-exponent node has positive value, so each summand is smaller
than its sum in a later sorted construction. -/
theorem shiftedMersenne_pos {a : ℕ} (ha : 0 < a) (k : ℕ) :
    0 < shiftedMersenne a k := by
  have hm := mersenne_mod_two ha
  exact Nat.mul_pos (Nat.two_pow_pos k) (by omega)

/-- Successive shifts are explicit doubling steps. -/
theorem shiftedMersenne_succ (a k : ℕ) :
    shiftedMersenne a (k + 1) = shiftedMersenne a k + shiftedMersenne a k := by
  simp [shiftedMersenne, pow_succ, Nat.mul_comm, Nat.two_mul, Nat.add_mul]

/-- The base-node sum is the existing exact Mersenne block identity. This
equation alone does not establish that the requested nodes were allocated. -/
theorem shiftedMersenne_base_sum (a b : ℕ) :
    shiftedMersenne a b + shiftedMersenne b 0 = shiftedMersenne (a + b) 0 := by
  simpa [shiftedMersenne] using mersenne_block_identity a b

/-- Distinct node labels remain distinct after conversion to numerical values.
The positivity hypothesis is essential; all labels `(0,k)` have value zero. -/
theorem shiftedMersenne_nodup {nodes : List (ℕ × ℕ)} (hn : nodes.Nodup)
    (hp : ∀ p ∈ nodes, 0 < p.1) :
    (nodes.map (fun p => shiftedMersenne p.1 p.2)).Nodup := by
  apply hn.map_on
  intro p hpn q hqn heq
  have he := (shiftedMersenne_eq_iff (hp p hpn) (hp q hqn)).mp heq
  exact Prod.ext he.1 he.2

-- Essential boundary: allowing exponent zero destroys injectivity.
example : shiftedMersenne 0 0 = shiftedMersenne 0 1 := by decide
example : shiftedMersenne 1 0 = 1 := by decide
example : shiftedMersenne 1 8 = 256 := by decide
-- Interleaving nodes from the saved 29 fixture remain distinct.
example : [shiftedMersenne 8 1, shiftedMersenne 9 0, shiftedMersenne 8 2] =
    [510, 511, 1020] := by decide
example : [shiftedMersenne 8 4, shiftedMersenne 12 0, shiftedMersenne 8 5] =
    [4080, 4095, 8160] := by decide
-- Universal separation for the retained 12 anchor and unmarked 13 in 12509.
example (k l : ℕ) : shiftedMersenne 12 k ≠ shiftedMersenne 13 l := by
  intro h
  have := (shiftedMersenne_eq_iff (by decide) (by decide)).mp h
  omega

end ScholzBrauer
