import ScholzBrauer.Hansen
import ScholzBrauer.StarLift

/-! The selected graph in Clift's `LargeNonHansen.png`, rechecked 2026-10-08.
The graph uses 8 = 4 + 4. The value sequence also permits 8 = 7 + 1 and is
therefore a star source. These are different parent graphs.

We prove the standard-orientation minimum and the failure of the previously
proved one-gap repair at its later reuse. The wider two-exception enumeration
is a separate exact Python result; arbitrary-labelling impossibility is not
asserted here. -/
namespace ScholzBrauer.Clift109

def source : List ℕ := [1, 2, 4, 5, 7, 8, 15, 23, 28, 51, 58, 109]

def selectedSteps : List Step :=
  [(1, 1), (2, 2), (4, 1), (5, 2), (4, 4), (8, 7),
   (15, 8), (23, 5), (28, 23), (51, 7), (58, 51)]

theorem selected_replay : replay selectedSteps = some source := by decide +kernel

theorem source_valid : IsAdditionChain source := replay_sound selected_replay

/-- This checks all source values using the alternate parent choice at 8. -/
theorem source_is_star : IsStarFrom [1] 1 [1, 2, 1, 2, 1, 7, 8, 5, 23, 7, 51] := by
  decide +kernel

theorem alternate_source :
    starSourceFrom [1] 1 [1, 2, 1, 2, 1, 7, 8, 5, 23, 7, 51] = source := by
  decide +kernel

theorem source_is_hansen : IsHansenFrom [1] 1
    [(2, true), (4, true), (5, true), (7, true), (8, true), (15, true),
     (23, true), (28, true), (51, true), (58, true), (109, true)] := by
  decide +kernel

/-- The selected graph cannot use the latest marked parent even through 8.
The first doubling forces marking 2; the next two sums and the doubling from 4
then give incompatible anchor requirements. Marking 8 cannot fix earlier sums. -/
theorem selected_prefix_no_marking (m2 m4 m5 m7 : Bool) :
    let a2 := if m2 then 2 else 1
    let a4 := if m4 then 4 else a2
    let a5 := if m5 then 5 else a4
    let a7 := if m7 then 7 else a5
    ¬ (a2 = 2 ∧ (a4 = 4 ∨ a4 = 1) ∧ (a5 = 5 ∨ a5 = 2) ∧ a7 = 4) := by
  revert m2 m4 m5 m7
  decide +kernel

/-- Maximal outgoing shifts for every standard Mersenne orientation.
Booleans reverse the unequal pair at the vertex named by the argument. -/
def mersenneCaps (r5 r7 r15 r23 r28 r51 r58 r109 : Bool) : List ℕ :=
  [max 1 (if r5 then 4 else 0),
   max 2 (if r7 then 5 else 0),
   4,
   max (if r7 then 0 else 2) (if r28 then 23 else 0),
   max (if r15 then 8 else 0) (if r58 then 51 else 0),
   max (if r15 then 0 else 7) (if r23 then 15 else 0),
   if r23 then 0 else 8,
   max (if r28 then 0 else 5) (if r51 then 28 else 0),
   if r51 then 0 else 23,
   max (if r58 then 0 else 7) (if r109 then 58 else 0),
   if r109 then 0 else 51,
   0]

theorem mersenne_orientation_min :
    (∀ a b c d e f g h, 110 ≤ (mersenneCaps a b c d e f g h).sum) ∧
    (mersenneCaps false false false false false false false false).sum = 110 := by
  decide +kernel

/-- A generic finite bound used to turn the next obstruction into an exhaustive
kernel computation, rather than assuming that tested shifts cover all shifts. -/
theorem shift_lt_of_sum {u v a b n : ℕ} (hu : 0 < u)
    (h : u * 2 ^ a + v * 2 ^ b = 2 ^ n - 1) : a < n := by
  by_contra hn
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show n ≤ a by omega)
  have hmul : 2 ^ a ≤ u * 2 ^ a := by
    simpa using Nat.mul_le_mul_right (2 ^ a) hu
  have hpos := Nat.two_pow_pos n
  omega

/-- The existing one-gap lift at A=4,B=2 assigns base 121 to source vertex 5.
It cannot be reused to construct M(28) alongside the unchanged M(23), under
ANY nonnegative shifts. Thus the later use of 5 blocks this local repair. -/
theorem repaired_five_cannot_feed_28 (a b : ℕ) :
    121 * 2 ^ a + (2 ^ 23 - 1) * 2 ^ b ≠ (2 ^ 28 - 1 : ℕ) := by
  intro h
  have ha : a < 28 := shift_lt_of_sum (by decide) h
  have hb : b < 28 := shift_lt_of_sum (by decide)
    (show (2 ^ 23 - 1) * 2 ^ b + 121 * 2 ^ a = (2 ^ 28 - 1 : ℕ) by omega)
  have finite : ∀ x y : Fin 28,
      121 * 2 ^ (x : ℕ) + (2 ^ 23 - 1) * 2 ^ (y : ℕ) ≠ (2 ^ 28 - 1 : ℕ) := by
    decide +kernel
  exact finite ⟨a, ha⟩ ⟨b, hb⟩ h

/-- The obstructed base is precisely the one in the existing family, not a
numerical approximation to it. -/
theorem initial_repair_values :
    2 ^ (2 + 1) * (2 ^ 4 - 1) + 1 = (121 : ℕ) ∧
    121 + 2 * (2 ^ 2 - 1) = (2 ^ 7 - 1 : ℕ) := by
  decide +kernel


/-- Reusing base 5 at 28, while it also lies below M15, forces a shifted M5.
The finite check exhausts shifts, not all possible natural-number bases. -/
theorem small_five_is_shifted_mersenne {u a b : ℕ} (hu : 0 < u)
    (hsmall : u ≤ 2 ^ 15 - 1)
    (h : u * 2 ^ a + (2 ^ 23 - 1) * 2 ^ b = (2 ^ 28 - 1 : ℕ)) :
    ∃ k : Fin 11, u = (2 ^ 5 - 1) * 2 ^ (k : ℕ) := by
  have ha : a < 28 := shift_lt_of_sum hu h
  have hb : b < 6 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 6 ≤ b by omega)
    change 64 ≤ 2 ^ b at hp
    change u * 2 ^ a + 8388607 * 2 ^ b = 268435455 at h
    omega
  have he : u * 2 ^ a = (2 ^ 28 - 1) - (2 ^ 23 - 1) * 2 ^ b := by omega
  have hd : ((2 ^ 28 - 1) - (2 ^ 23 - 1) * 2 ^ b) / 2 ^ a = u := by
    rw [← he]; exact Nat.mul_div_cancel u (Nat.two_pow_pos a)
  have hr : ((2 ^ 28 - 1) - (2 ^ 23 - 1) * 2 ^ b) % 2 ^ a = 0 := by
    rw [← he]; simp
  have finite : ∀ x : Fin 28, ∀ y : Fin 6,
      let rem := (2 ^ 28 - 1) - (2 ^ 23 - 1) * 2 ^ (y : ℕ)
      rem % 2 ^ (x : ℕ) = 0 → rem / 2 ^ (x : ℕ) ≤ 2 ^ 15 - 1 →
      ∃ k : Fin 11, rem / 2 ^ (x : ℕ) = (2 ^ 5 - 1) * 2 ^ (k : ℕ) := by
    decide +kernel
  simpa only [hd] using finite ⟨a, ha⟩ ⟨b, hb⟩ hr (by simpa only [hd] using hsmall)

theorem small_seven_is_shifted_mersenne {u a b : ℕ} (hu : 0 < u)
    (hsmall : u ≤ 2 ^ 15 - 1)
    (h : u * 2 ^ a + (2 ^ 51 - 1) * 2 ^ b = (2 ^ 58 - 1 : ℕ)) :
    ∃ k : Fin 9, u = (2 ^ 7 - 1) * 2 ^ (k : ℕ) := by
  have ha : a < 58 := shift_lt_of_sum hu h
  have hb : b < 8 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 8 ≤ b by omega)
    change 256 ≤ 2 ^ b at hp
    change u * 2 ^ a + 2251799813685247 * 2 ^ b = 288230376151711743 at h
    omega
  have he : u * 2 ^ a = (2 ^ 58 - 1) - (2 ^ 51 - 1) * 2 ^ b := by omega
  have hd : ((2 ^ 58 - 1) - (2 ^ 51 - 1) * 2 ^ b) / 2 ^ a = u := by
    rw [← he]; exact Nat.mul_div_cancel u (Nat.two_pow_pos a)
  have hr : ((2 ^ 58 - 1) - (2 ^ 51 - 1) * 2 ^ b) % 2 ^ a = 0 := by
    rw [← he]; simp
  have finite : ∀ x : Fin 58, ∀ y : Fin 8,
      let rem := (2 ^ 58 - 1) - (2 ^ 51 - 1) * 2 ^ (y : ℕ)
      rem % 2 ^ (x : ℕ) = 0 → rem / 2 ^ (x : ℕ) ≤ 2 ^ 15 - 1 →
      ∃ k : Fin 9, rem / 2 ^ (x : ℕ) = (2 ^ 7 - 1) * 2 ^ (k : ℕ) := by
    decide +kernel
  simpa only [hd] using finite ⟨a, ha⟩ ⟨b, hb⟩ hr (by simpa only [hd] using hsmall)
/-- Four equations of the selected graph force both detour bases to be
shifted Mersennes, even though we initially allow arbitrary positive integers.
This is a structural restriction, not a general graph-labelling impossibility. -/
theorem detour_bases_rigid {u v a b c d e f g h : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (h7 : u * 2 ^ a + 3 * 2 ^ b = v)
    (h15 : v * 2 ^ c + 255 * 2 ^ d = (2 ^ 15 - 1 : ℕ))
    (h28 : u * 2 ^ e + (2 ^ 23 - 1) * 2 ^ f = (2 ^ 28 - 1 : ℕ))
    (h58 : v * 2 ^ g + (2 ^ 51 - 1) * 2 ^ h = (2 ^ 58 - 1 : ℕ)) :
    (∃ k : Fin 11, u = (2 ^ 5 - 1) * 2 ^ (k : ℕ)) ∧
    (∃ k : Fin 9, v = (2 ^ 7 - 1) * 2 ^ (k : ℕ)) := by
  have hvle := Nat.le_mul_of_pos_right v (Nat.two_pow_pos c)
  have hule := Nat.le_mul_of_pos_right u (Nat.two_pow_pos a)
  have hvsmall : v ≤ 2 ^ 15 - 1 := by omega
  have husmall : u ≤ 2 ^ 15 - 1 := by omega
  exact ⟨small_five_is_shifted_mersenne hu husmall h28,
    small_seven_is_shifted_mersenne hv hvsmall h58⟩

end ScholzBrauer.Clift109
