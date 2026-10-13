import ScholzBrauer.Clift109Shifted

namespace ScholzBrauer

/-- A divisor by a power of two cannot change the odd part. -/
theorem factor_of_shifted_odd {u v a t : ℕ} (hv : v % 2 = 1)
    (h : u * 2 ^ a = v * 2 ^ t) : ∃ k, u = v * 2 ^ k := by
  induction a generalizing t with
  | zero => exact ⟨t, by simpa using h⟩
  | succ a ih =>
    cases t with
    | zero =>
      have hm := congrArg (· % 2) h
      simp [pow_succ, Nat.mul_mod, hv] at hm
    | succ t =>
      apply ih (t := t)
      simp only [pow_succ] at h
      nlinarith only [h]

/-- A complement that is smaller than the removed block cannot have a gap.
All exponents and the unknown base are unbounded naturals. -/
theorem small_mersenne_complement {p q u a b : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hsmall : u < 2 ^ q - 1)
    (h : u * 2 ^ a + (2 ^ q - 1) * 2 ^ b = 2 ^ (p + q) - 1) :
    ∃ k, u = (2 ^ p - 1) * 2 ^ k := by
  have op := mersenne_mod_two hp
  have oq := mersenne_mod_two hq
  have ot := mersenne_mod_two (show 0 < p + q by omega)
  have block := mersenne_block_identity p q
  have block' := mersenne_block_identity q p
  rw [Nat.add_comm q p] at block'
  rw [Nat.mul_comm (2 ^ q)] at block
  rw [Nat.mul_comm (2 ^ p)] at block'
  have pq : 0 < 2 ^ q - 1 := by omega
  have pp := Nat.two_pow_pos p
  have pa := Nat.two_pow_pos a
  by_cases hb : b = 0
  · subst b
    have he : u * 2 ^ a = (2 ^ p - 1) * 2 ^ q := by
      simp only [pow_zero, Nat.mul_one] at h
      omega
    exact factor_of_shifted_odd op he
  · have ha : a = 0 := by
      by_contra ha
      obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
      obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
      have hm := congrArg (· % 2) h
      simp [pow_succ, Nat.mul_mod, Nat.add_mod, ot] at hm
    subst a
    simp only [pow_zero, Nat.mul_one] at h
    have hbp : b ≤ p := by
      by_contra hbp
      have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show p + 1 ≤ b by omega)
      rw [pow_succ] at he
      have hq2 : 2 ≤ 2 ^ q := by omega
      have hm := Nat.mul_le_mul_left (2 ^ q - 1) he
      have hpos := Nat.le_mul_of_pos_left (2 ^ p) pq
      have hpbound : 2 ^ p - 1 < 2 ^ p := by omega
      nlinarith only [hm, h, block', hpos, hpbound]
    have hpb : p ≤ b := by
      by_contra hpb
      have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show b + 1 ≤ p by omega)
      rw [pow_succ] at he
      have pb := Nat.two_pow_pos b
      have hm := Nat.mul_le_mul_left (2 ^ q - 1) he
      have hpos := Nat.le_mul_of_pos_right (2 ^ q - 1) pb
      nlinarith only [hm, h, block', hpos, hsmall]
    have : b = p := by omega
    subst b
    exact ⟨0, by simp; omega⟩

/-- Every non-block complement is exactly two separated binary intervals:
[0,b) and [q+b,p+q). This gives its shape, not just a finite search bound. -/
theorem nonblock_mersenne_complement {p q u a b : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (h : u * 2 ^ a + (2 ^ q - 1) * 2 ^ b = 2 ^ (p + q) - 1)
    (hn : ¬ ∃ k, u = (2 ^ p - 1) * 2 ^ k) :
    a = 0 ∧ 0 < b ∧ b < p ∧
      u = (2 ^ (p - b) - 1) * 2 ^ (q + b) + (2 ^ b - 1) := by
  have op := mersenne_mod_two hp
  have oq := mersenne_mod_two hq
  have ot := mersenne_mod_two (show 0 < p + q by omega)
  have block := mersenne_block_identity p q
  have block' := mersenne_block_identity q p
  rw [Nat.add_comm q p] at block'
  rw [Nat.mul_comm (2 ^ q)] at block
  rw [Nat.mul_comm (2 ^ p)] at block'
  have pq : 0 < 2 ^ q - 1 := by omega
  have hb : b ≠ 0 := by
    intro hb
    subst b
    simp only [pow_zero, Nat.mul_one] at h
    exact hn (factor_of_shifted_odd op (show
      u * 2 ^ a = (2 ^ p - 1) * 2 ^ q by omega))
  have ha : a = 0 := by
    by_contra ha
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
    have hm := congrArg (· % 2) h
    simp [pow_succ, Nat.mul_mod, Nat.add_mod, ot] at hm
  subst a
  simp only [pow_zero, Nat.mul_one] at h
  have hbp : b ≤ p := by
    by_contra hbp
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show p + 1 ≤ b by omega)
    rw [pow_succ] at he
    have hm := Nat.mul_le_mul_left (2 ^ q - 1) he
    have hpos := Nat.le_mul_of_pos_left (2 ^ p) pq
    have hpbound : 2 ^ p - 1 < 2 ^ p := by have := Nat.two_pow_pos p; omega
    nlinarith only [hm, h, block', hpos, hpbound]
  have hne : b ≠ p := by
    intro he
    subst b
    apply hn
    exact ⟨0, by simp; omega⟩
  refine ⟨rfl, by omega, by omega, ?_⟩
  have outer := mersenne_block_identity (p - b) (q + b)
  have inner := mersenne_block_identity q b
  have indices : p - b + (q + b) = p + q := by omega
  rw [indices, Nat.mul_comm (2 ^ (q + b))] at outer
  rw [Nat.mul_comm (2 ^ b)] at inner
  omega

/-- Repeated consumers force the detours to be blocks without fixing any of
2, 4, 8 or 15. The fixed tail bounds every early base by M23. -/
theorem Clift109.early_detours_rigid (B a b : ℕ → ℕ)
    (hpos : ∀ v ∈ Clift109.source, 0 < B v)
    (hsteps : ∀ s ∈ Clift109.selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (h23 : B 23 = 2 ^ 23 - 1) (h28 : B 28 = 2 ^ 28 - 1)
    (h51 : B 51 = 2 ^ 51 - 1) (h58 : B 58 = 2 ^ 58 - 1) :
    (∃ k : Fin 19, B 5 = (2 ^ 5 - 1) * 2 ^ (k : ℕ)) ∧
    (∃ k : Fin 17, B 7 = (2 ^ 7 - 1) * 2 ^ (k : ℕ)) := by
  have s7 := hsteps (5, 2) (by decide)
  have s15 := hsteps (8, 7) (by decide)
  have s23 := hsteps (15, 8) (by decide)
  have s28 := hsteps (23, 5) (by decide)
  have s58 := hsteps (51, 7) (by decide)
  norm_num only at s7 s15 s23 s28 s58
  have p8 := hpos 8 (by decide)
  have l5 := Nat.le_mul_of_pos_right (B 5) (Nat.two_pow_pos (a 7))
  have l7 := Nat.le_mul_of_pos_right (B 7) (Nat.two_pow_pos (b 15))
  have l15 := Nat.le_mul_of_pos_right (B 15) (Nat.two_pow_pos (a 23))
  have p8s := Nat.mul_pos p8 (Nat.two_pow_pos (b 23))
  have small5 : B 5 < 2 ^ 23 - 1 := by omega
  have small7 : B 7 < 2 ^ 23 - 1 := by omega
  have e28 : B 5 * 2 ^ b 28 + (2 ^ 23 - 1) * 2 ^ a 28 =
      2 ^ (5 + 23) - 1 := by
    simpa [h23, h28, Nat.add_comm] using s28
  have e58 : B 7 * 2 ^ b 58 + (2 ^ 51 - 1) * 2 ^ a 58 =
      2 ^ (7 + 51) - 1 := by
    simpa [h51, h58, Nat.add_comm] using s58
  have small7' : B 7 < 2 ^ 51 - 1 := by
    norm_num at small7 ⊢
    omega
  obtain ⟨k, hk⟩ := small_mersenne_complement (p := 5) (q := 23)
    (u := B 5) (a := b 28) (b := a 28) (by decide) (by decide) small5 e28
  obtain ⟨l, hl⟩ := small_mersenne_complement (p := 7) (q := 51)
    (u := B 7) (a := b 58) (b := a 58) (by decide) (by decide) small7' e58
  have bk : k < 19 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 19 ≤ k by omega)
    norm_num at hp hk small5
    omega
  have bl : l < 17 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 17 ≤ l by omega)
    norm_num at hp hl small7
    omega
  exact ⟨⟨⟨k, bk⟩, hk⟩, ⟨⟨l, bl⟩, hl⟩⟩

end ScholzBrauer
