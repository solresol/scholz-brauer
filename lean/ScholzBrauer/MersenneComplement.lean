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

/-- Complete local domain, including the shifts: either two adjoining blocks,
or a uniquely positioned pair of separated intervals. No finite shift cutoff
or carry-free assumption is used. -/
theorem mersenne_complement_iff {p q u a b : ℕ} (hp : 0 < p) (hq : 0 < q) :
    u * 2 ^ a + (2 ^ q - 1) * 2 ^ b = 2 ^ (p + q) - 1 ↔
    (∃ k, u = (2 ^ p - 1) * 2 ^ k ∧
      ((k + a = q ∧ b = 0) ∨ (k + a = 0 ∧ b = p))) ∨
    (a = 0 ∧ 0 < b ∧ b < p ∧
      u = (2 ^ (p - b) - 1) * 2 ^ (q + b) + (2 ^ b - 1)) := by
  constructor
  · intro h
    by_cases hb : ∃ k, u = (2 ^ p - 1) * 2 ^ k
    · obtain ⟨k, hk⟩ := hb
      have hs : (2 ^ p - 1) * 2 ^ (k + a) + (2 ^ q - 1) * 2 ^ b =
          (2 ^ (p + q) - 1) * 2 ^ 0 := by
        simpa [hk, pow_add, Nat.mul_assoc] using h
      have ho := Clift109.mersenne_sum_shifts hp hq (k + a) b 0 hs
      exact Or.inl ⟨k, hk, by simpa using ho⟩
    · exact Or.inr (nonblock_mersenne_complement hp hq h hb)
  · rintro (⟨k, rfl, h | h⟩ | ⟨rfl, hb, hbp, rfl⟩)
    · rw [Nat.mul_assoc, ← pow_add, h.1, h.2]
      simpa [Nat.mul_comm] using mersenne_block_identity p q
    · rw [Nat.mul_assoc, ← pow_add, h.1, h.2]
      simpa [Nat.mul_comm, Nat.add_comm] using mersenne_block_identity q p
    · have outer := mersenne_block_identity (p - b) (q + b)
      have inner := mersenne_block_identity q b
      have indices : p - b + (q + b) = p + q := by omega
      rw [indices, Nat.mul_comm (2 ^ (q + b))] at outer
      rw [Nat.mul_comm (2 ^ b)] at inner
      simp only [pow_zero, Nat.mul_one]
      omega

/-- A separated-interval complement occupies more than half the full block.
This stronger smallness criterion still forces a block even when u >= Mq. -/
theorem half_mersenne_complement {p q u a b : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hsmall : 2 * u < 2 ^ (p + q) - 1)
    (h : u * 2 ^ a + (2 ^ q - 1) * 2 ^ b = 2 ^ (p + q) - 1) :
    ∃ k, u = (2 ^ p - 1) * 2 ^ k := by
  by_contra hn
  obtain ⟨ha, hb, hbp, _⟩ := nonblock_mersenne_complement hp hq h hn
  subst a
  simp only [pow_zero, Nat.mul_one] at h
  have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show b + 1 ≤ p by omega)
  rw [pow_succ] at he
  have hm := Nat.mul_le_mul_left (2 ^ q - 1) he
  have block := mersenne_block_identity q p
  rw [Nat.add_comm q p, Nat.mul_comm (2 ^ p)] at block
  have pp := Nat.two_pow_pos p
  nlinarith only [hm, block, h, hsmall, pp]

/-- Exactly the finite candidate shapes when shifts are existentially hidden. -/
theorem mersenne_complement_domain {p q u : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (∃ a b, u * 2 ^ a + (2 ^ q - 1) * 2 ^ b = 2 ^ (p + q) - 1) ↔
    (∃ k : Fin (q + 1), u = (2 ^ p - 1) * 2 ^ (k : ℕ)) ∨
    (∃ b : Fin p, 0 < (b : ℕ) ∧
      u = (2 ^ (p - (b : ℕ)) - 1) * 2 ^ (q + (b : ℕ)) + (2 ^ (b : ℕ) - 1)) := by
  constructor
  · rintro ⟨a, b, h⟩
    rcases (mersenne_complement_iff hp hq).mp h with ⟨k, hk, ho⟩ | ⟨ha, hb, hbp, hu⟩
    · exact Or.inl ⟨⟨k, by rcases ho with ho | ho <;> omega⟩, hk⟩
    · exact Or.inr ⟨⟨b, hbp⟩, hb, hu⟩
  · rintro (⟨k, hk⟩ | ⟨b, hb, hu⟩)
    · refine ⟨q - k, 0, (mersenne_complement_iff hp hq).mpr ?_⟩
      exact Or.inl ⟨k, hk, Or.inl ⟨by have := k.isLt; omega, rfl⟩⟩
    · exact ⟨0, b, (mersenne_complement_iff hp hq).mpr
        (Or.inr ⟨rfl, hb, b.isLt, hu⟩)⟩

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

/-- Fixing only terminal M109 and B58=M58 forces B51 and B7 to be
shifted blocks. All other intermediate bases, including 23 and 28, are free.
Repeated consumption gives 2*B7 < B51 < M58, excluding the separated case. -/
theorem Clift109.fixed58_tail_rigid (B a b : ℕ → ℕ)
    (hpos : ∀ v ∈ Clift109.source, 0 < B v)
    (hsteps : ∀ s ∈ Clift109.selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (h58 : B 58 = 2 ^ 58 - 1) (h109 : B 109 = 2 ^ 109 - 1) :
    ∃ k : Fin 8, ∃ l : Fin 44,
      B 51 = (2 ^ 51 - 1) * 2 ^ (k : ℕ) ∧
      B 7 = (2 ^ 7 - 1) * 2 ^ (l : ℕ) ∧
      (((k : ℕ) + a 58 = 7 ∧ (l : ℕ) + b 58 = 0) ∨
       ((k : ℕ) + a 58 = 0 ∧ (l : ℕ) + b 58 = 51)) ∧
      ((a 109 = 51 ∧ (k : ℕ) + b 109 = 0) ∨
       (a 109 = 0 ∧ (k : ℕ) + b 109 = 58)) := by
  have s15 := hsteps (8, 7) (by decide)
  have s23 := hsteps (15, 8) (by decide)
  have s28 := hsteps (23, 5) (by decide)
  have s51 := hsteps (28, 23) (by decide)
  have s58 := hsteps (51, 7) (by decide)
  have s109 := hsteps (58, 51) (by decide)
  norm_num only at s15 s23 s28 s51 s58 s109
  have lower (v e : ℕ) : B v ≤ B v * 2 ^ e :=
    Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have p8 := Nat.mul_pos (hpos 8 (by decide)) (Nat.two_pow_pos (a 15))
  have p5 := Nat.mul_pos (hpos 5 (by decide)) (Nat.two_pow_pos (b 28))
  have p7 := Nat.mul_pos (hpos 7 (by decide)) (Nat.two_pow_pos (b 58))
  have half : 2 * B 7 < B 51 := by
    have := lower 7 (b 15)
    have := lower 15 (a 23)
    have := lower 23 (a 28)
    have := lower 28 (a 51)
    have := lower 23 (b 51)
    omega
  have small51 : B 51 < 2 ^ 58 - 1 := by
    have := lower 51 (a 58)
    omega
  have e109 : B 51 * 2 ^ b 109 + (2 ^ 58 - 1) * 2 ^ a 109 =
      2 ^ (51 + 58) - 1 := by simpa [h58, h109, Nat.add_comm] using s109
  obtain ⟨k, hk⟩ := small_mersenne_complement (by decide) (by decide) small51 e109
  have e58 : B 7 * 2 ^ b 58 + (2 ^ 51 - 1) * 2 ^ (k + a 58) =
      2 ^ (7 + 51) - 1 := by
    simpa [hk, h58, pow_add, Nat.mul_assoc, Nat.add_comm] using s58
  obtain ⟨l, hl⟩ := half_mersenne_complement (by decide) (by decide)
    (show 2 * B 7 < 2 ^ (7 + 51) - 1 by omega) e58
  have bk : k < 8 := by
    by_contra hn
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 8 ≤ k by omega)
    norm_num at he hk small51
    omega
  have orient58 : (k + a 58 = 7 ∧ l + b 58 = 0) ∨
      (k + a 58 = 0 ∧ l + b 58 = 51) := by
    have he : (2 ^ 51 - 1) * 2 ^ (k + a 58) +
        (2 ^ 7 - 1) * 2 ^ (l + b 58) = (2 ^ (51 + 7) - 1) * 2 ^ 0 := by
      simpa [hk, hl, h58, pow_add, Nat.mul_assoc] using s58
    simpa using Clift109.mersenne_sum_shifts (by decide) (by decide) _ _ 0 he
  have bl : l < 44 := by
    rcases orient58 with ho | ho
    · omega
    · have kz : k = 0 := by omega
      simp only [kz, pow_zero, Nat.mul_one] at hk
      by_contra hn
      have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 44 ≤ l by omega)
      norm_num at he hl hk
      omega
  refine ⟨⟨k, bk⟩, ⟨l, bl⟩, hk, hl, orient58, ?_⟩
  have he : (2 ^ 58 - 1) * 2 ^ a 109 +
      (2 ^ 51 - 1) * 2 ^ (k + b 109) = (2 ^ (58 + 51) - 1) * 2 ^ 0 := by
    simpa [hk, h58, h109, pow_add, Nat.mul_assoc] using s109
  simpa using Clift109.mersenne_sum_shifts (by decide) (by decide) _ _ 0 he

/-- If instead B51 is fixed, the terminal equation has this complete local
109-shape domain for B58: 52 shifted blocks and 57 separated-interval forms.
This is a local iff; graph compatibility and the doubling budget remain open. -/
theorem Clift109.fixed51_terminal_domain (u : ℕ) :
    (∃ a b, u * 2 ^ a + (2 ^ 51 - 1) * 2 ^ b = 2 ^ 109 - 1) ↔
    (∃ k : Fin 52, u = (2 ^ 58 - 1) * 2 ^ (k : ℕ)) ∨
    (∃ b : Fin 58, 0 < (b : ℕ) ∧
      u = (2 ^ (58 - (b : ℕ)) - 1) * 2 ^ (51 + (b : ℕ)) + (2 ^ (b : ℕ) - 1)) :=
  mersenne_complement_domain (by decide) (by decide)

end ScholzBrauer
