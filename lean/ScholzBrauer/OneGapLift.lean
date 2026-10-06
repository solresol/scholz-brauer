import ScholzBrauer.NonHansen29
import ScholzBrauer.HansenLift
import ScholzBrauer.Exclusion

/-! A parametric one-gap repair of the non-Hansen example at 29.
We insert two values inside a doubling run, then resume from a stored value.
Strict replay order replaces the need for a new sorted-allocation interface.
No source optimality or universal non-Hansen classification is assumed. -/
namespace ScholzBrauer.OneGapLift

/-- Resume doubling a stored value after inserting other nodes. The first new
sum must exceed the current chain; subsequent doublings use the ordinary API. -/
theorem resume_doubling {c : List ℕ} {x : ℕ} (hc : IsAdditionChain c)
    (hx : x ∈ c) (hgt : ∀ y ∈ c, y < x + x) (k : ℕ) :
    ∃ d, IsAdditionChain d ∧ d.getLast? = some (2 ^ (k + 1) * x) ∧
      d.length = c.length + (k + 1) ∧ c ⊆ d ∧ x + x ∈ d := by
  have he := append_sum hc hx hx hgt
  obtain ⟨d, hr, hd, hl, hs⟩ := doublingSteps_replay he
    (by simp : (c ++ [x + x]).getLast? = some (x + x)) k
  have hlen := replayFrom_length hr
  refine ⟨d, hd, ?_, ?_, fun y hy => hs (List.mem_append_left _ hy), hs (by simp)⟩
  · simpa [pow_succ, Nat.mul_assoc, Nat.mul_two, Nat.mul_add, Nat.add_mul] using hl
  · simp only [List.length_append, List.length_singleton, doublingSteps_length] at hlen
    omega

/-- Mersenne spine for the powers-of-two source, retaining the first doubling
of every earlier base. This is exactly the summand the repair will need. -/
theorem spine_chain (a : ℕ) :
    ∃ c, IsAdditionChain c ∧ c.getLast? = some (2 ^ (2 ^ a) - 1) ∧
      c.length = 2 ^ a + a ∧
      ∀ b < a, 2 * (2 ^ (2 ^ b) - 1) ∈ c := by
  induction a with
  | zero => exact ⟨[1], by decide, by decide, by decide, by omega⟩
  | succ a ih =>
    obtain ⟨c, hc, hl, hlen, hstored⟩ := ih
    obtain ⟨hm, hmax⟩ := endpoint_properties hc hl
    have hp := hc.one_le_of_mem hm
    have hA : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by decide)
    obtain ⟨d, hd, hdl, hdlen, hsub, hdouble⟩ := resume_doubling hc hm
      (by intro y hy; have := hmax y hy; omega) (2 ^ a - 1)
    have hcancel : 2 ^ a - 1 + 1 = 2 ^ a := by omega
    rw [hcancel] at hdl
    obtain ⟨hx, hdmax⟩ := endpoint_properties hd hdl
    have hm' := hsub hm
    have hgt : ∀ y ∈ d, y < 2 ^ (2 ^ a) * (2 ^ (2 ^ a) - 1) + (2 ^ (2 ^ a) - 1) := by
      intro y hy; have := hdmax y hy; omega
    refine ⟨d ++ [2 ^ (2 ^ a) * (2 ^ (2 ^ a) - 1) + (2 ^ (2 ^ a) - 1)],
      append_sum hd hx hm' hgt, ?_, ?_, ?_⟩
    · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        mersenne_block_identity]
      rw [pow_succ, Nat.mul_two]
    · simp only [List.length_append, List.length_singleton, pow_succ, Nat.mul_two]
      omega
    · intro b hb
      by_cases he : b = a
      · subst b
        exact List.mem_append_left _ (by simpa [Nat.two_mul] using hdouble)
      · exact List.mem_append_left _ (hsub (hstored b (by omega)))

/-- The two inserted values fit strictly between consecutive doublings. -/
theorem repair_window (A B : ℕ) (hA : 2 ≤ A) (hB : 1 ≤ B) :
    let x := 2 ^ (B + 1) * (2 ^ A - 1)
    x < x + 1 ∧ x + 1 < 2 ^ (A + B + 1) - 1 ∧
      2 ^ (A + B + 1) - 1 < x + x := by
  dsimp
  have hpB : 2 ≤ 2 ^ B := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hB
  have hpA : 4 ≤ 2 ^ A := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hA
  have hid := NonHansen29.one_gap_repair_identity A B
  have hlarge : 2 ^ (B + 1) ≤ 2 ^ (B + 1) * (2 ^ A - 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpow : 2 ^ (B + 1) = 2 * 2 ^ B := by simp [pow_succ, Nat.mul_comm]
  omega

/-- A repaired block from any suitable prefix. It supplies all required sums,
strict order, the endpoint, preservation and the exact number of additions. -/
theorem repair_chain {c : List ℕ} {A B : ℕ} (hc : IsAdditionChain c)
    (hl : c.getLast? = some (2 ^ A - 1)) (hB : 1 ≤ B) (hgap : B + 2 ≤ A)
    (hstored : 2 * (2 ^ B - 1) ∈ c) :
    ∃ d, IsAdditionChain d ∧ d.getLast? = some (2 ^ (3 * A + B + 1) - 1) ∧
      d.length = c.length + (2 * A + B + 5) ∧ c ⊆ d := by
  obtain ⟨hm, _⟩ := endpoint_properties hc hl
  have hpos := hc.one_le_of_mem hm
  have hone : 1 ∈ c := List.mem_of_head? hc.1
  obtain ⟨e, hr, he, hel, hesub⟩ := doublingSteps_replay hc hl (B + 1)
  have helen := replayFrom_length hr
  simp only [doublingSteps_length] at helen
  let x := 2 ^ (B + 1) * (2 ^ A - 1)
  change e.getLast? = some x at hel
  obtain ⟨hx, hmax⟩ := endpoint_properties he hel
  obtain ⟨hwin1, hwin2, hwin3⟩ := repair_window A B (by omega) hB
  change x < x + 1 at hwin1
  change x + 1 < 2 ^ (A + B + 1) - 1 at hwin2
  change 2 ^ (A + B + 1) - 1 < x + x at hwin3
  have hfirst := append_sum he hx (hesub hone)
    (by intro y hy; have := hmax y hy; omega)
  let f := e ++ [x + 1]
  change IsAdditionChain f at hfirst
  have hfsub : e ⊆ f := fun y hy => List.mem_append_left _ hy
  have hsecond : IsAdditionChain (f ++ [2 ^ (A + B + 1) - 1]) := by
    have hsum := NonHansen29.one_gap_repair_identity A B
    change (x + 1) + 2 * (2 ^ B - 1) = _ at hsum
    rw [← hsum]
    apply append_sum hfirst (by simp [f]) (hfsub (hesub hstored))
    intro y hy
    have := (endpoint_properties hfirst (a := x + 1) (by simp [f])).2 y hy
    omega
  let g := f ++ [2 ^ (A + B + 1) - 1]
  change IsAdditionChain g at hsecond
  have hgsub : e ⊆ g := fun y hy => List.mem_append_left _ (hfsub hy)
  obtain ⟨j, hj, hjl, hjlen, hjsub, _⟩ := resume_doubling hsecond (hgsub hx)
    (by intro y hy; have := (endpoint_properties hsecond (a := 2 ^ (A + B + 1) - 1) (by simp [g])).2 y hy; omega)
    (A - (B + 2))
  have hexp : (A - (B + 2) + 1) + (B + 1) = A := by omega
  have hxend : 2 ^ (A - (B + 2) + 1) * x = 2 ^ A * (2 ^ A - 1) := by
    dsimp [x]
    rw [← Nat.mul_assoc, ← pow_add, hexp]
  rw [hxend] at hjl
  obtain ⟨hjm, hjmax⟩ := endpoint_properties hj hjl
  have hcj : c ⊆ j := fun y hy => hjsub (hgsub (hesub hy))
  have hk := append_sum hj hjm (hcj hm)
    (by intro y hy; have := hjmax y hy; omega)
  let k := j ++ [2 ^ A * (2 ^ A - 1) + (2 ^ A - 1)]
  change IsAdditionChain k at hk
  have hkl : k.getLast? = some (2 ^ (A + A) - 1) := by
    simp [k, mersenne_block_identity]
  have hkd : 2 ^ (A + B + 1) - 1 ∈ k :=
    List.mem_append_left _ (hjsub (by simp [g]))
  obtain ⟨d, _, hd, hdl, hdlen, hdsub⟩ := brauerBlock_replay hk hkl hkd
  refine ⟨d, hd, ?_, ?_, fun y hy => hdsub (List.mem_append_left _ (hcj hy))⟩
  · have heq : A + A + (A + B + 1) = 3 * A + B + 1 := by omega
    simpa only [heq] using hdl
  · simp only [k, g, f, List.length_append, List.length_singleton] at hdlen hjlen
    omega

/-- The repair is not restricted to powers-of-two prefixes. Any accepted
Hansen allocation containing the doubled B-base supplies the same four-step
extension, with an exact count. The labelled membership is an explicit hypothesis. -/
theorem hansen_prefix_repair_certificate {steps : List MarkedStep} {A B : ℕ}
    (h : IsHansenFrom [1] 1 steps) (hA : hansenAnchorFrom 1 steps = A)
    (hB : 1 ≤ B) (hgap : B + 2 ≤ A) (hlabel : (B, 1) ∈ hansenLabels 1 steps) :
    let n := 3 * A + B + 1
    ∃ cert c, replay cert = some c ∧ c.getLast? = some (2 ^ n - 1) ∧
      cert.length = n - 1 + (steps.length + 4) := by
  obtain ⟨hc, hl, hlen⟩ := hansenLift_chain h hA
  have hstored : 2 * (2 ^ B - 1) ∈ hansenLift steps :=
    mem_hansenLift.mpr ⟨(B, 1), hlabel, by simp [shiftedMersenne]⟩
  obtain ⟨d, hd, hdl, hdlen, _⟩ := repair_chain hc hl hB hgap hstored
  obtain ⟨cert, hr, hcert⟩ := additionChain_exists_replay hd
  exact ⟨cert, d, hr, hdl, by dsimp; omega⟩

/-- Full infinite family: n = 3*2^a + 2^b + 1, 1 ≤ b < a. The certificate
has exactly n-1+(a+4) steps. Its source need not be optimal or non-Hansen. -/
theorem family_certificate (a b : ℕ) (hb : 1 ≤ b) (hba : b < a) :
    let n := 3 * 2 ^ a + 2 ^ b + 1
    ∃ cert c, replay cert = some c ∧ c.getLast? = some (2 ^ n - 1) ∧
      cert.length = n - 1 + (a + 4) := by
  dsimp
  obtain ⟨c, hc, hl, hlen, hs⟩ := spine_chain a
  have hB : 2 ≤ 2 ^ b := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have hAB : 2 * 2 ^ b ≤ 2 ^ a := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show b + 1 ≤ a by omega)
    simpa [pow_succ, Nat.mul_comm] using this
  obtain ⟨d, hd, hdl, hdlen, _⟩ := repair_chain hc hl (by omega) (by omega) (hs b hba)
  obtain ⟨cert, hr, hcert⟩ := additionChain_exists_replay hd
  exact ⟨cert, d, hr, hdl, by omega⟩

theorem family_upper_bound (a b : ℕ) (hb : 1 ≤ b) (hba : b < a) :
    let n := 3 * 2 ^ a + 2 ^ b + 1
    additionChainLength (2 ^ n - 1) ≤ n - 1 + (a + 4) := by
  obtain ⟨cert, c, hr, hl, hlen⟩ := family_certificate a b hb hba
  simpa [hlen] using replay_upper_bound hr hl

/-- The actual source family, with a powers-of-two prefix. -/
def powerSource : ℕ → List ℕ
  | 0 => [1]
  | a + 1 => powerSource a ++ [2 ^ (a + 1)]

def familySource (a b : ℕ) : List ℕ :=
  powerSource a ++ [2 ^ a + 1, 2 ^ a + 2 ^ b + 1, 2 * 2 ^ a,
    3 * 2 ^ a + 2 ^ b + 1]

theorem powerSource_properties (a : ℕ) :
    IsAdditionChain (powerSource a) ∧ (powerSource a).getLast? = some (2 ^ a) ∧
      (powerSource a).length = a + 1 ∧
      ∀ x, x ∈ powerSource a ↔ ∃ i ≤ a, x = 2 ^ i := by
  induction a with
  | zero => simp [powerSource, show IsAdditionChain [1] by decide]
  | succ a ih =>
    obtain ⟨hc, hl, hlen, hmem⟩ := ih
    obtain ⟨ha, hmax⟩ := endpoint_properties hc hl
    have hp := Nat.two_pow_pos a
    have he := append_sum hc ha ha (by intro y hy; have := hmax y hy; omega)
    have hpow : 2 ^ (a + 1) = 2 ^ a + 2 ^ a := by simp [pow_succ, Nat.mul_two]
    refine ⟨by simpa [powerSource, hpow] using he, by simp [powerSource],
      by simp [powerSource, hlen], ?_⟩
    intro x
    simp only [powerSource, List.mem_append, List.mem_singleton, hmem]
    constructor
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨a + 1, le_refl _, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      by_cases he : i = a + 1
      · exact Or.inr (by rw [he])
      · exact Or.inl ⟨i, by omega, rfl⟩

/-- The source is valid and has exactly a+4 additions. This is a witness,
not a lower bound on the source's minimum addition-chain length. -/
theorem familySource_chain (a b : ℕ) (hb : 1 ≤ b) (hba : b < a) :
    IsAdditionChain (familySource a b) ∧
      (familySource a b).getLast? = some (3 * 2 ^ a + 2 ^ b + 1) ∧
      (familySource a b).length = (a + 4) + 1 := by
  obtain ⟨hc, hl, hlen, hmem⟩ := powerSource_properties a
  obtain ⟨ha, hmax⟩ := endpoint_properties hc hl
  have hB : 2 ≤ 2 ^ b := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have hAB : 2 * 2 ^ b ≤ 2 ^ a := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show b + 1 ≤ a by omega)
    simpa [pow_succ, Nat.mul_comm] using this
  have hone : 1 ∈ powerSource a := List.mem_of_head? hc.1
  have hbmem : 2 ^ b ∈ powerSource a := (hmem _).mpr ⟨b, by omega, rfl⟩
  have h1 := append_sum hc ha hone (by intro x hx; have := hmax x hx; omega)
  have h2 := append_sum h1 (a := 2 ^ a + 1) (by simp)
    (List.mem_append_left _ hbmem) (by
      intro x hx
      have := (endpoint_properties h1 (a := 2 ^ a + 1) (by simp)).2 x hx
      omega)
  have hamem : 2 ^ a ∈ (powerSource a ++ [2 ^ a + 1]) ++ [2 ^ a + 1 + 2 ^ b] :=
    List.mem_append_left _ (List.mem_append_left _ ha)
  have h3 := append_sum h2 hamem hamem (by
    intro x hx
    have := (endpoint_properties h2 (a := 2 ^ a + 1 + 2 ^ b) (by simp)).2 x hx
    omega)
  have h4 := append_sum h3 (a := 2 ^ a + 2 ^ a) (by simp)
    (b := 2 ^ a + 1 + 2 ^ b) (by simp) (by
      intro x hx
      have := (endpoint_properties h3 (a := 2 ^ a + 2 ^ a) (by simp)).2 x hx
      omega)
  refine ⟨?_, by simp [familySource], by simp [familySource, hlen, Nat.add_assoc]⟩
  convert h4 using 1
  simp [familySource, List.append_assoc,
    Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

/-- The Scholz conclusion is conditional on this particular source being optimal. -/
theorem scholz_of_optimal_family (a b : ℕ) (hb : 1 ≤ b) (hba : b < a)
    (hopt : additionChainLength (3 * 2 ^ a + 2 ^ b + 1) = a + 4) :
    let n := 3 * 2 ^ a + 2 ^ b + 1
    additionChainLength (2 ^ n - 1) ≤ n - 1 + additionChainLength n := by
  dsimp
  rw [hopt]
  exact family_upper_bound a b hb hba

/-- Local marking obstruction after a doubling. It quantifies over all
summands, including alternative decompositions, and every continuation. -/
theorem no_marking_after_double {P : List ℕ} {H B anchor : ℕ}
    (hP : ∀ x ∈ P, x ≤ H ∧ (x = 1 ∨ x % 2 = 0))
    (hH : 4 ≤ H) (hHeven : H % 2 = 0) (hB : 2 ≤ B)
    (hBH : B ≤ H) (hBeven : B % 2 = 0)
    (m₀ m₁ m₂ m₃ : Bool) (rest : List MarkedStep) :
    ¬ IsHansenFrom P anchor
      ((2 * H, m₀) :: (2 * H + 1, m₁) :: (2 * H + B + 1, m₂) ::
        (4 * H, m₃) :: rest) := by
  intro h
  obtain ⟨ha, ⟨u, hu, heq⟩, _, hnext⟩ := h
  have haH := (hP anchor ha).1
  have huH := (hP u hu).1
  have hanchor : anchor = H := by omega
  subst anchor
  cases m₀ with
  | false =>
    obtain ⟨_, ⟨v, hv, he⟩, _, _⟩ := hnext
    simp only [Bool.false_eq_true, ↓reduceIte] at he
    rcases List.mem_append.mp hv with hv | hv
    · rcases (hP v hv).2 with he1 | heven <;> omega
    · have := List.mem_singleton.mp hv; omega
  | true =>
    obtain ⟨_, _, _, hnext⟩ := hnext
    cases m₁ with
    | false =>
      obtain ⟨_, ⟨v, hv, he⟩, _, _⟩ := hnext
      simp only [Bool.false_eq_true, ↓reduceIte] at he
      simp only [List.mem_append, List.mem_singleton] at hv
      rcases hv with (hv | hv) | hv
      · rcases (hP v hv).2 with he1 | heven <;> omega
      · omega
      · omega
    | true =>
      obtain ⟨_, _, _, hnext⟩ := hnext
      cases m₂ <;>
        obtain ⟨_, ⟨v, hv, he⟩, _, _⟩ := hnext <;>
        simp only [Bool.false_eq_true, ↓reduceIte] at he <;>
        simp only [List.mem_append, List.mem_singleton] at hv <;>
        rcases hv with ((hv | hv) | hv) | hv
      all_goals try omega
      all_goals rcases (hP v hv).2 with he1 | heven <;> omega

/-- Arbitrary marks on the powers-of-two prefix. -/
def powerMarks (f : ℕ → Bool) : ℕ → List MarkedStep
  | 0 => []
  | a + 1 => powerMarks f a ++ [(2 ^ (a + 1), f a)]

private theorem sourceFrom_append (P : List ℕ) (pre tail : List MarkedStep) :
    hansenSourceFrom P (pre ++ tail) = hansenSourceFrom (hansenSourceFrom P pre) tail := by
  induction pre generalizing P with
  | nil => rfl
  | cons s pre ih => exact ih (P ++ [s.1])

theorem powerMarks_source (f : ℕ → Bool) (a : ℕ) :
    hansenSourceFrom [1] (powerMarks f a) = powerSource a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [powerMarks, sourceFrom_append, hansenSourceFrom, ih, powerSource]

theorem family_marked_source (a b : ℕ) (f : ℕ → Bool) (m₁ m₂ m₃ m₄ : Bool) :
    hansenSourceFrom [1] (powerMarks f a ++
      [(2 ^ a + 1, m₁), (2 ^ a + 2 ^ b + 1, m₂),
       (2 * 2 ^ a, m₃), (3 * 2 ^ a + 2 ^ b + 1, m₄)]) = familySource a b := by
  simp [sourceFrom_append, powerMarks_source, hansenSourceFrom, familySource,
    List.append_assoc]

/-- Apart from the smallest boundary member, every proposed source is
non-Hansen: no Boolean assignment can satisfy the existing marking predicate. -/
theorem family_not_hansen (a b : ℕ) (ha : 3 ≤ a) (hb : 1 ≤ b) (hba : b < a)
    (f : ℕ → Bool) (m₁ m₂ m₃ m₄ : Bool) :
    ¬ IsHansenFrom [1] 1 (powerMarks f a ++
      [(2 ^ a + 1, m₁), (2 ^ a + 2 ^ b + 1, m₂),
       (2 * 2 ^ a, m₃), (3 * 2 ^ a + 2 ^ b + 1, m₄)]) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show a ≠ 0 by omega)
  intro h
  rw [powerMarks, List.append_assoc] at h
  obtain ⟨hcut, _⟩ := hansenFrom_split (powerMarks f p) _ (by simp : 1 ∈ ([1] : List ℕ)) h
  rw [powerMarks_source] at hcut
  have hH : 4 ≤ 2 ^ p := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ p by omega)
  have even_pow (i : ℕ) (hi : 1 ≤ i) : (2 ^ i) % 2 = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
    simp [pow_succ]
  have hP : ∀ x ∈ powerSource p, x ≤ 2 ^ p ∧ (x = 1 ∨ x % 2 = 0) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := ((powerSource_properties p).2.2.2 x).mp hx
    refine ⟨Nat.pow_le_pow_right (by decide) hi, ?_⟩
    by_cases hz : i = 0
    · left; simp [hz]
    · right; exact even_pow i (by omega)
  have hB : 2 ≤ 2 ^ b := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have hBH : 2 ^ b ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
  have hbad := no_marking_after_double (anchor := hansenAnchorFrom 1 (powerMarks f p)) hP hH (even_pow p (by omega)) hB hBH
    (even_pow b hb) (f p) m₁ m₂ m₃ [(3 * 2 ^ (p + 1) + 2 ^ b + 1, m₄)]
  apply hbad
  simpa only [pow_succ, Nat.mul_comm (2 ^ p) 2, ← Nat.mul_assoc,
    Nat.reduceMul, List.singleton_append] using hcut

/-- The smallest proposed member is Hansen, so the unrestricted claim that
all family sources are non-Hansen is false. No optimum is asserted here. -/
theorem boundary_is_hansen : IsHansenFrom [1] 1
    [(2, true), (4, true), (5, true), (7, true), (8, false), (15, true)] := by
  decide +kernel

/-- The existing exact exclusion format, generated at target 29/limit 6.
Every occurrence is kernel checked in its own source prefix. -/
def exclusion29 : Array ExclusionNode :=
  #[.gap,
    .split [(16, 0)],
    .split [(8, 1)],
    .split [(15, 0), (20, 0)],
    .split [(8, 1), (10, 3)],
    .split [(15, 0), (18, 0)],
    .split [(15, 0), (18, 0), (24, 0)],
    .split [(8, 1), (9, 5), (12, 6)],
    .split [(4, 2), (5, 4), (6, 7)],
    .split [(18, 0)],
    .split [(8, 1), (9, 9), (10, 3)],
    .split [(16, 0), (20, 0)],
    .split [(16, 0), (18, 0), (24, 0)],
    .split [(8, 1), (10, 11), (12, 12)],
    .split [(16, 0), (17, 0), (18, 0)],
    .split [(16, 0), (18, 0), (20, 0)],
    .split [(16, 0), (20, 0), (24, 0)],
    .split [(17, 0), (18, 0), (20, 0), (24, 0)],
    .split [(9, 14), (10, 15), (12, 16), (16, 17)],
    .split [(5, 10), (6, 13), (8, 18)],
    .split [(3, 8), (4, 19)],
    .split [(2, 20)]]

theorem exclusion29_checked : checkExclusion exclusion29 29 [1] 1 6 21 = true := by
  decide +kernel

/-- Optimality of the motivating source; independent of the Mersenne lift. -/
theorem length29_eq_seven : additionChainLength 29 = 7 := by
  have hne := additionChainSteps_nonempty (n := 29) (r := 7)
    NonHansen29.source NonHansen29.source_valid (by decide) (by decide)
  have hlo := checkExclusion_lower_bound exclusion29_checked hne
  have hhi := additionChainLength_le (n := 29) (r := 7)
    NonHansen29.source NonHansen29.source_valid (by decide) (by decide)
  omega

/-- End-to-end Scholz at 29 through the new family lift and proved source optimum. -/
theorem scholz29 : additionChainLength (2 ^ 29 - 1) ≤ 29 - 1 + additionChainLength 29 := by
  exact scholz_of_optimal_family 3 2 (by decide) (by decide) length29_eq_seven

end ScholzBrauer.OneGapLift
