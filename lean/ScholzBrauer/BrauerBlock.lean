import ScholzBrauer.Certificate

/-! One constructive Brauer step: double the current endpoint `b` times, then
add the stored value `2^b - 1`. All operations use the existing replay checker. -/
namespace ScholzBrauer

/-- Explicit summand-value certificate for `k` successive doublings. -/
def doublingSteps (a : ℕ) : ℕ → List Step
  | 0 => []
  | k + 1 => (a, a) :: doublingSteps (a + a) k

@[simp] theorem doublingSteps_length (a k : ℕ) : (doublingSteps a k).length = k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [doublingSteps, ih]

/-- Extract membership and the maximum property from the upstream chain API. -/
theorem endpoint_properties {c : List ℕ} {a : ℕ}
    (hc : IsAdditionChain c) (hlast : c.getLast? = some a) :
    a ∈ c ∧ ∀ x ∈ c, x ≤ a := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  refine ⟨by simp, ?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact le_of_lt ((List.pairwise_append.mp hc.2.1).2.2 x hx a (by simp))
  · simpa using le_of_eq (List.mem_singleton.mp hx)

/-- Doubling replay succeeds, preserves every stored value, and has the exact endpoint.
The exact number of added entries follows separately from `replayFrom_length`. -/
theorem doublingSteps_replay {c : List ℕ} {a : ℕ}
    (hc : IsAdditionChain c) (hlast : c.getLast? = some a) (k : ℕ) :
    ∃ d, replayFrom c (doublingSteps a k) = some d ∧
      IsAdditionChain d ∧ d.getLast? = some (2 ^ k * a) ∧ c ⊆ d := by
  induction k generalizing c a with
  | zero => exact ⟨c, rfl, hc, by simpa using hlast, List.Subset.refl c⟩
  | succ k ih =>
    obtain ⟨ha, hmax⟩ := endpoint_properties hc hlast
    have hpos := hc.one_le_of_mem ha
    have hgt : ∀ x ∈ c, x < a + a := by
      intro x hx
      have := hmax x hx
      omega
    have he : extend c (a, a) = some (c ++ [a + a]) := by
      exact if_pos ⟨ha, ha, hgt⟩
    obtain ⟨d, hd, hdc, hdl, hsub⟩ :=
      ih (append_sum hc ha ha hgt) (by simp : (c ++ [a + a]).getLast? = some (a + a))
    refine ⟨d, ?_, hdc, ?_, ?_⟩
    · simpa [doublingSteps, replayFrom, he] using hd
    · simpa [pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_two, Nat.add_mul] using hdl
    · exact (fun x hx => hsub (List.mem_append_left _ hx))

/-- Replay of concatenated certificates is composition of partial replays. -/
theorem replayFrom_append (c : List ℕ) (ss ts : List Step) :
    replayFrom c (ss ++ ts) = (replayFrom c ss).bind (fun d => replayFrom d ts) := by
  induction ss generalizing c with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.cons_append, replayFrom]
    cases he : extend c s <;> simp [ih]

/-- One star-source step `a -> a+b`, represented by explicit summand pairs. -/
def brauerBlock (a b : ℕ) : List Step :=
  doublingSteps (2 ^ a - 1) b ++ [(2 ^ b * (2 ^ a - 1), 2 ^ b - 1)]

@[simp] theorem brauerBlock_length (a b : ℕ) : (brauerBlock a b).length = b + 1 := by
  simp [brauerBlock]

/-- Natural-number subtraction is exact here because both powers are positive. -/
theorem mersenne_block_identity (a b : ℕ) :
    2 ^ b * (2 ^ a - 1) + (2 ^ b - 1) = 2 ^ (a + b) - 1 := by
  have hpa := Nat.one_le_pow a 2 (by decide)
  have hpb := Nat.one_le_pow b 2 (by decide)
  have hmul := Nat.le_mul_of_pos_right (2 ^ b) (by omega : 0 < 2 ^ a)
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_add, Nat.mul_comm (2 ^ a)]
  omega

/-- A checked lift block preserves the old chain, ends at `2^(a+b)-1`, and adds
exactly `b+1` entries. The stored Mersenne value is an explicit hypothesis;
its availability in successive blocks remains the general star-lift invariant. -/
theorem brauerBlock_replay {c : List ℕ} {a b : ℕ}
    (hc : IsAdditionChain c) (hlast : c.getLast? = some (2 ^ a - 1))
    (hb : 2 ^ b - 1 ∈ c) :
    ∃ d, replayFrom c (brauerBlock a b) = some d ∧
      IsAdditionChain d ∧ d.getLast? = some (2 ^ (a + b) - 1) ∧
      d.length = c.length + (b + 1) ∧ c ⊆ d := by
  obtain ⟨e, he, hec, helast, hsub⟩ := doublingSteps_replay hc hlast b
  obtain ⟨hea, hemax⟩ := endpoint_properties hec helast
  have heb : 2 ^ b - 1 ∈ e := hsub hb
  have hbpos := hec.one_le_of_mem heb
  have hgt : ∀ x ∈ e, x < 2 ^ b * (2 ^ a - 1) + (2 ^ b - 1) := by
    intro x hx
    have := hemax x hx
    omega
  let d := e ++ [2 ^ b * (2 ^ a - 1) + (2 ^ b - 1)]
  have hext : extend e (2 ^ b * (2 ^ a - 1), 2 ^ b - 1) = some d := by
    exact if_pos ⟨hea, heb, hgt⟩
  have hd : replayFrom c (brauerBlock a b) = some d := by
    simp [brauerBlock, replayFrom_append, he, replayFrom, hext]
  refine ⟨d, hd, append_sum hec hea heb hgt, ?_, ?_, ?_⟩
  · simp [d, mersenne_block_identity]
  · simpa using replayFrom_length hd
  · exact fun x hx => List.mem_append_left _ (hsub hx)

/-- The block gives a conditional numerical upper bound without assuming optimality. -/
theorem brauerBlock_upper_bound {c : List ℕ} {a b r : ℕ}
    (hc : IsAdditionChain c) (hlast : c.getLast? = some (2 ^ a - 1))
    (hb : 2 ^ b - 1 ∈ c) (hlen : c.length = r + 1) :
    additionChainLength (2 ^ (a + b) - 1) ≤ r + b + 1 := by
  obtain ⟨d, _, hdc, hdl, hdlen, _⟩ := brauerBlock_replay hc hlast hb
  exact additionChainLength_le d hdc hdl (by omega)

-- Kernel-evaluated examples cover a zero-length doubling block, a first lift,
-- a stored value different from the endpoint, and a missing stored value.
example : replayFrom [1] (doublingSteps 1 0) = some [1] := by decide
example : replayFrom [1] (brauerBlock 1 1) = some [1, 2, 3] := by decide
example : replayFrom [1, 2, 3] (brauerBlock 2 1) = some [1, 2, 3, 6, 7] := by decide
example : replayFrom [1] (brauerBlock 1 2) = none := by decide
example : replayFrom [1] (brauerBlock 1 0) = none := by decide

end ScholzBrauer
