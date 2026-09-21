import ScholzBrauer.BrauerBlock

/-! A star source is encoded by its increments: from endpoint `a`, the next
increment `b` must already occur in the source prefix. Composing the explicit
Brauer blocks retains every stored Mersenne value and telescopes the count.
No minimum-length assumption is needed for certificate correctness. -/
namespace ScholzBrauer

/-- Check each increment against the source prefix available at that step. -/
def IsStarFrom (source : List ℕ) (a : ℕ) : List ℕ → Prop
  | [] => True
  | b :: bs => b ∈ source ∧ IsStarFrom (source ++ [a + b]) (a + b) bs

instance (source : List ℕ) (a : ℕ) (bs : List ℕ) :
    Decidable (IsStarFrom source a bs) := by
  induction bs generalizing source a with
  | nil => exact isTrue True.intro
  | cons b bs ih =>
    unfold IsStarFrom
    have := ih (source ++ [a + b]) (a + b)
    infer_instance

/-- Source values obtained by successively adding the increments. -/
def starSourceFrom (source : List ℕ) (a : ℕ) : List ℕ → List ℕ
  | [] => source
  | b :: bs => starSourceFrom (source ++ [a + b]) (a + b) bs

/-- Explicit summand-value certificate; correctness requires `IsStarFrom`. -/
def starCertificateFrom (a : ℕ) : List ℕ → List Step
  | [] => []
  | b :: bs => brauerBlock a b ++ starCertificateFrom (a + b) bs

theorem starSourceFrom_length (source : List ℕ) (a : ℕ) (bs : List ℕ) :
    (starSourceFrom source a bs).length = source.length + bs.length := by
  induction bs generalizing source a with
  | nil => simp [starSourceFrom]
  | cons b bs ih =>
    simp only [starSourceFrom, ih, List.length_append, List.length_cons, List.length_nil]
    omega

theorem starSourceFrom_endpoint {source : List ℕ} {a : ℕ}
    (hlast : source.getLast? = some a) (bs : List ℕ) :
    (starSourceFrom source a bs).getLast? = some (a + bs.sum) := by
  induction bs generalizing source a with
  | nil => simpa [starSourceFrom] using hlast
  | cons b bs ih =>
    simpa [starSourceFrom, Nat.add_assoc] using
      ih (by simp : (source ++ [a + b]).getLast? = some (a + b))

/-- The checked source really is an addition chain under the upstream API. -/
theorem starSourceFrom_valid {source : List ℕ} {a : ℕ} {bs : List ℕ}
    (hs : IsAdditionChain source) (hlast : source.getLast? = some a)
    (hstar : IsStarFrom source a bs) :
    IsAdditionChain (starSourceFrom source a bs) := by
  induction bs generalizing source a with
  | nil => exact hs
  | cons b bs ih =>
    obtain ⟨hb, hrest⟩ := hstar
    obtain ⟨ha, hmax⟩ := endpoint_properties hs hlast
    have hbpos := hs.one_le_of_mem hb
    have hgt : ∀ x ∈ source, x < a + b := by
      intro x hx
      have := hmax x hx
      omega
    exact ih (append_sum hs ha hb hgt) (by simp) hrest

/-- Sum of block lengths, before specialising the initial exponent to one. -/
theorem starCertificateFrom_length (a : ℕ) (bs : List ℕ) :
    (starCertificateFrom a bs).length = bs.sum + bs.length := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [starCertificateFrom, List.length_append, brauerBlock_length,
      ih, List.sum_cons, List.length_cons]
    omega

/-- Whole-source replay invariant: every previous source Mersenne value remains
available. Each recursive call uses the proved block and replay composition. -/
theorem starCertificateFrom_replay {source c : List ℕ} {a : ℕ} {bs : List ℕ}
    (hstar : IsStarFrom source a bs) (hc : IsAdditionChain c)
    (hlast : c.getLast? = some (2 ^ a - 1))
    (hstored : ∀ x ∈ source, 2 ^ x - 1 ∈ c) :
    ∃ d, replayFrom c (starCertificateFrom a bs) = some d ∧
      IsAdditionChain d ∧ d.getLast? = some (2 ^ (a + bs.sum) - 1) ∧
      d.length = c.length + (bs.sum + bs.length) ∧ c ⊆ d ∧
      ∀ x ∈ starSourceFrom source a bs, 2 ^ x - 1 ∈ d := by
  induction bs generalizing source c a with
  | nil =>
    exact ⟨c, rfl, hc, by simpa using hlast, by simp,
      List.Subset.refl c, hstored⟩
  | cons b bs ih =>
    obtain ⟨hb, hrest⟩ := hstar
    obtain ⟨e, he, hec, helast, helen, hesub⟩ :=
      brauerBlock_replay hc hlast (hstored b hb)
    have hstore : ∀ x ∈ source ++ [a + b], 2 ^ x - 1 ∈ e := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hesub (hstored x hx)
      · have hx' := List.mem_singleton.mp hx
        subst x
        exact (endpoint_properties hec helast).1
    obtain ⟨d, hd, hdc, hdlast, hdlen, hdsub, hdstore⟩ :=
      ih hrest hec helast hstore
    refine ⟨d, ?_, hdc, ?_, ?_, fun x hx => hdsub (hesub hx), hdstore⟩
    · simpa [starCertificateFrom, replayFrom_append, he] using hd
    · simpa [List.sum_cons, Nat.add_assoc] using hdlast
    · simp only [List.sum_cons, List.length_cons]
      omega

/-- Starting at `[1]`, a checked `r`-step source ending at `n` produces a
certificate with exactly `n-1+r` additions, including the empty source-step list. -/
theorem starLift_certificate {bs : List ℕ} {n : ℕ}
    (hstar : IsStarFrom [1] 1 bs) (hn : 1 + bs.sum = n) :
    ∃ d, replay (starCertificateFrom 1 bs) = some d ∧
      IsAdditionChain d ∧ d.getLast? = some (2 ^ n - 1) ∧
      d.length = (n - 1 + bs.length) + 1 ∧
      (starCertificateFrom 1 bs).length = n - 1 + bs.length ∧
      ∀ x ∈ starSourceFrom [1] 1 bs, 2 ^ x - 1 ∈ d := by
  obtain ⟨d, hd, hdc, hdlast, hdlen, _, hdstore⟩ :=
    starCertificateFrom_replay hstar (by decide : IsAdditionChain [1])
      (by decide) (by simp)
  refine ⟨d, hd, hdc, by simpa [hn] using hdlast, ?_, ?_, hdstore⟩
  · simp only [List.length_singleton] at hdlen
    omega
  · rw [starCertificateFrom_length]
    omega

/-- General Brauer witness bound. The source need not be optimal. -/
theorem starLift_upper_bound {bs : List ℕ} {n : ℕ}
    (hstar : IsStarFrom [1] 1 bs) (hn : 1 + bs.sum = n) :
    additionChainLength (2 ^ n - 1) ≤ n - 1 + bs.length := by
  obtain ⟨d, _, hdc, hdlast, hdlen, _, _⟩ := starLift_certificate hstar hn
  exact additionChainLength_le d hdc hdlast hdlen

/-- Scholz follows for a checked star source whose length is minimum.
Optimality is an explicit hypothesis, not a claim about every exponent. -/
theorem scholz_of_optimal_star {bs : List ℕ} {n : ℕ}
    (hstar : IsStarFrom [1] 1 bs) (hn : 1 + bs.sum = n)
    (hoptimal : bs.length = additionChainLength n) :
    additionChainLength (2 ^ n - 1) ≤ n - 1 + additionChainLength n := by
  simpa [hoptimal] using starLift_upper_bound hstar hn

-- Singleton source, first block, use of an older value, and invalid increments.
example : IsStarFrom [1] 1 [] := by decide
example : replay (starCertificateFrom 1 []) = some [1] := by decide
example : additionChainLength (2 ^ 1 - 1) ≤ 0 :=
  starLift_upper_bound (bs := []) (by decide) (by decide)
example : replay (starCertificateFrom 1 [1, 1]) = some [1, 2, 3, 6, 7] := by decide
example : ¬ IsStarFrom [1] 1 [0] := by decide
example : ¬ IsStarFrom [1] 1 [2] := by decide
example : ¬ IsStarFrom [1] 1 [1, 3] := by decide

end ScholzBrauer
