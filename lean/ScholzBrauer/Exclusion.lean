import ScholzBrauer.HansenLift

/-! Context-sensitive exclusion of all chains with at most a given number of
additions. Certificate nodes reuse the portable bound/gap/split syntax. Recursion
is on the remaining budget: sharing a node never shares a conclusion across
prefixes. The bridge to the upstream predicate uses its proved replay theorem. -/
namespace ScholzBrauer

/-- Reachability by at most `r` further increasing addition steps. -/
inductive ChainReach (n : ℕ) : List ℕ → ℕ → ℕ → Prop
  | stop (c : List ℕ) (r : ℕ) : ChainReach n c n r
  | step {c : List ℕ} {m r a b : ℕ} (ha : a ∈ c) (hb : b ∈ c)
      (hgt : m < a + b) (next : ChainReach n (c ++ [a + b]) (a + b) r) :
      ChainReach n c m (r + 1)

theorem ChainReach.mono {n m r k : ℕ} {c : List ℕ}
    (h : ChainReach n c m r) (hr : r ≤ k) : ChainReach n c m k := by
  induction h generalizing k with
  | stop => exact .stop _ _
  | @step c m r a b ha hb hgt hn ih =>
    cases k with
    | zero => omega
    | succ k => exact .step ha hb hgt (ih (by omega))

theorem ChainReach.endpoint_le {n m r : ℕ} {c : List ℕ}
    (h : ChainReach n c m r) : m ≤ n := by
  induction h with
  | stop => exact le_rfl
  | step _ _ hgt _ ih => omega

/-- The extension version of the upstream doubling bound. -/
theorem ChainReach.doubling_bound {n m r : ℕ} {c : List ℕ}
    (h : ChainReach n c m r) (hc : ∀ x ∈ c, x ≤ m) : n ≤ m * 2 ^ r := by
  induction h with
  | stop c r => exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos r)
  | @step c m r a b ha hb hgt hn ih =>
    have hab : a + b ≤ 2 * m := by have := hc a ha; have := hc b hb; omega
    have hnext : ∀ x ∈ c ++ [a + b], x ≤ a + b := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact le_trans (hc x hx) (Nat.le_of_lt hgt)
      · exact le_of_eq (List.mem_singleton.mp hx)
    have hi := ih hnext
    calc n ≤ (a + b) * 2 ^ r := hi
         _ ≤ (2 * m) * 2 ^ r := Nat.mul_le_mul_right _ hab
         _ = m * 2 ^ (r + 1) := by simp [pow_succ, Nat.mul_comm, Nat.mul_assoc]

/-- Successful replay reaches its endpoint using its exact number of steps. -/
theorem replayFrom_reaches {steps : List Step} {c d : List ℕ} {m n : ℕ}
    (h : replayFrom c steps = some d) (hm : c.getLast? = some m)
    (hn : d.getLast? = some n) : ChainReach n c m steps.length := by
  induction steps generalizing c m with
  | nil =>
    have he : c = d := Option.some.inj h
    have hmn : m = n := by rw [he, hn] at hm; exact (Option.some.inj hm).symm
    subst m
    exact .stop _ _
  | cons s ss ih =>
    simp only [replayFrom] at h
    unfold extend at h
    split at h
    · rename_i hs
      simp only [Option.bind_some] at h
      exact .step hs.1 hs.2.1 (hs.2.2 m (List.mem_of_getLast? hm))
        (ih h (by simp))
    · simp at h

/-- No restriction to star chains is introduced by the reachability relation. -/
theorem additionChain_reaches {c : List ℕ} {n : ℕ} (hc : IsAdditionChain c)
    (hn : c.getLast? = some n) : ChainReach n [1] 1 (c.length - 1) := by
  obtain ⟨cert, hr, hl⟩ := additionChain_exists_replay hc
  have hh := replayFrom_reaches hr (by rfl : ([1] : List ℕ).getLast? = some 1) hn
  have he : cert.length = c.length - 1 := by omega
  simpa [he] using hh

/-- Every valid upstream extension is represented, including arbitrary prefixes.
Positivity forces the next value's summands to lie strictly before that value. -/
theorem additionChain_extension_reaches {c s : List ℕ} {m n : ℕ}
    (hc : IsAdditionChain (c ++ s)) (hm : c.getLast? = some m)
    (hn : (c ++ s).getLast? = some n) : ChainReach n c m s.length := by
  induction s generalizing c m with
  | nil =>
    have he : m = n := by simpa [hm] using hn
    subst m
    exact .stop _ _
  | cons x xs ih =>
    have hmx : m < x := (List.pairwise_append.mp hc.2.1).2.2
      m (List.mem_of_getLast? hm) x (by simp)
    have hmpos := hc.one_le_of_mem (List.mem_append_left _ (List.mem_of_getLast? hm))
    have hearly : ∀ y ∈ c ++ x :: xs, y < x → y ∈ c := by
      intro y hy hyx
      rcases List.mem_append.mp hy with hy | hy
      · exact hy
      · rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · have hh := (List.pairwise_cons.mp (List.pairwise_append.mp hc.2.1).2.1).1 y hy
          omega
    obtain ⟨a, ha, b, hb, he⟩ := hc.2.2 x (by simp) (by omega)
    have hapos := hc.one_le_of_mem ha
    have hbpos := hc.one_le_of_mem hb
    have hap := hearly a ha (by omega)
    have hbp := hearly b hb (by omega)
    have hnext : ChainReach n (c ++ [x]) x xs.length :=
      ih (by simpa [List.append_assoc] using hc) (by simp)
        (by simpa [List.append_assoc] using hn)
    rw [he] at hnext
    exact .step hap hbp (by omega) hnext

/-- `invalid` is the rejecting default for an out-of-range reference. -/
inductive ExclusionNode
  | invalid
  | bound
  | gap
  | split (edges : List (ℕ × ℕ))
  deriving DecidableEq, Repr, Inhabited

/-- Check coverage and every child in its own context. Coverage may contain
extra edges; these only add obligations, so exact sorting/deduplication is not
needed for soundness. Portable certificates provide exact sorted coverage. -/
def checkExclusion (nodes : Array ExclusionNode) (n : ℕ) :
    (c : List ℕ) → (m r id : ℕ) → Bool
  | c, m, r, id =>
    if m = n then false else
    match nodes[id]?.getD .invalid with
    | .invalid => false
    | .bound => decide (m * 2 ^ r < n)
    | .gap => decide (r = 1 ∧ ∀ a ∈ c, ∀ b ∈ c, a + b ≠ n)
    | .split edges =>
      match r with
      | 0 => false
      | k + 1 =>
        decide (∀ a ∈ c, ∀ b ∈ c, m < a + b → a + b ≤ n →
          n ≤ (a + b) * 2 ^ k → ∃ e ∈ edges, e.1 = a + b) &&
        edges.all (fun e => checkExclusion nodes n (c ++ [e.1]) e.1 k e.2)

theorem checkExclusion_sound {nodes : Array ExclusionNode} {n r id m : ℕ}
    {c : List ℕ} (hcheck : checkExclusion nodes n c m r id = true)
    (hc : ∀ x ∈ c, x ≤ m) : ¬ ChainReach n c m r := by
  induction r generalizing c m id with
  | zero =>
    intro hr
    cases hr with
    | stop => rw [checkExclusion, if_pos rfl] at hcheck; contradiction
  | succ r ih =>
    intro hr
    have hne : m ≠ n := by
      intro he
      rw [checkExclusion, if_pos he] at hcheck
      contradiction
    rw [checkExclusion, if_neg hne] at hcheck
    cases hnode : nodes[id]?.getD .invalid with
    | invalid => simp [hnode] at hcheck
    | bound =>
      have hh : m * 2 ^ (r + 1) < n := by simpa [hnode] using hcheck
      have := hr.doubling_bound hc
      omega
    | gap =>
      have hh : r + 1 = 1 ∧ ∀ a ∈ c, ∀ b ∈ c, a + b ≠ n := by
        simpa [hnode] using hcheck
      have hz : r = 0 := by omega
      subst r
      cases hr with
      | stop => exact hne rfl
      | step ha hb hgt hn =>
        cases hn with
        | stop => exact hh.2 _ ha _ hb rfl
    | split edges =>
      simp only [hnode, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcheck
      cases hr with
      | stop => exact hne rfl
      | @step _ _ _ a b ha hb hgt hn =>
        have hnext : ∀ x ∈ c ++ [a + b], x ≤ a + b := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact le_trans (hc x hx) (Nat.le_of_lt hgt)
          · exact le_of_eq (List.mem_singleton.mp hx)
        obtain ⟨e, he, hv⟩ := hcheck.1 a ha b hb hgt hn.endpoint_le
          (hn.doubling_bound hnext)
        have hh := hcheck.2 e he
        rw [hv] at hh
        exact ih hh hnext hn

/-- Acceptance excludes every upstream chain with at most `r` additions. -/
theorem checkExclusion_excludes {nodes : Array ExclusionNode} {n r id : ℕ}
    (h : checkExclusion nodes n [1] 1 r id = true) {c : List ℕ}
    (hc : IsAdditionChain c) (hn : c.getLast? = some n) (hlen : c.length - 1 ≤ r) : False :=
  checkExclusion_sound h (by simp) ((additionChain_reaches hc hn).mono hlen)

/-- Soundness stated directly for arbitrary upstream-valid prefix extensions. -/
theorem checkExclusion_excludes_extension {nodes : Array ExclusionNode}
    {n r id m : ℕ} {c s : List ℕ}
    (h : checkExclusion nodes n c m r id = true)
    (hc : IsAdditionChain (c ++ s)) (hm : c.getLast? = some m)
    (hn : (c ++ s).getLast? = some n) (hlen : s.length ≤ r) : False := by
  have hmax : ∀ x ∈ c, x ≤ m := by
    intro x hx
    have hne : c ≠ [] := by intro he; simp [he] at hm
    have hlast : c.getLast hne = m := by
      rw [List.getLast?_eq_some_getLast hne] at hm
      exact Option.some.inj hm
    have hh := ((List.pairwise_append.mp hc.2.1).1.imp le_of_lt).rel_getLast hx
    simpa [hlast] using hh
  exact checkExclusion_sound h hmax ((additionChain_extension_reaches hc hm hn).mono hlen)

/-- A known witness supplies nonemptiness of the infimum defining `ell`. -/
theorem checkExclusion_lower_bound {nodes : Array ExclusionNode} {n r id : ℕ}
    (h : checkExclusion nodes n [1] 1 r id = true)
    (hne : (additionChainSteps n).Nonempty) : r < additionChainLength n := by
  by_contra! hle
  obtain ⟨c, hc, hn, hlen⟩ := Nat.sInf_mem hne
  apply checkExclusion_excludes h hc hn
  change c.length = additionChainLength n + 1 at hlen
  omega

/-- The existing generator's entire 7/3 DAG, with gap node 0. -/
def exclusionSeven : Array ExclusionNode :=
  #[.gap, .split [(4, 0)], .split [(2, 1)]]

theorem exclusionSeven_checked : checkExclusion exclusionSeven 7 [1] 1 3 2 = true := by
  decide

theorem length_seven_eq_four : additionChainLength 7 = 4 := by
  have hc : IsAdditionChain [1, 2, 3, 4, 7] := by decide
  have hne := additionChainSteps_nonempty (n := 7) (r := 4) _ hc rfl rfl
  have hlo := checkExclusion_lower_bound exclusionSeven_checked hne
  have hhi := additionChainLength_le (n := 7) (r := 4) _ hc rfl rfl
  omega

-- Critical rejection boundaries: a reached target, missing branch, invalid
-- reference, false final-gap rule, and a cyclic reference (fuel must decrease).
example : checkExclusion #[.bound] 1 [1] 1 0 0 = false := by decide
example : checkExclusion #[.split []] 7 [1] 1 3 0 = false := by decide
example : checkExclusion #[] 7 [1] 1 3 0 = false := by decide
example : checkExclusion #[.gap] 7 [1, 2, 3, 4] 4 1 0 = false := by decide
example : checkExclusion #[.split [(2, 0), (4, 0), (8, 0)]] 9 [1] 1 4 0 = false := by decide
-- The same syntax is valid in one prefix but invalid in another.
example : checkExclusion #[.gap] 15 [1, 2, 3, 4, 8] 8 1 0 = true := by decide
example : checkExclusion #[.gap] 15 [1, 2, 3, 5, 10] 10 1 0 = false := by decide
example : checkExclusion #[.bound] 9 [1] 1 3 0 = true := by decide

end ScholzBrauer
