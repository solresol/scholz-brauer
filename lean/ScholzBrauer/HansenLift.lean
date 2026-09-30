import ScholzBrauer.HansenAllocation

/-! The complete Hansen lift: sort the finite, closed allocation, then realise
that sorted addition chain by the existing summand-value replay. No optimality
of the source is assumed until the explicitly conditional Scholz corollary. -/
namespace ScholzBrauer

/-- The sorted numerical allocation, including its seed. -/
def hansenLift (steps : List MarkedStep) : List ℕ :=
  ((hansenLabels 1 steps).map (fun p => shiftedMersenne p.1 p.2)).mergeSort (· ≤ ·)

theorem mem_hansenLift {steps : List MarkedStep} {x : ℕ} :
    x ∈ hansenLift steps ↔ ∃ p ∈ hansenLabels 1 steps, shiftedMersenne p.1 p.2 = x := by
  unfold hansenLift
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_map]

/-- The exponent envelope bounds every numerical node by the final Mersenne. -/
theorem shiftedMersenne_le_endpoint {a k n : ℕ} (h : a + k ≤ n) :
    shiftedMersenne a k ≤ 2 ^ n - 1 := by
  have hp := Nat.two_pow_pos k
  have hn := Nat.pow_le_pow_right (by decide : 1 ≤ 2) h
  have he : shiftedMersenne a k = 2 ^ (a + k) - 2 ^ k := by
    simp [shiftedMersenne, Nat.mul_sub_left_distrib, pow_add, Nat.mul_comm]
  omega

/-- Sorting preserves membership and count, and closure supplies all sums.
This is an actual addition chain with the exact Hansen length. -/
theorem hansenLift_chain {steps : List MarkedStep} {n : ℕ}
    (h : IsHansenFrom [1] 1 steps) (hn : hansenAnchorFrom 1 steps = n) :
    IsAdditionChain (hansenLift steps) ∧
    (hansenLift steps).getLast? = some (2 ^ n - 1) ∧
    (hansenLift steps).length = (n - 1 + steps.length) + 1 := by
  have hs : IsAdditionChain [1] := by decide
  have ha : 1 ∈ ([1] : List ℕ) := by simp
  have hp := hansenLabels_positive hs ha h
  have hd := shiftedMersenne_nodup (hansenLabels_nodup ha h) hp
  have hperm := List.mergeSort_perm
    ((hansenLabels 1 steps).map (fun p => shiftedMersenne p.1 p.2)) (· ≤ ·)
  have hle : (hansenLift steps).Pairwise (· ≤ ·) := List.pairwise_mergeSort' _ _
  have hnd : (hansenLift steps).Nodup := hperm.nodup_iff.mpr hd
  have hlt : (hansenLift steps).Pairwise (· < ·) :=
    (hle.and (List.nodup_iff_pairwise_ne.mp hnd)).imp (fun hh => lt_of_le_of_ne hh.1 hh.2)
  have hpos : ∀ x ∈ hansenLift steps, 0 < x := by
    intro x hx
    obtain ⟨p, hm, rfl⟩ := mem_hansenLift.mp hx
    exact shiftedMersenne_pos (hp p hm) p.2
  have hseed : 1 ∈ hansenLift steps := mem_hansenLift.mpr
    ⟨(1, 0), hansenLabels_base 1 steps, by decide⟩
  have hne : hansenLift steps ≠ [] := by rintro he; simp [he] at hseed
  have hhead : (hansenLift steps).head? = some 1 := by
    rw [List.head?_eq_some_head hne]
    congr 1
    have hlow := hpos _ (List.head_mem hne)
    have hhigh := hle.rel_head hseed
    omega
  have hsum : ∀ x ∈ hansenLift steps, x ≠ 1 →
      ∃ y ∈ hansenLift steps, ∃ z ∈ hansenLift steps, x = y + z := by
    intro x hx hx1
    obtain ⟨p, hm, rfl⟩ := mem_hansenLift.mp hx
    have hp1 : p ≠ (1, 0) := by rintro rfl; exact hx1 (by decide)
    obtain ⟨q, hq, r, hr, he⟩ := hansenLabels_closed h p hm hp1
    exact ⟨_, mem_hansenLift.mpr ⟨q, hq, rfl⟩,
      _, mem_hansenLift.mpr ⟨r, hr, rfl⟩, he⟩
  refine ⟨⟨hhead, hlt, hsum⟩, ?_, ?_⟩
  · have hendSource : n ∈ hansenSourceFrom [1] steps := by
      have he := hansenSourceFrom_endpoint h
      rw [hn] at he
      exact List.mem_of_getLast? he
    have hendLabel : (n, 0) ∈ hansenLabels 1 steps := by
      rcases hansenLabels_source_base (a := 1) hendSource with hh | hh
      · simpa [List.mem_singleton.mp hh] using hansenLabels_base 1 steps
      · exact hh
    have hend : 2 ^ n - 1 ∈ hansenLift steps := mem_hansenLift.mpr
      ⟨(n, 0), hendLabel, by simp [shiftedMersenne]⟩
    have hbound : ∀ x ∈ hansenLift steps, x ≤ 2 ^ n - 1 := by
      intro x hx
      obtain ⟨p, hm, rfl⟩ := mem_hansenLift.mp hx
      exact shiftedMersenne_le_endpoint (hn ▸ hansenLabels_envelope hs ha h p hm)
    rw [List.getLast?_eq_some_getLast hne]
    congr 1
    exact le_antisymm (hbound _ (List.getLast_mem hne)) (hle.rel_getLast hend)
  · simp only [hansenLift, List.length_mergeSort, List.length_map, hansenLabels_length,
      hansenShiftCaps_sum h hn]
    omega

/-- Every addition chain admits a successful summand-value replay in its
existing order. Positivity ensures that the last node's summands occur earlier. -/
theorem additionChain_exists_replay {c : List ℕ} (hc : IsAdditionChain c) :
    ∃ cert : List Step, replay cert = some c ∧ cert.length + 1 = c.length := by
  suffices ∃ cert : List Step, replay cert = some c by
    obtain ⟨cert, hr⟩ := this
    exact ⟨cert, hr, (replay_length hr).symm⟩
  induction c using List.reverseRecOn with
  | nil => simp [IsAdditionChain] at hc
  | append_singleton ys y ih =>
    rcases eq_or_ne ys [] with rfl | hys
    · have hy : y = 1 := by simpa [IsAdditionChain] using hc.1
      subst y
      exact ⟨[], rfl⟩
    · have hprefix := hc.dropLast hys
      obtain ⟨cert, hr⟩ := ih hprefix
      have hy1 : y ≠ 1 := by
        have hhead : 1 ∈ ys := List.mem_of_head? hprefix.1
        have hgt := (List.pairwise_append.mp hc.2.1).2.2 1 hhead y (by simp)
        omega
      obtain ⟨a, ha, b, hb, he⟩ := hc.2.2 y (by simp) hy1
      have hapos := hc.one_le_of_mem ha
      have hbpos := hc.one_le_of_mem hb
      have hap : a ∈ ys := by
        rcases List.mem_append.mp ha with ha | ha
        · exact ha
        · have := List.mem_singleton.mp ha; omega
      have hbp : b ∈ ys := by
        rcases List.mem_append.mp hb with hb | hb
        · exact hb
        · have := List.mem_singleton.mp hb; omega
      have hgt : ∀ x ∈ ys, x < a + b := by
        intro x hx
        rw [← he]
        exact (List.pairwise_append.mp hc.2.1).2.2 x hx y (by simp)
      have hext : extend ys (a, b) = some (ys ++ [y]) := by
        unfold extend
        rw [if_pos ⟨hap, hbp, hgt⟩]
        rw [he]
      refine ⟨cert ++ [(a, b)], ?_⟩
      change replayFrom [1] (cert ++ [(a, b)]) = _
      rw [replayFrom_append, show replayFrom [1] cert = some ys from hr]
      simp only [Option.bind_some, replayFrom, hext]

/-- The general Hansen lift has a successful sorted replay with precisely
`n-1+r` additions for an accepted `r`-step marked source ending at `n`. -/
theorem hansenLift_certificate {steps : List MarkedStep} {n : ℕ}
    (h : IsHansenFrom [1] 1 steps) (hn : hansenAnchorFrom 1 steps = n) :
    ∃ cert : List Step, replay cert = some (hansenLift steps) ∧
      cert.length = n - 1 + steps.length ∧
      (hansenLift steps).getLast? = some (2 ^ n - 1) := by
  obtain ⟨hc, he, hl⟩ := hansenLift_chain h hn
  obtain ⟨cert, hr, hlen⟩ := additionChain_exists_replay hc
  exact ⟨cert, hr, by omega, he⟩

/-- Hansen's upper bound, without any assumption that the source is optimal. -/
theorem hansenLift_upper_bound {steps : List MarkedStep} {n : ℕ}
    (h : IsHansenFrom [1] 1 steps) (hn : hansenAnchorFrom 1 steps = n) :
    additionChainLength (2 ^ n - 1) ≤ n - 1 + steps.length := by
  obtain ⟨hc, he, hl⟩ := hansenLift_chain h hn
  exact additionChainLength_le _ hc he hl

/-- Conditional Scholz theorem: only optimality of this particular accepted
source remains to be supplied. No universal Hansen or optimality assertion. -/
theorem scholz_of_optimal_hansen {steps : List MarkedStep} {n : ℕ}
    (h : IsHansenFrom [1] 1 steps) (hn : hansenAnchorFrom 1 steps = n)
    (hopt : steps.length = additionChainLength n) :
    additionChainLength (2 ^ n - 1) ≤ n - 1 + additionChainLength n := by
  simpa [hopt] using hansenLift_upper_bound h hn

-- The general theorem includes the zero-step source and interleaved nodes.
example : hansenLift [] = [1] := by simp [hansenLift, hansenLabels, shiftedMersenne]
example : additionChainLength (2 ^ 1 - 1) ≤ 0 :=
  hansenLift_upper_bound (by decide : IsHansenFrom [1] 1 []) rfl
example : additionChainLength (2 ^ 29 - 1) ≤ 35 :=
  hansenLift_upper_bound (by decide : IsHansenFrom [1] 1
    [(2, true), (4, true), (8, true), (9, false), (12, false),
     (17, true), (29, true)]) rfl

end ScholzBrauer
