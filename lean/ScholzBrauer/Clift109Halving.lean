import ScholzBrauer.Clift109Normalize

/-! Exact multiset halving for the interval classification. Integer weights
retain the signed offsets of the normalized remainder. Peeling the least
weight is complete for every positive translation, including multiplicities. -/

namespace ScholzBrauer.Clift109

/-- A bounded version of the existing search's least-weight peeling step. -/
def halveAux (d : ℤ) : ℕ → Multiset ℤ → Option (Multiset ℤ)
  | 0, s => if s = 0 then some 0 else none
  | fuel + 1, s =>
      if h : s.toFinset.Nonempty then
        let m := s.toFinset.min' h
        if m + d ∈ s.erase m then
          (halveAux d fuel ((s.erase m).erase (m + d))).map (m ::ₘ ·)
        else none
      else some 0

/-- The input cardinality supplies sufficient fuel; no search limit is assumed. -/
def halve (d : ℤ) (s : Multiset ℤ) : Option (Multiset ℤ) :=
  halveAux d s.card s

private theorem empty_of_not_nonempty {s : Multiset ℤ}
    (h : ¬s.toFinset.Nonempty) : s = 0 := by
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro x hx
  exact h ⟨x, Multiset.mem_toFinset.mpr hx⟩

/-- Acceptance reconstructs the entire input multiset, with multiplicities. -/
theorem halveAux_sound (d : ℤ) (fuel : ℕ) (s a : Multiset ℤ)
    (h : halveAux d fuel s = some a) : s = zbranch a d := by
  induction fuel generalizing s a with
  | zero =>
    simp only [halveAux] at h
    split_ifs at h with hs
    · cases h
      simpa [zbranch, zshift] using hs
  | succ fuel ih =>
    simp only [halveAux] at h
    split_ifs at h with hs hm
    · obtain ⟨a', ha', heq⟩ := Option.map_eq_some_iff.mp h
      subst a
      have hmem : s.toFinset.min' hs ∈ s :=
        Multiset.mem_toFinset.mp (Finset.min'_mem _ _)
      have hr := ih _ _ ha'
      have hrestore := Multiset.cons_erase hm
      rw [hr] at hrestore
      have hrestore' := Multiset.cons_erase hmem
      rw [← hrestore] at hrestore'
      simpa [zbranch, zshift, Multiset.cons_add, Multiset.add_cons,
        Multiset.cons_swap] using hrestore'.symm
    · cases h
      simpa [zbranch, zshift] using empty_of_not_nonempty hs

private theorem peel_branch (d m : ℤ) (a : Multiset ℤ) (hm : m ∈ a) :
    zbranch a d = m ::ₘ (m + d) ::ₘ zbranch (a.erase m) d := by
  conv_lhs => rw [← Multiset.cons_erase hm]
  simp [zbranch, zshift, Multiset.cons_add, Multiset.add_cons, Multiset.cons_swap]

/-- Every translated double is accepted, with its original half recovered. -/
theorem halveAux_complete (d : ℤ) (hd : 0 < d) (fuel : ℕ)
    (a : Multiset ℤ) (hf : a.card ≤ fuel) :
    halveAux d fuel (zbranch a d) = some a := by
  induction fuel generalizing a with
  | zero =>
    have ha : a = 0 := Multiset.card_eq_zero.mp (by omega)
    subst a
    simp [halveAux, zbranch, zshift]
  | succ fuel ih =>
    by_cases hs : (zbranch a d).toFinset.Nonempty
    · let m := (zbranch a d).toFinset.min' hs
      have hmS : m ∈ zbranch a d := Multiset.mem_toFinset.mp (Finset.min'_mem _ _)
      have hmin : ∀ x ∈ zbranch a d, m ≤ x := by
        intro x hx
        exact Finset.min'_le _ _ (Multiset.mem_toFinset.mpr hx)
      have hm : m ∈ a := by
        rcases Multiset.mem_add.mp hmS with hm | hm
        · exact hm
        · obtain ⟨x, hx, heq⟩ := Multiset.mem_map.mp hm
          have hle := hmin x (Multiset.mem_add.mpr (Or.inl hx))
          omega
      have heq := peel_branch d m a hm
      have hpartner : m + d ∈ (zbranch a d).erase m := by
        rw [heq, Multiset.erase_cons_head]
        exact Multiset.mem_cons_self _ _
      have herase : ((zbranch a d).erase m).erase (m + d) =
          zbranch (a.erase m) d := by
        rw [heq, Multiset.erase_cons_head, Multiset.erase_cons_head]
      have hf' : (a.erase m).card ≤ fuel := by
        have hc := Multiset.card_cons m (a.erase m)
        rw [Multiset.cons_erase hm] at hc
        omega
      simp only [halveAux, dif_pos hs]
      change (if m + d ∈ (zbranch a d).erase m then _ else _) = _
      rw [if_pos hpartner, herase, ih _ hf']
      simp only [Option.map_some, Option.some.injEq]
      exact Multiset.cons_erase hm
    · have hz := empty_of_not_nonempty hs
      have ha : a = 0 := by
        have hc := congrArg Multiset.card hz
        simp only [zbranch, zshift, Multiset.card_add, Multiset.card_map,
          Multiset.card_zero] at hc
        exact Multiset.card_eq_zero.mp (by omega)
      subst a
      simp [halveAux, zbranch, zshift]

/-- Exact decision and recovery, not just a necessary divisibility test. -/
theorem halve_eq_some_iff (d : ℤ) (hd : 0 < d) (s a : Multiset ℤ) :
    halve d s = some a ↔ s = zbranch a d := by
  constructor
  · exact halveAux_sound d s.card s a
  · intro h
    subst s
    apply halveAux_complete d hd
    simp [zbranch, zshift]

/-- A finite multiset has at most one half for a positive translation. -/
theorem zbranch_injective (d : ℤ) (hd : 0 < d) :
    Function.Injective (fun a : Multiset ℤ => zbranch a d) := by
  intro a b h
  have ha := (halve_eq_some_iff d hd (zbranch a d) a).mpr rfl
  have hb := (halve_eq_some_iff d hd (zbranch a d) b).mpr h
  exact Option.some.inj (ha.symm.trans hb)

/-- Rejection excludes every half; it cannot be a fuel timeout. -/
theorem halve_eq_none_iff (d : ℤ) (hd : 0 < d) (s : Multiset ℤ) :
    halve d s = none ↔ ¬ ∃ a, s = zbranch a d := by
  constructor
  · rintro h ⟨a, ha⟩
    have := (halve_eq_some_iff d hd s a).mpr ha
    rw [h] at this
    contradiction
  · intro h
    cases heq : halve d s with
    | none => rfl
    | some a => exact (h ⟨a, (halve_eq_some_iff d hd s a).mp heq⟩).elim

-- Empty input, signed repeated weights, overlapping translates, and rejection.
example : halve 3 0 = some 0 := by decide +kernel
example : halve 2 {-3, -3, -1, -1} = some {-3, -3} := by decide +kernel
example : halve 1 {0, 1, 1, 2} = some {0, 1} := by decide +kernel
example : halve 2 {0, 1} = none := by decide +kernel

/-- Seven exceptional sink-side weights, retaining multiplicities. -/
def sinkExceptions (c : GaugeCoordinates) : Multiset ℤ :=
  zshift (zbranch (zbranch {c.p} c.u) c.v) c.A1 +
  zshift (zbranch {c.p} c.u) c.A2 + {c.A3 + c.p}

/-- The nineteen weights remaining after sink-side halving. -/
def sinkHalf (c : GaugeCoordinates) : Multiset ℤ :=
  zshift (zbranch (zbranch ({0, c.d2} + {c.q}) c.u) c.v) c.A1 +
  zshift (zbranch {0, c.d2} c.u) c.A2 +
  zshift ({0, c.d2} + {c.q}) c.A3

/-- The nineteen weights remaining after source-side halving. -/
def sourceHalf (c : GaugeCoordinates) : Multiset ℤ :=
  zshift (zbranch (rem5 c) c.v) c.A1 + zshift (rem7 c) c.A2

/-- Sink-side decomposition used by the existing C++ enumeration. -/
theorem remainder_sink_factor (c : GaugeCoordinates) :
    coordinateRemainder c = zbranch (sinkHalf c) c.d1 + sinkExceptions c := by
  simp [coordinateRemainder, sinkHalf, sinkExceptions, rem5, rem7, zSS,
    zbranch, zshift]
  simp only [Int.add_left_comm, Int.add_comm, ← Multiset.singleton_add]
  ac_rfl

/-- Source-side decomposition used by the independent Python enumeration. -/
theorem remainder_source_factor (c : GaugeCoordinates) :
    coordinateRemainder c = zbranch (sourceHalf c) c.u + zshift (rem5 c) c.A3 := by
  simp [coordinateRemainder, sourceHalf, zbranch, zshift]
  simp only [Int.add_left_comm, Int.add_comm]
  ac_rfl

theorem card_sinkExceptions (c : GaugeCoordinates) : (sinkExceptions c).card = 7 := by
  simp [sinkExceptions, zbranch, zshift]

theorem card_sinkHalf (c : GaugeCoordinates) : (sinkHalf c).card = 19 := by
  simp [sinkHalf, zbranch, zshift]

theorem card_sourceHalf (c : GaugeCoordinates) : (sourceHalf c).card = 19 := by
  simp [sourceHalf, rem5, rem7, zSS, zbranch, zshift]

theorem card_sourceExceptions (c : GaugeCoordinates) :
    (zshift (rem5 c) c.A3).card = 7 := by
  simp [rem5, rem7, zSS, zbranch, zshift]

/-- Both interval remainders are recovered exactly by halving. No assertion
about feasible caps, or completeness of the whole search, is assumed. -/
theorem interval_halving (c : GaugeCoordinates) (hu : 0 < c.u) (hd : 0 < c.d1)
    (h : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    halve c.d1 (((Multiset.range 109).map Int.ofNat - coordinateBox c) -
      sinkExceptions c) = some (sinkHalf c) ∧
    halve c.u (((Multiset.range 109).map Int.ofNat - coordinateBox c) -
      zshift (rem5 c) c.A3) = some (sourceHalf c) := by
  rw [← h]
  simp only [coordinateWeights, add_tsub_cancel_left]
  constructor
  · apply (halve_eq_some_iff _ hd _ _).mpr
    rw [remainder_sink_factor, add_tsub_cancel_right]
  · apply (halve_eq_some_iff _ hu _ _).mpr
    rw [remainder_source_factor, add_tsub_cancel_right]

/-- The multiset identities become disjoint set partitions under the interval
equation. In particular the seven exceptions and nineteen half-weights really
are distinct; no bit-mask interpretation is assumed in the preceding algebra. -/
theorem interval_halves_disjoint (c : GaugeCoordinates)
    (h : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    (sinkHalf c).Nodup ∧ Disjoint (sinkHalf c) (zshift (sinkHalf c) c.d1) ∧
      (sinkExceptions c).Nodup ∧
      Disjoint (zbranch (sinkHalf c) c.d1) (sinkExceptions c) ∧
    (sourceHalf c).Nodup ∧ Disjoint (sourceHalf c) (zshift (sourceHalf c) c.u) ∧
      (zshift (rem5 c) c.A3).Nodup ∧
      Disjoint (zbranch (sourceHalf c) c.u) (zshift (rem5 c) c.A3) := by
  have hnd : (coordinateWeights c).Nodup := by
    rw [h]
    exact (Multiset.nodup_range 109).map Int.ofNat_injective
  have hr := (Multiset.nodup_add.mp hnd).2.1
  have hs := hr
  rw [remainder_sink_factor] at hs
  rw [remainder_source_factor] at hr
  obtain ⟨hsb, hse, hsd⟩ := Multiset.nodup_add.mp hs
  obtain ⟨hrb, hre, hrd⟩ := Multiset.nodup_add.mp hr
  obtain ⟨hsn, _, hsbd⟩ := Multiset.nodup_add.mp hsb
  obtain ⟨hrn, _, hrbd⟩ := Multiset.nodup_add.mp hrb
  exact ⟨hsn, hsbd, hse, hsd, hrn, hrbd, hre, hrd⟩

/-- Every hypothetical budget-108 labelling passes both exact halving steps
and induces the disjoint partitions above. This ties the reduction to the
original natural edge labelling, not only to a freely chosen coordinate tuple. -/
theorem halving_of_budget (B a b cap : ℕ → ℕ) (h1 : B 1 = 1)
    (hsteps : ∀ s ∈ selectedSteps,
      B s.1 * 2 ^ a (s.1 + s.2) + B s.2 * 2 ^ b (s.1 + s.2) = B (s.1 + s.2))
    (hcap : ∀ s ∈ selectedSteps, a (s.1 + s.2) ≤ cap s.1 ∧ b (s.1 + s.2) ≤ cap s.2)
    (h109 : B 109 = 2 ^ 109 - 1)
    (hbudget : cap 1 + cap 2 + cap 4 + cap 5 + cap 7 + cap 8 + cap 15 +
      cap 23 + cap 28 + cap 51 + cap 58 ≤ 108) :
    let c := minimumCoordinates (fun i => a i) (fun i => b i)
    0 < c.u ∧ 0 < c.d1 ∧
    halve c.d1 (((Multiset.range 109).map Int.ofNat - coordinateBox c) -
      sinkExceptions c) = some (sinkHalf c) ∧
    halve c.u (((Multiset.range 109).map Int.ofNat - coordinateBox c) -
      zshift (rem5 c) c.A3) = some (sourceHalf c) := by
  dsimp only
  have hp := CliftLabelling.positive_of_subsetSums_nodup _
    (box_dissociated B a b h1 hsteps h109)
  have hpu := hp (CliftLabelling.pairGap (a 2, b 2)) (by simp [boxPairs])
  have hpd := hp (CliftLabelling.pairGap (a 58 + a 109, b 109)) (by simp [boxPairs])
  simp only [CliftLabelling.pairGap] at hpu hpd
  have hu : 0 < (minimumCoordinates (fun i => (a i : ℤ)) (fun i => (b i : ℤ))).u := by
    simp only [minimumCoordinates, abs_pos, sub_ne_zero]
    omega
  have hd : 0 < (minimumCoordinates (fun i => (a i : ℤ)) (fun i => (b i : ℤ))).d1 := by
    simp only [minimumCoordinates, abs_pos, sub_ne_zero]
    omega
  exact ⟨hu, hd, interval_halving _ hu hd
    (normalized_interval_of_budget B a b cap h1 hsteps hcap h109 hbudget)⟩

end ScholzBrauer.Clift109
