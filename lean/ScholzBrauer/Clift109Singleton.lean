import ScholzBrauer.Clift109OddRuns
import ScholzBrauer.Clift109SinkPositions

namespace ScholzBrauer.Clift109
open scoped Classical

private theorem runClass_modEq {d x y : ℤ} {s : Multiset ℤ}
    (h : runClass d s x = runClass d s y) : x ≡ y [ZMOD d] := by
  have hr : Relation.EqvGen (fun i j => i ∈ s ∧ j ∈ s ∧ j = i + d) x y :=
    Quotient.exact h
  clear h
  induction hr with
  | rel i j he => rw [he.2.2]; exact Int.add_modEq_right.symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ij => exact ih.trans ij

private theorem paired_run_edge (d : ℤ) (a : Multiset ℤ) (x : ℤ) (hx : x ∈ a) :
    x ∈ zbranch a d ∧ x + d ∈ zbranch a d := by
  exact ⟨Multiset.mem_add.mpr (.inl hx),
    Multiset.mem_add.mpr (.inr (Multiset.mem_map.mpr ⟨x, hx, rfl⟩))⟩

/-- In a translated double with one exceptional weight, exactly its run is odd. -/
theorem singleton_odd_class (d : ℤ) (a : Multiset ℤ) (z : ℤ) :
    let s := zbranch a d + {z}
    ∀ q, ((s.map (runClass d s)).count q % 2 = 1 ↔ q = runClass d s z) := by
  classical
  dsimp only
  intro q
  let s := zbranch a d + {z}
  have he (x) (hx : x ∈ a) := paired_run_edge d a x hx
  have hc := paired_class_count d a {z} (runClass d s)
    (fun x hx => runClass_step d s x (Multiset.mem_add.mpr (.inl (he x hx).1))
      (Multiset.mem_add.mpr (.inl (he x hx).2))) q
  rw [hc]
  by_cases h : q = runClass d s z <;> simp [s] at h ⊢ <;> simp [h]

/-- The number of elements on either chosen side of the singleton within its
original run is even. Choosing the lower side gives the zero-based index. -/
theorem singleton_run_side_even (d : ℤ) (hd : 0 < d) (a : Multiset ℤ) (z : ℤ)
    (hn : (zbranch a d + {z}).Nodup) (lower : Bool) :
    let s := zbranch a d + {z}
    (s.filter (fun x => runClass d s x = runClass d s z ∧
      (if lower then x < z else z < x))).card % 2 = 0 := by
  classical
  let s := zbranch a d + {z}
  let p (x : ℤ) := runClass d s x = runClass d s z ∧ (if lower then x < z else z < x)
  have hf (x) (hx : x ∈ a) : decide (p (x+d)) = decide (p x) := by
    obtain ⟨h1,h2⟩ := paired_run_edge d a x hx
    have hs := runClass_step d s x (Multiset.mem_add.mpr (.inl h1))
      (Multiset.mem_add.mpr (.inl h2))
    have hz : z ∉ zbranch a d :=
      fun h => Multiset.disjoint_left.mp (Multiset.nodup_add.mp hn).2.2 h (by simp)
    have hxz : x ≠ z := fun h => hz (h ▸ h1)
    have hdz : x+d ≠ z := fun h => hz (h ▸ h2)
    by_cases h : runClass d s x = runClass d s z
    · have hle (hlt : x < z) : x+d ≤ z := by
        have := Int.le_of_dvd (show 0 < z-x by omega) (runClass_modEq h).dvd
        omega
      cases lower <;> simp [p, hs, h] <;> omega
    · simp [p, hs, h]
  have hc := paired_class_count d a {z} (fun x => decide (p x)) hf true
  have hp : ¬ p z := by cases lower <;> simp [p, *]
  change (s.filter p).card % 2 = 0
  have hcount : (s.map (fun x => decide (p x))).count true = (s.filter p).card := by
    simp [Multiset.count_map]
  change (s.map (fun x => decide (p x))).count true = _ at hc
  rw [← hcount, hc]
  simp [hp]

/-- Necessary singleton test directly on the staged sink-position remainder. -/
theorem interval_sink_singleton_runs (c : GaugeCoordinates) (hd : 0 < c.d1)
    (hi : coordinateWeights c = (Multiset.range 109).map Int.ofNat) :
    let s := (Multiset.range 109).map Int.ofNat - coordinateBox c -
      sinkRectangle c (c.A1 + c.p) - sinkPair c (c.A2 + c.p)
    let z := c.A3 + c.p
    (∀ q, (s.map (runClass c.d1 s)).count q % 2 = 1 ↔ q = runClass c.d1 s z) ∧
      ∀ lower : Bool, (s.filter (fun x => runClass c.d1 s x = runClass c.d1 s z ∧
        (if lower then x < z else z < x))).card % 2 = 0 := by
  dsimp only
  let r := sinkRectangle c (c.A1 + c.p)
  let t := sinkPair c (c.A2 + c.p)
  let z := c.A3 + c.p
  have hex : sinkExceptions c = r + t + {z} := sinkExceptions_eq_placed c
  have hs : (Multiset.range 109).map Int.ofNat - coordinateBox c - r - t =
      zbranch (sinkHalf c) c.d1 + {z} := by
    rw [← hi]
    simp only [coordinateWeights, add_tsub_cancel_left, remainder_sink_factor, hex]
    rw [show zbranch (sinkHalf c) c.d1 + (r + t + {z}) =
      r + (t + (zbranch (sinkHalf c) c.d1 + {z})) by ac_rfl]
    simp
  have hn : (zbranch (sinkHalf c) c.d1 + {z}).Nodup := by
    rw [← hs]
    apply Multiset.nodup_of_le ((Multiset.sub_le_self _ _).trans
      ((Multiset.sub_le_self _ _).trans (Multiset.sub_le_self _ _)))
    exact (Multiset.nodup_range 109).map Int.ofNat_injective
  rw [hs]
  exact ⟨singleton_odd_class _ _ _, singleton_run_side_even _ hd _ _ hn⟩

end ScholzBrauer.Clift109
