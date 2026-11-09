import ScholzBrauer.Clift109PlacedPairs

/-! A signed residue fingerprint retains more of the exception positions than
parity. Translation by m negates each digit, so every regular m-pair cancels.
Radix four is only a necessary scalar invariant; injectivity is not assumed. -/

namespace ScholzBrauer.Clift109

/-- Signed evaluation modulo X^m+1, at radix four. Defined for signed positions. -/
def alternatingDigit (m x : ℤ) : ℤ :=
  (if x / m % 2 = 0 then 1 else -1) * (4 : ℤ) ^ (x % m).toNat

theorem alternatingDigit_shift (m x : ℤ) (hm : 0 < m) :
    alternatingDigit m (x + m) = -alternatingDigit m x := by
  have hr : (x + m) % m = x % m := Int.add_emod_right x m
  have hq : (x + m) / m = x / m + 1 := by
    rw [Int.add_ediv_of_dvd_right (dvd_refl m), Int.ediv_self (ne_of_gt hm)]
  simp only [alternatingDigit, hr, hq]
  have ht : (x / m + 1) % 2 = 0 ↔ ¬x / m % 2 = 0 := by omega
  by_cases h : x / m % 2 = 0
  · simp [h, ht]
  · simp [h, ht]

def alternatingSum (m : ℤ) (a : Multiset ℤ) : ℤ :=
  (a.map (alternatingDigit m)).sum

theorem alternatingSum_branch (m : ℤ) (hm : 0 < m) (a : Multiset ℤ) :
    alternatingSum m (zbranch a m) = 0 := by
  induction a using Multiset.induction_on with
  | empty => simp [alternatingSum, zbranch, zshift]
  | @cons x a ih =>
    have he : alternatingSum m (zbranch (x ::ₘ a) m) =
        alternatingDigit m x + alternatingDigit m (x + m) +
          alternatingSum m (zbranch a m) := by
      simp [alternatingSum, zbranch, zshift, Multiset.cons_add, Multiset.add_cons]
      ring
    rw [he, ih, alternatingDigit_shift m x hm]
    ring

def alternatingEdge (m d x : ℤ) : ℤ :=
  alternatingDigit m x + alternatingDigit m (x + d)

def alternatingTarget (m : ℤ) : ℤ :=
  ((List.range 109).map (fun i : ℕ => alternatingDigit m i)).sum

/-- Any exact interval placement has this signed fingerprint, with bounded
pair starts. Coincident starts are allowed by this necessary relaxation. -/
theorem interval_placement_alternating (m d s : ℤ) (hm : 0 < m)
    (h : intervalThreePairPlacement m d s) :
    ∃ x y z : ℤ, (0 ≤ x ∧ x + d < 109) ∧ (0 ≤ y ∧ y + d < 109) ∧
      (0 ≤ z ∧ z + d < 109) ∧
      alternatingEdge m d x + alternatingEdge m d y + alternatingEdge m d z +
        alternatingDigit m s = alternatingTarget m := by
  obtain ⟨x, y, z, a, ha⟩ := h
  obtain ⟨_, hb, _, _⟩ := interval_three_pair_bounds m d s x y z a ha
  refine ⟨x, y, z, hb x (by simp), hb y (by simp), hb z (by simp), ?_⟩
  have he := congrArg (alternatingSum m) ha
  have hz := alternatingSum_branch m hm a
  simp only [alternatingSum, Multiset.map_add, Multiset.sum_add] at he
  change alternatingTarget m =
    alternatingSum m (zbranch a m) + alternatingSum m (threePairWeights d x y z s) at he
  rw [hz, zero_add] at he
  simpa [alternatingSum, threePairWeights, zbranch, zshift, alternatingEdge,
    add_assoc, add_left_comm, add_comm] using he.symm

/-- A Boolean classifier for two-edge sums. The soundness theorem below does
not assume that the tree is sorted or that lookup is a correct set operation:
coverage of every possible edge sum is checked explicitly. -/
inductive AlternatingLookup where
  | empty
  | node (pivot : ℤ) (left right : AlternatingLookup)

noncomputable def AlternatingLookup.contains : AlternatingLookup → ℤ → Bool
  | .empty, _ => false
  | .node p l r, x =>
    bif Int.blt' x p then l.contains x else bif Int.beq' x p then true else r.contains x

/-- Candidate finite data, with no assumed mathematical properties. -/
structure AlternatingCertificate where
  edges : List ℤ
  pairs : AlternatingLookup
  singletons : List ℕ
  target : ℤ

/-- Verify edge coverage, coverage of all sums of two edges, and the remaining
edge-plus-singleton test. Extra edges or pair sums only strengthen the checks. -/
noncomputable def checkAlternating (m d : ℤ) (c : AlternatingCertificate) : Bool :=
  (c.target == alternatingTarget m) &&
  ((List.range (109 - d).toNat).all fun x => c.edges.contains (alternatingEdge m d x)) &&
  (c.edges.all fun x => c.edges.all fun y => c.pairs.contains (x + y)) &&
  ((List.range 109).all fun s => c.edges.all fun z =>
    !c.pairs.contains (c.target - z - alternatingDigit m s) ||
      c.singletons.contains s)

/-- Every exact placement's actual singleton survives any accepted certificate.
All finite checks are premises here, and must subsequently pass the kernel. -/
theorem checkAlternating_sound (m d s : ℤ) (c : AlternatingCertificate)
    (hm : 0 < m) (hs : 0 ≤ s ∧ s < 109)
    (hc : checkAlternating m d c = true)
    (hp : intervalThreePairPlacement m d s) : s.toNat ∈ c.singletons := by
  obtain ⟨htarget, hcover, hsums, hsingle⟩ :
      (c.target == alternatingTarget m) = true ∧
      ((List.range (109 - d).toNat).all fun x => c.edges.contains (alternatingEdge m d x)) = true ∧
      (c.edges.all fun x => c.edges.all fun y => c.pairs.contains (x + y)) = true ∧
      ((List.range 109).all fun s => c.edges.all fun z =>
        !c.pairs.contains (c.target - z - alternatingDigit m s) ||
          c.singletons.contains s) = true := by
    simpa only [checkAlternating, Bool.and_eq_true, and_assoc] using hc
  have ht : c.target = alternatingTarget m := by simpa only [beq_iff_eq] using htarget
  have edge_mem (x : ℤ) (hx : 0 ≤ x ∧ x + d < 109) :
      alternatingEdge m d x ∈ c.edges := by
    have hn : x.toNat ∈ List.range (109 - d).toNat := List.mem_range.mpr (by omega)
    have he := List.all_eq_true.mp hcover x.toNat hn
    simpa only [Int.toNat_of_nonneg hx.1, List.contains_iff_mem] using he
  obtain ⟨x, y, z, hx, hy, hz, he⟩ := interval_placement_alternating m d s hm hp
  have hxy := List.all_eq_true.mp (List.all_eq_true.mp hsums _ (edge_mem x hx)) _ (edge_mem y hy)
  have hres : c.target - alternatingEdge m d z - alternatingDigit m s =
      alternatingEdge m d x + alternatingEdge m d y := by omega
  have hsn : s.toNat ∈ List.range 109 := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp (List.all_eq_true.mp hsingle s.toNat hsn) _ (edge_mem z hz)
  simpa only [Int.toNat_of_nonneg hs.1, hres, hxy, Bool.not_true, Bool.false_or,
    List.contains_iff_mem] using hh

open Lean Elab Term

/-- Reify candidate literals as a balanced classifier. This elaborator only
constructs data: coverage and rejection still require kernel reduction. -/
private def alternatingLookupExpr : ℕ → Array Expr → TermElabM Expr
  | 0, _ => throwError "alternating lookup depth exceeded"
  | fuel + 1, xs => do
    if xs.isEmpty then return mkConst ``AlternatingLookup.empty
    let mid := xs.size / 2
    let left ← alternatingLookupExpr fuel (xs.extract 0 mid)
    let right ← alternatingLookupExpr fuel (xs.extract (mid + 1) xs.size)
    return mkApp3 (mkConst ``AlternatingLookup.node) xs[mid]! left right

syntax "alternating_lookup% " str : term

elab_rules : term
  | `(alternating_lookup% $data:str) => do
    let json ← match Json.parse data.getString with
      | .ok x => pure x
      | .error e => throwError "invalid alternating lookup JSON: {e}"
    let xs ← match json.getArr? with
      | .ok x => pure x
      | .error e => throwError "expected alternating lookup array: {e}"
    let values ← xs.mapM fun x => do
      match x.getInt? with
      | .ok n => pure (if n < 0 then
          mkApp (mkConst ``Int.negSucc) (mkNatLit (n.natAbs - 1))
        else mkApp (mkConst ``Int.ofNat) (mkNatLit n.toNat))
      | .error e => throwError "expected alternating lookup integer: {e}"
    alternatingLookupExpr 32 values

end ScholzBrauer.Clift109
