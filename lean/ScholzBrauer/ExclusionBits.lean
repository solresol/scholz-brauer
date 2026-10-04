import ScholzBrauer.ExclusionContext
namespace ScholzBrauer
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
set_option Elab.async false
/-- Exact finite-set encoding; membership is characterised below. -/
def valueBits : List Nat → Nat
| [] => 0
| v::vs => (2^v) ||| valueBits vs
structure BitContext where
 q : ExclusionContext
 mask : Nat
 edgeMask : Nat
def checkBitContext (n : Nat) (lookup : Nat → BitContext) (s : BitContext) : Bool :=
 (valueBits s.q.values == s.mask) && (s.q.last != n) &&
 s.q.values.all (fun a => decide (a ≤ s.q.last)) &&
 match s.q.rule with
 | .invalid => false
 | .bound => decide (s.q.last * 2^s.q.remaining < n)
 | .gap => (s.q.remaining == 1) &&
   (activeValues n s.q 0).all (fun a => !s.mask.testBit (n-a))
 | .split edges =>
   match s.q.remaining with
   | 0 => false
   | k+1 =>
     (valueBits (edges.map Prod.fst) == s.edgeMask) &&
     (activeValues n s.q k).all (fun a => (activeValues n s.q k).all (fun b =>
       if s.q.last < a+b ∧ a+b ≤ n ∧ n ≤ (a+b)*2^k
       then s.edgeMask.testBit (a+b) else true)) &&
     edges.all (fun e =>
       let child := lookup e.2
       (child.q.last == e.1) && (child.q.remaining == k) &&
       ((s.mask &&& child.mask) == s.mask) && child.mask.testBit e.1)

@[simp] theorem testBit_valueBits (vs : List Nat) (v : Nat) :
    (valueBits vs).testBit v = true ↔ v ∈ vs := by
  induction vs with
  | nil => simp [valueBits]
  | cons a vs ih =>
    simp only [valueBits, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

theorem mem_of_bits_subset {vs ws : List Nat} {v : Nat}
    (h : (valueBits vs &&& valueBits ws) = valueBits vs) (hv : v ∈ vs) : v ∈ ws := by
  have ht := congrArg (fun b : Nat => b.testBit v) h
  have ha := (testBit_valueBits vs v).mpr hv
  change (valueBits vs &&& valueBits ws).testBit v = (valueBits vs).testBit v at ht
  simp only [Nat.testBit_and, ha, Bool.true_and] at ht
  exact (testBit_valueBits ws v).mp (by simpa using ht)

/-- Each accepted state verifies its own bit encoding; child bit sets are
trusted only after using the same acceptance hypothesis for that child. -/
theorem checkBitContext_sound {n : ℕ} {lookup : ℕ → BitContext}
    (hall : ∀ i, checkBitContext n lookup (lookup i) = true) (i : ℕ) :
    ¬ ChainReach n (lookup i).q.values (lookup i).q.last (lookup i).q.remaining := by
  have hbits (j : ℕ) : valueBits (lookup j).q.values = (lookup j).mask := by
    have hc := hall j
    simp only [checkBitContext, Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1.1.1
  suffices h : ∀ r i, (lookup i).q.remaining = r →
      ¬ ChainReach n (lookup i).q.values (lookup i).q.last r from h _ i rfl
  intro r
  induction r with
  | zero =>
    intro i hi hr
    have hcheck := hall i
    simp only [checkBitContext, Bool.and_eq_true, bne_iff_ne] at hcheck
    have hne := hcheck.1.1.2
    cases hr with
    | stop => exact hne rfl
  | succ k ih =>
    intro i hi hr
    have hcheck := hall i
    simp only [checkBitContext, Bool.and_eq_true, List.all_eq_true, bne_iff_ne,
      decide_eq_true_eq] at hcheck
    obtain ⟨⟨⟨_, hne⟩, hmax⟩, hcheck⟩ := hcheck
    cases hnode : (lookup i).q.rule with
    | invalid => simp [hnode] at hcheck
    | bound =>
      have hh : (lookup i).q.last * 2 ^ (k + 1) < n := by simpa [hnode, hi] using hcheck
      have := hr.doubling_bound hmax
      omega
    | gap =>
      have hh : (lookup i).q.remaining = 1 ∧
          ∀ a ∈ activeValues n (lookup i).q 0,
          (lookup i).mask.testBit (n-a) = false := by
        simpa [hnode, List.all_eq_true] using hcheck
      have hk : k = 0 := by omega
      subst k
      cases hr with
      | stop => exact hne rfl
      | @step _ _ _ a b ha hb hgt hn =>
        cases hn with
        | stop =>
          have hf := hh.2 a (mem_activeValues ha (hmax b hb) (by simp))
          have ht := (testBit_valueBits (lookup i).q.values b).mpr hb
          rw [← hbits i, Nat.add_sub_cancel_left] at hf
          exact Bool.false_ne_true (hf.symm.trans ht)
    | split edges =>
      simp only [hnode, hi, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hcheck
      obtain ⟨⟨hedge, hcover⟩, hchildren⟩ := hcheck
      cases hr with
      | stop => exact hne rfl
      | @step _ _ _ a b ha hb hgt hn =>
        have hnext : ∀ x ∈ (lookup i).q.values ++ [a + b], x ≤ a + b := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact le_trans (hmax x hx) (Nat.le_of_lt hgt)
          · exact le_of_eq (List.mem_singleton.mp hx)
        have hbound := hn.doubling_bound hnext
        have hc := hcover a (mem_activeValues ha (hmax b hb) hbound)
          b (mem_activeValues hb (hmax a ha) (by simpa [Nat.add_comm] using hbound))
        rw [if_pos ⟨hgt, hn.endpoint_le, hbound⟩, ← hedge] at hc
        have hm := (testBit_valueBits (edges.map Prod.fst) (a+b)).mp hc
        obtain ⟨e, he, hv⟩ := List.mem_map.mp hm
        have hchild := hchildren e he
        obtain ⟨⟨⟨hm, hr⟩, hs⟩, hv'⟩ := hchild
        rw [← hbits i, ← hbits e.2] at hs
        rw [← hbits e.2] at hv'
        apply ih e.2 hr
        rw [hm, hv]
        apply hn.enlarge
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact mem_of_bits_subset hs hx
        · have hx' := List.mem_singleton.mp hx
          have hm := (testBit_valueBits (lookup e.2).q.values e.1).mp hv'
          simpa [hx', hv] using hm

/-- Transfer the bit-checked root exclusion to the upstream minimum length. -/
theorem checkBitContext_lower_bound {n r i : ℕ} {lookup : ℕ → BitContext}
    (hall : ∀ j, checkBitContext n lookup (lookup j) = true)
    (hseed : 1 ∈ (lookup i).q.values) (hlast : (lookup i).q.last = 1)
    (hsteps : (lookup i).q.remaining = r)
    (hne : (additionChainSteps n).Nonempty) : r < additionChainLength n := by
  by_contra! hle
  obtain ⟨c, hc, hn, hlen⟩ := Nat.sInf_mem hne
  have hlen' : c.length - 1 ≤ r := by
    change c.length = additionChainLength n + 1 at hlen
    omega
  have hr := ((additionChain_reaches hc hn).mono hlen').enlarge
    (show [1] ⊆ (lookup i).q.values by simpa using hseed)
  have hno := checkBitContext_sound hall i
  rw [hlast, hsteps] at hno
  exact hno hr

/-- Every leaf is a complete abstract state; balanced lookup affects only cost. -/
inductive BitContextTree
  | leaf (context : BitContext)
  | branch (pivot : ℕ) (left right : BitContextTree)

def BitContextTree.lookup : BitContextTree → ℕ → BitContext
  | .leaf q, _ => q
  | .branch p l r, i => if i < p then l.lookup i else r.lookup i

def BitContextTree.all (p : BitContext → Bool) : BitContextTree → Bool
  | .leaf q => p q
  | .branch _ l r => l.all p && r.all p

theorem BitContextTree.all_branch {l r : BitContextTree} {pivot : ℕ} {p : BitContext → Bool}
    (hl : l.all p = true) (hr : r.all p = true) :
    (BitContextTree.branch pivot l r).all p = true := by
  simpa only [all, Bool.and_eq_true] using And.intro hl hr

theorem BitContextTree.all_lookup {t : BitContextTree} {p : BitContext → Bool}
    (h : t.all p = true) (i : ℕ) : p (t.lookup i) = true := by
  induction t with
  | leaf q => exact h
  | branch pivot l r il ir =>
    have hh : l.all p = true ∧ r.all p = true := by simpa only [all, Bool.and_eq_true] using h
    obtain ⟨hl, hr⟩ := hh
    simp only [lookup]
    split
    · exact il hl
    · exact ir hr

end ScholzBrauer

/-! Data-only elaboration; acceptance and all proof terms are kernel checked. -/
open Lean Meta Elab

private def bitContextTreeExpr (fuel offset : Nat) (xs : List Expr) : MetaM Expr := do
  match fuel, xs with
  | 0, _ => throwError "context tree depth exceeded"
  | _ + 1, [] => throwError "empty context chunk"
  | _ + 1, [q] => return mkApp (mkConst ``ScholzBrauer.BitContextTree.leaf) q
  | fuel + 1, _ =>
    let mid := xs.length / 2
    let l ← bitContextTreeExpr fuel offset (xs.take mid)
    let r ← bitContextTreeExpr fuel (offset + mid) (xs.drop mid)
    return mkApp3 (mkConst ``ScholzBrauer.BitContextTree.branch) (mkNatLit (offset + mid)) l r

elab "exclusion_bit_contexts%" offset:num blob:str : term => do
  let json ← Lean.ofExcept (Json.parse blob.getString)
  let records ← Lean.ofExcept json.getArr?
  let nat := mkConst ``Nat
  let pair := mkApp2 (mkConst ``Prod [levelZero, levelZero]) nat nat
  let contexts ← records.toList.mapM fun record => do
    let fields ← Lean.ofExcept record.getArr?
    unless fields.size == 5 do throwError "invalid context shape"
    let values ← Lean.ofExcept fields[0]!.getArr?
    let naturals ← values.toList.mapM fun v => Lean.ofExcept v.getNat?
    let vals := naturals.map mkNatLit
    let mask := naturals.foldl (fun bits v => bits ||| 2^v) 0
    let last ← Lean.ofExcept fields[1]!.getNat?
    let remaining ← Lean.ofExcept fields[2]!.getNat?
    let kind ← Lean.ofExcept fields[3]!.getStr?
    let edges ← Lean.ofExcept fields[4]!.getArr?
    let rule ← if kind == "gap" && edges.isEmpty then pure (mkConst ``ScholzBrauer.ExclusionNode.gap)
      else if kind == "bound" && edges.isEmpty then pure (mkConst ``ScholzBrauer.ExclusionNode.bound)
      else if kind == "split" then do
        let pairs ← edges.toList.mapM fun edge => do
          let e ← Lean.ofExcept edge.getArr?
          unless e.size == 2 do throwError "invalid edge"
          let v ← Lean.ofExcept e[0]!.getNat?
          let i ← Lean.ofExcept e[1]!.getNat?
          return mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) nat nat (mkNatLit v) (mkNatLit i)
        pure (mkApp (mkConst ``ScholzBrauer.ExclusionNode.split) (← mkListLit pair pairs))
      else throwError "invalid rule"
    let edgeValues ← edges.toList.mapM fun edge => do
      let e ← Lean.ofExcept edge.getArr?
      Lean.ofExcept e[0]!.getNat?
    let edgeMask := edgeValues.foldl (fun bits v => bits ||| 2^v) 0
    let q := mkApp4 (mkConst ``ScholzBrauer.ExclusionContext.mk)
      (← mkListLit nat vals) (mkNatLit last) (mkNatLit remaining) rule
    return mkApp3 (mkConst ``ScholzBrauer.BitContext.mk) q (mkNatLit mask) (mkNatLit edgeMask)
  bitContextTreeExpr 32 offset.getNat contexts
