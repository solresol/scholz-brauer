import ScholzBrauer.ExclusionTree

/-! Exclusion on certified supersets of prefixes. Shared nodes carry the entire
context, endpoint and remaining budget. Every edge checks context inclusion;
node identity alone never justifies reusing an exclusion proof. -/
namespace ScholzBrauer

theorem ChainReach.enlarge {n m r : ℕ} {c d : List ℕ}
    (h : ChainReach n c m r) (hcd : c ⊆ d) : ChainReach n d m r := by
  induction h generalizing d with
  | stop => exact .stop _ _
  | @step c m r a b ha hb hgt hn ih =>
    apply ChainReach.step (hcd ha) (hcd hb) hgt
    apply ih
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (hcd hx)
    · exact List.mem_append_right _ hx

structure ExclusionContext where
  values : List ℕ
  last : ℕ
  remaining : ℕ
  rule : ExclusionNode

/-- Both summands of a viable next value pass this filter, since each is at
most the current endpoint. This avoids quadratic work on irrelevant small values. -/
def activeValues (n : ℕ) (q : ExclusionContext) (k : ℕ) : List ℕ :=
  q.values.filter fun a => decide (n ≤ (a + q.last) * 2 ^ k)

def checkContext (n : ℕ) (lookup : ℕ → ExclusionContext) (q : ExclusionContext) : Bool :=
  (q.last != n) && q.values.all (fun a => decide (a ≤ q.last)) &&
  match q.rule with
  | .invalid => false
  | .bound => decide (q.last * 2 ^ q.remaining < n)
  | .gap => (q.remaining == 1) &&
      (activeValues n q 0).all (fun a =>
        (activeValues n q 0).all (fun b => a + b != n))
  | .split edges =>
    match q.remaining with
    | 0 => false
    | k + 1 =>
      (activeValues n q k).all (fun a => (activeValues n q k).all (fun b =>
        if q.last < a + b ∧ a + b ≤ n ∧ n ≤ (a + b) * 2 ^ k
        then edges.any (fun e => e.1 == a + b) else true)) &&
      edges.all (fun e =>
        let child := lookup e.2
        (child.last == e.1) && (child.remaining == k) &&
        decide (q.values.Sublist child.values) && child.values.contains e.1)

theorem mem_activeValues {n k a b : ℕ} {q : ExclusionContext}
    (ha : a ∈ q.values) (hb : b ≤ q.last) (hn : n ≤ (a + b) * 2 ^ k) :
    a ∈ activeValues n q k := by
  apply List.mem_filter.mpr
  exact ⟨ha, decide_eq_true (le_trans hn (Nat.mul_le_mul_right _ (Nat.add_le_add_left hb _)))⟩

/-- All contexts may be checked independently. The remaining budget, not node
order or a trusted evaluator, supplies the induction for sound reuse. -/
theorem checkContext_sound {n : ℕ} {lookup : ℕ → ExclusionContext}
    (hall : ∀ i, checkContext n lookup (lookup i) = true) (i : ℕ) :
    ¬ ChainReach n (lookup i).values (lookup i).last (lookup i).remaining := by
  suffices h : ∀ r i, (lookup i).remaining = r →
      ¬ ChainReach n (lookup i).values (lookup i).last r from h _ i rfl
  intro r
  induction r with
  | zero =>
    intro i hi hr
    have hcheck := hall i
    simp only [checkContext, Bool.and_eq_true, bne_iff_ne] at hcheck
    have hne := hcheck.1.1
    cases hr with
    | stop => exact hne rfl
  | succ k ih =>
    intro i hi hr
    have hcheck := hall i
    simp only [checkContext, Bool.and_eq_true, List.all_eq_true, bne_iff_ne,
      decide_eq_true_eq] at hcheck
    obtain ⟨⟨hne, hmax⟩, hcheck⟩ := hcheck
    cases hnode : (lookup i).rule with
    | invalid => simp [hnode] at hcheck
    | bound =>
      have hh : (lookup i).last * 2 ^ (k + 1) < n := by simpa [hnode, hi] using hcheck
      have := hr.doubling_bound hmax
      omega
    | gap =>
      have hh : (lookup i).remaining = 1 ∧
          ∀ a ∈ activeValues n (lookup i) 0,
          ∀ b ∈ activeValues n (lookup i) 0, a + b ≠ n := by
        simpa [hnode, List.all_eq_true] using hcheck
      have hk : k = 0 := by omega
      subst k
      cases hr with
      | stop => exact hne rfl
      | @step _ _ _ a b ha hb hgt hn =>
        cases hn with
        | stop =>
          apply hh.2 a (mem_activeValues ha (hmax b hb) (by simp))
            b (mem_activeValues hb (hmax a ha) (by simp [Nat.add_comm])) rfl
    | split edges =>
      simp only [hnode, hi, Bool.and_eq_true, List.all_eq_true] at hcheck
      cases hr with
      | stop => exact hne rfl
      | @step _ _ _ a b ha hb hgt hn =>
        have hnext : ∀ x ∈ (lookup i).values ++ [a + b], x ≤ a + b := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact le_trans (hmax x hx) (Nat.le_of_lt hgt)
          · exact le_of_eq (List.mem_singleton.mp hx)
        have hbound := hn.doubling_bound hnext
        have hcover := hcheck.1 a (mem_activeValues ha (hmax b hb) hbound)
          b (mem_activeValues hb (hmax a ha) (by simpa [Nat.add_comm] using hbound))
        rw [if_pos ⟨hgt, hn.endpoint_le, hbound⟩] at hcover
        obtain ⟨e, he, hv⟩ := (show ∃ e ∈ edges, e.1 = a + b from by
          simpa only [List.any_eq_true, beq_iff_eq] using hcover)
        have hchild := hcheck.2 e he
        simp only [beq_iff_eq, decide_eq_true_eq,
          List.contains_iff_mem] at hchild
        obtain ⟨⟨⟨hm, hr⟩, hs⟩, hv'⟩ := hchild
        apply ih e.2 hr
        rw [hm, hv]
        apply hn.enlarge
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hs.subset hx
        · have hx' := List.mem_singleton.mp hx
          simpa [hx', hv] using hv'

/-- An accepted abstract root excludes every actual chain starting at one. -/
theorem checkContext_lower_bound {n r i : ℕ} {lookup : ℕ → ExclusionContext}
    (hall : ∀ j, checkContext n lookup (lookup j) = true)
    (hseed : 1 ∈ (lookup i).values) (hlast : (lookup i).last = 1)
    (hsteps : (lookup i).remaining = r)
    (hne : (additionChainSteps n).Nonempty) : r < additionChainLength n := by
  by_contra! hle
  obtain ⟨c, hc, hn, hlen⟩ := Nat.sInf_mem hne
  have hlen' : c.length - 1 ≤ r := by
    change c.length = additionChainLength n + 1 at hlen
    omega
  have hr := ((additionChain_reaches hc hn).mono hlen').enlarge
    (show [1] ⊆ (lookup i).values by simpa using hseed)
  have hno := checkContext_sound hall i
  rw [hlast, hsteps] at hno
  exact hno hr

/-- Every leaf is a complete abstract state; balanced lookup affects only cost. -/
inductive ContextTree
  | leaf (context : ExclusionContext)
  | branch (pivot : ℕ) (left right : ContextTree)

def ContextTree.lookup : ContextTree → ℕ → ExclusionContext
  | .leaf q, _ => q
  | .branch p l r, i => if i < p then l.lookup i else r.lookup i

def ContextTree.all (p : ExclusionContext → Bool) : ContextTree → Bool
  | .leaf q => p q
  | .branch _ l r => l.all p && r.all p

theorem ContextTree.all_branch {l r : ContextTree} {pivot : ℕ} {p : ExclusionContext → Bool}
    (hl : l.all p = true) (hr : r.all p = true) :
    (ContextTree.branch pivot l r).all p = true := by
  simpa only [all, Bool.and_eq_true] using And.intro hl hr

theorem ContextTree.all_lookup {t : ContextTree} {p : ExclusionContext → Bool}
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

private def contextTreeExpr (fuel offset : Nat) (xs : List Expr) : MetaM Expr := do
  match fuel, xs with
  | 0, _ => throwError "context tree depth exceeded"
  | _ + 1, [] => throwError "empty context chunk"
  | _ + 1, [q] => return mkApp (mkConst ``ScholzBrauer.ContextTree.leaf) q
  | fuel + 1, _ =>
    let mid := xs.length / 2
    let l ← contextTreeExpr fuel offset (xs.take mid)
    let r ← contextTreeExpr fuel (offset + mid) (xs.drop mid)
    return mkApp3 (mkConst ``ScholzBrauer.ContextTree.branch) (mkNatLit (offset + mid)) l r

elab "exclusion_contexts%" offset:num blob:str : term => do
  let json ← Lean.ofExcept (Json.parse blob.getString)
  let records ← Lean.ofExcept json.getArr?
  let nat := mkConst ``Nat
  let pair := mkApp2 (mkConst ``Prod [levelZero, levelZero]) nat nat
  let contexts ← records.toList.mapM fun record => do
    let fields ← Lean.ofExcept record.getArr?
    unless fields.size == 5 do throwError "invalid context shape"
    let values ← Lean.ofExcept fields[0]!.getArr?
    let vals ← values.toList.mapM fun v => return mkNatLit (← Lean.ofExcept v.getNat?)
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
    return mkApp4 (mkConst ``ScholzBrauer.ExclusionContext.mk)
      (← mkListLit nat vals) (mkNatLit last) (mkNatLit remaining) rule
  contextTreeExpr 32 offset.getNat contexts
