import ScholzBrauer.Exclusion
import Lean

namespace ScholzBrauer

/-- Balanced data lookup avoids linear list-backed array access in the kernel.
No ordering invariant is needed for soundness: the checker accepts any lookup. -/
inductive ExclusionTree
  | leaf (node : ExclusionNode)
  | branch (pivot : ℕ) (left right : ExclusionTree)

def ExclusionTree.lookup : ExclusionTree → ℕ → ExclusionNode
  | .leaf node, _ => node
  | .branch pivot left right, id =>
    if id < pivot then left.lookup id else right.lookup id

end ScholzBrauer

/-! Data elaboration only: this syntax emits constructor expressions, which the
kernel type-checks. It neither executes the exclusion checker nor produces proof
terms. Embedded JSON keeps the compiled module independent of external files. -/
open Lean Meta Elab

private def buildExclusionTree (fuel offset : Nat) (xs : Array Expr) : MetaM Expr := do
  match fuel with
  | 0 => throwError "tree depth exceeded"
  | fuel + 1 =>
    if xs.size == 1 then return mkApp (mkConst ``ScholzBrauer.ExclusionTree.leaf) xs[0]!
    let mid := xs.size / 2
    let left ← buildExclusionTree fuel offset (xs.extract 0 mid)
    let right ← buildExclusionTree fuel (offset + mid) (xs.extract mid xs.size)
    return mkApp3 (mkConst ``ScholzBrauer.ExclusionTree.branch) (mkNatLit (offset + mid)) left right

elab "exclusion_tree%" blob:str : term => do
  let text := blob.getString
  let json ← Lean.ofExcept (Json.parse text)
  let nodes ← Lean.ofExcept json.getArr?
  if nodes.isEmpty then throwError "empty exclusion table"
  let nat := mkConst ``Nat
  let pair := mkApp2 (mkConst ``Prod [levelZero, levelZero]) nat nat
  let vals ← nodes.toList.mapM fun node => do
    let arr ← Lean.ofExcept node.getArr?
    unless arr.size == 1 || arr.size == 2 do throwError "invalid node shape"
    let kind ← Lean.ofExcept arr[0]!.getStr?
    if kind == "gap" && arr.size == 1 then return mkConst ``ScholzBrauer.ExclusionNode.gap
    if kind == "bound" && arr.size == 1 then return mkConst ``ScholzBrauer.ExclusionNode.bound
    unless kind == "split" && arr.size == 2 do throwError "invalid node"
    let edges ← Lean.ofExcept arr[1]!.getArr?
    let pairs ← edges.toList.mapM fun edge => do
      let e ← Lean.ofExcept edge.getArr?
      unless e.size == 2 do throwError "invalid edge shape"
      let v ← Lean.ofExcept e[0]!.getNat?
      let i ← Lean.ofExcept e[1]!.getNat?
      return mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) nat nat (mkNatLit v) (mkNatLit i)
    return mkApp (mkConst ``ScholzBrauer.ExclusionNode.split) (← mkListLit pair pairs)
  buildExclusionTree 32 0 vals.toArray
