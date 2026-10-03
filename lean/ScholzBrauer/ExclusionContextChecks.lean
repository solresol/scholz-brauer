import ScholzBrauer.ExclusionContext
namespace ScholzBrauer
private noncomputable def contextSeven : ContextTree := exclusion_contexts% 0 "[[[1,2,4],4,1,\"gap\",[]],[[1,2],2,2,\"split\",[[4,0]]],[[1],1,3,\"split\",[[2,1]]]]"
theorem contextSeven_checked : contextSeven.all (checkContext 7 contextSeven.lookup) = true := by decide +kernel
theorem contextSeven_lower : 3 < additionChainLength 7 := checkContext_lower_bound
  (ContextTree.all_lookup contextSeven_checked) (i := 2) (by decide) (by decide) (by decide)
  (additionChainSteps_nonempty (r := 4) [1,2,3,4,7] (by decide) (by decide) (by decide))
-- Omitting an inherited summand is rejected, even when the child gap is true.
example : checkContext 7 (fun _ => ⟨[1,4],4,1,.gap⟩)
    ⟨[1,2],2,2,.split [(4,0)]⟩ = false := by decide
-- Omitting the newly added value is independently rejected.
example : checkContext 7 (fun _ => ⟨[1,2],4,1,.gap⟩)
    ⟨[1,2],2,2,.split [(4,0)]⟩ = false := by decide
-- A false widened gap is rejected: the new context contains 3 + 4 = 7.
example : checkContext 7 contextSeven.lookup ⟨[1,2,3,4],4,1,.gap⟩ = false := by decide
-- Wrong child endpoint and nondecreasing budget cannot borrow a true gap.
example : checkContext 7 (fun _ => ⟨[1,2,4],5,1,.gap⟩)
    ⟨[1,2],2,2,.split [(4,0)]⟩ = false := by decide
example : checkContext 7 (fun _ => ⟨[1,2,4],4,2,.gap⟩)
    ⟨[1,2],2,2,.split [(4,0)]⟩ = false := by decide
end ScholzBrauer
