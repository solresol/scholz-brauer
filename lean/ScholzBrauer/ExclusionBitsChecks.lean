import ScholzBrauer.ExclusionBits
namespace ScholzBrauer
private noncomputable def bitsSeven : BitContextTree := exclusion_bit_contexts% 0 "[[[1,2,4],4,1,\"gap\",[]],[[1,2],2,2,\"split\",[[4,0]]],[[1],1,3,\"split\",[[2,1]]]]"
theorem bitsSeven_checked : bitsSeven.all (checkBitContext 7 bitsSeven.lookup) = true := by decide +kernel
theorem bitsSeven_lower : 3 < additionChainLength 7 := checkBitContext_lower_bound
  (BitContextTree.all_lookup bitsSeven_checked) (i := 2) (by decide) (by decide) (by decide)
  (additionChainSteps_nonempty (r := 4) [1,2,3,4,7] (by decide) (by decide) (by decide))
-- Fabricating a bit for a missing summand fails the encoding check.
example : checkBitContext 7 bitsSeven.lookup ⟨⟨[1,2],2,2,.split [(4,0)]⟩,14,16⟩ = false := by decide +kernel
-- Fabricating coverage with a bit absent from the edge list also fails.
example : checkBitContext 7 bitsSeven.lookup ⟨⟨[1,2],2,2,.split []⟩,6,16⟩ = false := by decide +kernel
-- Honest encoding of incomplete coverage fails.
example : checkBitContext 7 bitsSeven.lookup ⟨⟨[1,2],2,2,.split []⟩,6,0⟩ = false := by decide +kernel
-- A child that forgets an inherited value is rejected.
example : checkBitContext 7 (fun _ => ⟨⟨[1,4],4,1,.gap⟩,18,0⟩)
    ⟨⟨[1,2],2,2,.split [(4,0)]⟩,6,16⟩ = false := by decide +kernel
-- A child that forgets the new value is rejected independently.
example : checkBitContext 7 (fun _ => ⟨⟨[1,2],4,1,.gap⟩,6,0⟩)
    ⟨⟨[1,2],2,2,.split [(4,0)]⟩,6,16⟩ = false := by decide +kernel
-- A dishonest child encoding is detected by that child's own local check.
example : checkBitContext 7 bitsSeven.lookup ⟨⟨[1,4],4,1,.gap⟩,22,0⟩ = false := by decide +kernel
end ScholzBrauer
