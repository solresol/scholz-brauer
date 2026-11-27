import ScholzBrauer.Clift109TranslatedExceptions

namespace ScholzBrauer.Clift109

/-- Every point of a translated pair has a partner at distance d. -/
theorem zbranch_has_neighbor (a : Multiset ℤ) (d x : ℤ) (hx : x ∈ zbranch a d) :
    x-d ∈ zbranch a d ∨ x+d ∈ zbranch a d := by
  rcases Multiset.mem_add.mp hx with h | h
  · exact Or.inr (Multiset.mem_add.mpr (.inr (Multiset.mem_map.mpr ⟨x, h, rfl⟩)))
  · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp h
    exact Or.inl (by rw [add_sub_cancel_right]; exact Multiset.mem_add.mpr (.inl hy))

/-- The four sorted dimension sets in this certificate have the form
[1, a, 8, b, 27, e]. The witness is a point left isolated by deletion. -/
structure Isolated827Row where
  a : ℤ
  b : ℤ
  e : ℤ
  t : ℤ
  v : ℤ
  r : ℤ
  s : ℤ
  z : ℤ
  witness : ℤ

def isolated827Rows : List Isolated827Row :=
  [⟨5, 10, 48, 1, 5, 0, 32, 35, 22⟩,
   ⟨5, 10, 48, 1, 48, 0, 75, 35, 21⟩,
   ⟨5, 10, 48, 2, 5, 41, 14, 19, 23⟩,
   ⟨5, 10, 48, 2, 5, 49, 76, 89, 22⟩,
   ⟨5, 10, 48, 2, 48, 6, 33, 89, 23⟩,
   ⟨5, 10, 48, 2, 48, 46, 67, 19, 23⟩,
   ⟨5, 10, 48, 3, 1, 99, 72, 73, 0⟩,
   ⟨5, 10, 48, 3, 5, 95, 68, 73, 0⟩,
   ⟨5, 10, 48, 3, 10, 90, 63, 73, 0⟩,
   ⟨5, 10, 48, 4, 48, 0, 21, 35, 1⟩,
   ⟨5, 10, 48, 5, 48, 52, 79, 73, 1⟩,
   ⟨5, 10, 48, 6, 1, 0, 28, 35, 2⟩,
   ⟨5, 10, 48, 6, 5, 0, 32, 35, 2⟩,
   ⟨5, 10, 48, 6, 10, 0, 37, 35, 2⟩,
   ⟨5, 10, 48, 7, 5, 46, 24, 19, 3⟩,
   ⟨5, 10, 48, 7, 5, 54, 86, 89, 3⟩,
   ⟨5, 10, 48, 7, 48, 6, 33, 89, 3⟩,
   ⟨5, 10, 48, 7, 48, 46, 67, 19, 3⟩,
   ⟨5, 10, 48, 8, 5, 95, 68, 73, 0⟩,
   ⟨5, 10, 48, 8, 48, 52, 25, 73, 0⟩,
   ⟨5, 11, 48, 1, 11, 0, 38, 35, 22⟩,
   ⟨5, 11, 48, 2, 1, 99, 72, 73, 0⟩,
   ⟨5, 11, 48, 2, 5, 95, 68, 73, 0⟩,
   ⟨5, 11, 48, 2, 48, 52, 25, 73, 0⟩,
   ⟨5, 11, 48, 2, 48, 52, 79, 73, 0⟩,
   ⟨5, 11, 48, 6, 1, 0, 28, 35, 3⟩,
   ⟨5, 11, 48, 6, 5, 0, 32, 35, 3⟩,
   ⟨5, 11, 48, 6, 48, 0, 21, 35, 2⟩,
   ⟨5, 11, 48, 6, 48, 0, 75, 35, 3⟩,
   ⟨5, 11, 48, 7, 11, 89, 62, 73, 0⟩,
   ⟨5, 11, 54, 1, 5, 46, 24, 19, 5⟩,
   ⟨5, 11, 54, 1, 5, 46, 24, 73, 5⟩,
   ⟨5, 11, 54, 1, 5, 46, 78, 19, 24⟩,
   ⟨5, 11, 54, 1, 5, 46, 78, 73, 19⟩,
   ⟨5, 11, 54, 1, 5, 49, 22, 35, 3⟩,
   ⟨5, 11, 54, 1, 5, 49, 22, 89, 3⟩,
   ⟨5, 11, 54, 1, 5, 49, 76, 35, 8⟩,
   ⟨5, 11, 54, 1, 5, 49, 76, 89, 22⟩,
   ⟨5, 11, 54, 1, 11, 35, 8, 73, 19⟩,
   ⟨5, 11, 54, 1, 11, 35, 62, 19, 8⟩,
   ⟨5, 11, 54, 1, 11, 35, 62, 73, 8⟩,
   ⟨5, 11, 54, 1, 11, 43, 16, 35, 8⟩,
   ⟨5, 11, 54, 1, 11, 43, 70, 35, 8⟩,
   ⟨5, 11, 54, 1, 11, 43, 70, 89, 16⟩,
   ⟨5, 11, 54, 1, 11, 46, 30, 19, 3⟩,
   ⟨5, 11, 54, 1, 11, 46, 30, 73, 3⟩,
   ⟨5, 11, 54, 1, 11, 46, 84, 73, 19⟩,
   ⟨5, 11, 54, 1, 11, 54, 38, 35, 8⟩,
   ⟨5, 11, 54, 1, 11, 54, 38, 89, 11⟩,
   ⟨5, 11, 54, 1, 11, 54, 92, 35, 8⟩,
   ⟨5, 11, 54, 1, 54, 0, 81, 35, 27⟩,
   ⟨5, 11, 54, 1, 54, 46, 19, 73, 0⟩,
   ⟨6, 11, 48, 1, 1, 99, 72, 73, 0⟩,
   ⟨6, 11, 48, 1, 11, 89, 62, 73, 0⟩,
   ⟨6, 11, 48, 2, 1, 99, 18, 73, 0⟩,
   ⟨6, 11, 48, 2, 1, 99, 72, 73, 0⟩,
   ⟨6, 11, 48, 2, 48, 52, 25, 73, 0⟩,
   ⟨6, 11, 48, 2, 48, 52, 79, 73, 0⟩,
   ⟨6, 11, 48, 5, 1, 0, 28, 35, 3⟩,
   ⟨6, 11, 48, 5, 1, 0, 82, 35, 3⟩,
   ⟨6, 11, 48, 5, 48, 0, 21, 35, 2⟩,
   ⟨6, 11, 48, 5, 48, 0, 75, 35, 3⟩,
   ⟨6, 11, 48, 6, 1, 0, 28, 35, 4⟩,
   ⟨6, 11, 48, 6, 11, 0, 38, 35, 4⟩]

/-- Remainder of the interval after removing the translated box and all seven
exceptions. The rectangle step is independent of the ordering used for zSS. -/
def isolated827Rest (k : Isolated827Row) : Multiset ℤ :=
  let box := zshift (zSS [k.e, k.b, k.a, 27, 8, 1]) k.t
  let exceptions := placedSinkExceptions { sparse827Box with v := k.v } k.r k.s k.z
  (Multiset.range 109).map Int.ofNat - box - exceptions

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem isolated827_witnesses : ∀ k ∈ isolated827Rows,
    k.witness ∈ isolated827Rest k ∧ k.witness-27 ∉ isolated827Rest k ∧
    k.witness+27 ∉ isolated827Rest k := by
  decide +kernel

/-- No unrestricted half exists for any of these 64 fingerprint matches. -/
theorem isolated827_no_half (k : Isolated827Row) (hk : k ∈ isolated827Rows)
    (a : Multiset ℤ) : isolated827Rest k ≠ zbranch a 27 := by
  intro he
  obtain ⟨hx, hlo, hhi⟩ := isolated827_witnesses k hk
  rw [he] at hx hlo hhi
  exact (zbranch_has_neighbor a 27 k.witness hx).elim hlo hhi

/-- An isolated row excludes every assignment of the remaining roles. -/
theorem isolated827_no_interval (c : GaugeCoordinates) (k : Isolated827Row)
    (hk : k ∈ isolated827Rows) (ht : c.t = k.t)
    (hp : [c.d3, c.d2, c.d1, c.w, c.v, c.u].Perm [k.e, k.b, k.a, 27, 8, 1])
    (hu : c.u = 8) (hv : c.v = k.v) (hd : c.d1 = 27)
    (hr : c.A1+c.p = k.r) (hs : c.A2+c.p = k.s) (hz : c.A3+c.p = k.z) :
    coordinateWeights c ≠ (Multiset.range 109).map Int.ofNat := by
  intro hi
  apply isolated827_no_half k hk (sinkHalf c)
  have hb : coordinateBox c = zshift (zSS [k.e, k.b, k.a, 27, 8, 1]) k.t := by
    rw [coordinateBox, ht, zSS_perm hp]
  have he : sinkExceptions c = placedSinkExceptions { sparse827Box with v := k.v } k.r k.s k.z := by
    rw [sinkExceptions_eq_placed, hr, hs, hz]
    simp only [placedSinkExceptions, hu, hv, sparse827Box]
  simp only [isolated827Rest, ← hi, coordinateWeights, hb,
    add_tsub_cancel_left, remainder_sink_factor, he, hd, add_tsub_cancel_right]

end ScholzBrauer.Clift109
