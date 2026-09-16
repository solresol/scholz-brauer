import ScholzBrauer.AdditionChain

/-! Certificates name summand values. The replay checks that both are already present,
then appends their sum only when it exceeds every previous entry. -/
namespace ScholzBrauer

abbrev Step := ℕ × ℕ

def extend (c : List ℕ) (s : Step) : Option (List ℕ) :=
  if s.1 ∈ c ∧ s.2 ∈ c ∧ ∀ x ∈ c, x < s.1 + s.2 then
    some (c ++ [s.1 + s.2])
  else none

def replayFrom (c : List ℕ) : List Step → Option (List ℕ)
  | [] => some c
  | s :: ss => (extend c s).bind (fun d => replayFrom d ss)

def replay (steps : List Step) : Option (List ℕ) := replayFrom [1] steps

theorem append_sum {c : List ℕ} (hc : IsAdditionChain c) {a b : ℕ}
    (ha : a ∈ c) (hb : b ∈ c) (hgt : ∀ x ∈ c, x < a + b) :
    IsAdditionChain (c ++ [a + b]) := by
  refine ⟨?_, ?_, ?_⟩
  · cases c with
    | nil => simp at ha
    | cons x xs => simpa using hc.1
  · exact List.pairwise_append.mpr ⟨hc.2.1, by simp, by simpa using hgt⟩
  · intro x hx hx1
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, z, hz, hsum⟩ := hc.2.2 x hx hx1
      exact ⟨y, List.mem_append_left _ hy, z, List.mem_append_left _ hz, hsum⟩
    · have hxsum : x = a + b := List.mem_singleton.mp hx
      exact ⟨a, List.mem_append_left _ ha, b, List.mem_append_left _ hb, hxsum⟩

theorem extend_sound {c d : List ℕ} {s : Step} (hc : IsAdditionChain c)
    (h : extend c s = some d) : IsAdditionChain d := by
  unfold extend at h
  split at h
  · rename_i hs
    cases Option.some.inj h
    exact append_sum hc hs.1 hs.2.1 hs.2.2
  · contradiction

theorem replayFrom_sound {steps : List Step} {c d : List ℕ}
    (hc : IsAdditionChain c) (h : replayFrom c steps = some d) :
    IsAdditionChain d := by
  induction steps generalizing c with
  | nil =>
    have he : c = d := Option.some.inj h
    exact he ▸ hc
  | cons s ss ih =>
    simp only [replayFrom] at h
    cases he : extend c s with
    | none => simp [he] at h
    | some e =>
      simp [he] at h
      exact ih (extend_sound hc he) h

theorem replay_sound {steps : List Step} {c : List ℕ} (h : replay steps = some c) :
    IsAdditionChain c := replayFrom_sound (by decide : IsAdditionChain [1]) h

theorem extend_length {c d : List ℕ} {s : Step}
    (h : extend c s = some d) : d.length = c.length + 1 := by
  unfold extend at h
  split at h
  · cases Option.some.inj h
    simp
  · contradiction

theorem replayFrom_length {steps : List Step} {c d : List ℕ}
    (h : replayFrom c steps = some d) : d.length = c.length + steps.length := by
  induction steps generalizing c with
  | nil =>
    have he : c = d := Option.some.inj h
    simp [he]
  | cons s ss ih =>
    simp only [replayFrom] at h
    cases he : extend c s with
    | none => simp [he] at h
    | some e =>
      simp [he] at h
      have hi := ih h
      have hl := extend_length he
      simp only [List.length_cons]
      omega

/-- Successful replay performs exactly one addition per supplied step. -/
theorem replay_length {steps : List Step} {c : List ℕ} (h : replay steps = some c) :
    c.length = steps.length + 1 := by
  have hlen := replayFrom_length h
  simpa [Nat.add_comm] using hlen

/-- A checked certificate gives an upper bound, without an optimality claim. -/
theorem certificate_upper_bound {steps : List Step} {c : List ℕ} {n r : ℕ}
    (h : replay steps = some c) (hlast : c.getLast? = some n)
    (hlen : c.length = r + 1) : additionChainLength n ≤ r :=
  additionChainLength_le c (replay_sound h) hlast hlen

/-- The length bound can be obtained directly from the certificate's step count. -/
theorem replay_upper_bound {steps : List Step} {c : List ℕ} {n : ℕ}
    (h : replay steps = some c) (hlast : c.getLast? = some n) :
    additionChainLength n ≤ steps.length :=
  certificate_upper_bound h hlast (replay_length h)

end ScholzBrauer
