import krylov.XR.MemoryPositive

/-!
Article: main_krylov, proof of thm:grow, finite forgetting of old pairs.
Use: measure the actual old prefix preceding a genuinely good suffix.
Deleting old entries preserves the forgetting potential while a bad entry
remains; appending a new good accepted observation lowers it by one.
Source: elementary chronological-list arithmetic, independent of the model.
-/

namespace krylov.XR
noncomputable section
variable {α : Type*}
local instance goodSuffixDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- Every observation after a physical chronological offset is good. -/
def goodSuffixFrom (Q : α → Prop) (W : List α) (offset : ℕ) : Prop := ∀ a ∈ W.drop offset, Q a

theorem goodSuffixFrom_mono (Q : α → Prop) (W : List α) (i j : ℕ) (hij : i ≤ j)
    (hi : goodSuffixFrom Q W i) : goodSuffixFrom Q W j := by
  intro a ha
  have he : i + (j - i) = j := by omega
  rw [← he, ← List.drop_drop] at ha
  exact hi a (List.mem_of_mem_drop ha)

theorem exists_goodSuffix (Q : α → Prop) (W : List α) : ∃ offset, goodSuffixFrom Q W offset :=
  ⟨W.length, by simp only [goodSuffixFrom, List.drop_length, List.not_mem_nil, IsEmpty.forall_iff, implies_true]⟩

/-- The true number of old entries preceding the longest good suffix. -/
def firstGoodSuffix (Q : α → Prop) (W : List α) : ℕ := Nat.find (exists_goodSuffix Q W)

theorem firstGoodSuffix_spec (Q : α → Prop) (W : List α) :
    goodSuffixFrom Q W (firstGoodSuffix Q W) := Nat.find_spec (exists_goodSuffix Q W)

theorem firstGoodSuffix_le_iff (Q : α → Prop) (W : List α) (j : ℕ) :
    firstGoodSuffix Q W ≤ j ↔ goodSuffixFrom Q W j := by
  constructor
  · intro h
    exact goodSuffixFrom_mono Q W _ j h (firstGoodSuffix_spec Q W)
  · exact Nat.find_min' (exists_goodSuffix Q W)

theorem firstGoodSuffix_le_length (Q : α → Prop) (W : List α) : firstGoodSuffix Q W ≤ W.length :=
  (firstGoodSuffix_le_iff Q W _).2 (by simp [goodSuffixFrom])

theorem firstGoodSuffix_eq_zero_iff (Q : α → Prop) (W : List α) :
    firstGoodSuffix Q W = 0 ↔ ∀ a ∈ W, Q a := by
  rw [← Nat.le_zero, firstGoodSuffix_le_iff]
  simp only [goodSuffixFrom, List.drop_zero]

/-- Dropping old entries subtracts their count from the actual bad prefix. -/
theorem firstGoodSuffix_drop (Q : α → Prop) (W : List α) (offset : ℕ) :
    firstGoodSuffix Q (W.drop offset) = firstGoodSuffix Q W - offset := by
  apply le_antisymm
  · apply (firstGoodSuffix_le_iff Q (W.drop offset) _).2
    change ∀ a ∈ (W.drop offset).drop _, Q a
    rw [List.drop_drop]
    apply (firstGoodSuffix_le_iff Q W _).1
    omega
  · have h := firstGoodSuffix_spec Q (W.drop offset)
    change ∀ a ∈ (W.drop offset).drop _, Q a at h
    rw [List.drop_drop] at h
    have hh := (firstGoodSuffix_le_iff Q W _).2 h
    omega

/-- Appending a genuinely good observed pair leaves the old bad prefix
unchanged, irrespective of the previous good suffix length. -/
theorem firstGoodSuffix_append_good (Q : α → Prop) (W : List α) (a : α) (ha : Q a) :
    firstGoodSuffix Q (W ++ [a]) = firstGoodSuffix Q W := by
  have hiff j : goodSuffixFrom Q (W ++ [a]) j ↔ goodSuffixFrom Q W j := by
    unfold goodSuffixFrom
    rw [List.drop_append]
    constructor
    · intro h b hb
      exact h b (List.mem_append_left _ hb)
    · intro h b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact h b hb
      · have he : b = a := List.mem_singleton.mp (List.mem_of_mem_drop hb)
        simpa only [he] using ha
  apply le_antisymm
  · exact (firstGoodSuffix_le_iff Q (W ++ [a]) _).2 ((hiff _).2 (firstGoodSuffix_spec Q W))
  · exact (firstGoodSuffix_le_iff Q W _).2 ((hiff _).1 (firstGoodSuffix_spec Q (W ++ [a])))

/-- Exact observation transport preserving goodness also preserves the
length of the true old bad prefix. -/
theorem firstGoodSuffix_map (Q : α → Prop) (W : List α) (f : α → α)
    (hf : ∀ a, Q (f a) ↔ Q a) : firstGoodSuffix Q (W.map f) = firstGoodSuffix Q W := by
  have hiff j : goodSuffixFrom Q (W.map f) j ↔ goodSuffixFrom Q W j := by
    unfold goodSuffixFrom
    rw [← List.map_drop]
    constructor
    · intro h a ha
      exact (hf a).mp (h (f a) (List.mem_map_of_mem ha))
    · intro h b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      exact (hf a).mpr (h a ha)
  apply le_antisymm
  · exact (firstGoodSuffix_le_iff Q (W.map f) _).2 ((hiff _).2 (firstGoodSuffix_spec Q W))
  · exact (firstGoodSuffix_le_iff Q W _).2 ((hiff _).1 (firstGoodSuffix_spec Q (W.map f)))

/-- Old bad entries plus unfilled observation slots. The actual window
bound makes this at most the configured pair bound. -/
def forgettingPotential (capacity : ℕ) (Q : α → Prop) (W : List α) : ℕ :=
  firstGoodSuffix Q W + (capacity - W.length)

theorem forgettingPotential_le_capacity (capacity : ℕ) (Q : α → Prop) (W : List α)
    (hlen : W.length ≤ capacity) : forgettingPotential capacity Q W ≤ capacity := by
  have h := firstGoodSuffix_le_length Q W
  unfold forgettingPotential
  omega

/-- Cleanup cannot postpone forgetting while any old bad entry remains. -/
theorem forgettingPotential_drop_of_bad (capacity : ℕ) (Q : α → Prop) (W : List α)
    (hlen : W.length ≤ capacity) (offset : ℕ) (hbad : firstGoodSuffix Q (W.drop offset) ≠ 0) :
    forgettingPotential capacity Q (W.drop offset) = forgettingPotential capacity Q W := by
  have hbadlen := firstGoodSuffix_le_length Q W
  unfold forgettingPotential
  rw [firstGoodSuffix_drop, List.length_drop]
  rw [firstGoodSuffix_drop] at hbad
  omega

/-- A genuine newly accepted good observation consumes one remaining
forgetting slot. -/
theorem forgettingPotential_append_good (capacity : ℕ) (Q : α → Prop) (W : List α)
    (a : α) (ha : Q a) (hlen : W.length < capacity) :
    forgettingPotential capacity Q (W ++ [a]) + 1 = forgettingPotential capacity Q W := by
  unfold forgettingPotential
  rw [firstGoodSuffix_append_good Q W a ha, List.length_append, List.length_singleton]
  omega

theorem forgettingPotential_map (capacity : ℕ) (Q : α → Prop) (W : List α) (f : α → α)
    (hf : ∀ a, Q (f a) ↔ Q a) : forgettingPotential capacity Q (W.map f) = forgettingPotential capacity Q W := by
  simp only [forgettingPotential, firstGoodSuffix_map Q W f hf, List.length_map]

end
end krylov.XR
