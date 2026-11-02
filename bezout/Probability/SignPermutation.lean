import bezout.Probability.SignProducts

/-!
Article: bezout, Proposition D.1, permutation invariance under iid channel signs.
Use: reordering the actual finite oracle errors preserves their joint probability law.
Proof: coordinate reindexing is a measure-preserving equivalence of the fair product space.
-/

namespace bezout.Probability.SignProducts
noncomputable section
open MeasureTheory

/-- Reorder the actual finite Boolean noise coordinates. -/
def permute {N : ℕ} (e : Equiv.Perm (Fin N)) (ω : Fin N → Bool) : Fin N → Bool :=
  fun s => ω (e s)

/-- An arbitrary permutation preserves the iid fair-sign source law. -/
theorem measurePreserving_permute {N : ℕ} (e : Equiv.Perm (Fin N)) :
    MeasurePreserving (permute e) (Signs.law N) (Signs.law N) := by
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin N => Bool) e.symm :
      (Fin N → Bool) → (Fin N → Bool)) = permute e := by
    funext ω s
    have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : Fin N => Bool) ω (e s)
    simpa only [Equiv.symm_apply_apply, permute] using h
  simpa only [he, Signs.law] using
    measurePreserving_piCongrLeft (fun _ : Fin N => Signs.coin) e.symm

/-- Reordering coordinates leaves every measurable output distribution unchanged. -/
theorem map_permute {N : ℕ} {E : Type*} [MeasurableSpace E]
    (e : Equiv.Perm (Fin N)) (f : (Fin N → Bool) → E) (hf : Measurable f) :
    Measure.map (fun ω => f (permute e ω)) (Signs.law N) = Measure.map f (Signs.law N) := by
  change Measure.map (f ∘ permute e) _ = _
  rw [← Measure.map_map hf (measurePreserving_permute e).measurable,
    (measurePreserving_permute e).map_eq]

end
end bezout.Probability.SignProducts
