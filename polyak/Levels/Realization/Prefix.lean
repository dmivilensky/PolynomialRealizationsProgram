import polyak.Dynamics.Iteration

/-! Article: Appendix E, the finite-dimensional restriction of an actual run.
Use: transport a from-rest prefix through a linear map when the actual
gradients agree at its finitely many visited points. No supplied-gradient
executor replaces the genuine iteration. -/

namespace polyak.Levels.Realization
noncomputable section
open Dynamics

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iterate_prefix_map (T : E→ₗ[ℝ]F) (g : E→E) (h : F→F)
    (α β : ℝ) (x₀ : E) (N : ℕ)
    (hgrad : ∀ k : ℕ,k<N→h (T (iterate g α β x₀ k))=T (g (iterate g α β x₀ k))) :
    ∀ k : ℕ,k≤N→iterate h α β (T x₀) k=T (iterate g α β x₀ k) := by
  have hs : ∀ k : ℕ,k≤N→state h α β (T x₀) k=
      (T (state g α β x₀ k).1,T (state g α β x₀ k).2) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [state,ih (by omega)]
      have hg:=hgrad k (by omega)
      change h (T (state g α β x₀ k).1)=T (g (state g α β x₀ k).1) at hg
      simp only [step,hg,map_sub,map_add,map_smul,state]
  intro k hk
  exact congrArg Prod.fst (hs k hk)

end
end polyak.Levels.Realization
