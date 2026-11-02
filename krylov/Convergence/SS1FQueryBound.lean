import krylov.Convergence.SS1FModel
import krylov.Convergence.SS1LocalBounds

/-!
Article: main_krylov, thm:ss1F.
Use: transport a proved error of the actual observed corrected matrix to
the actual physical query. The model inverse domain is a conclusion of
smallness. Source leaves derive the data and gradient budgets independently.
Source: exact observed normalization and the actual model-step identity.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.Functions krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A proved small error of the genuine normalized observed matrix gives
both the true inverse domain and the actual SS1-F query bound. -/
theorem ss1F_normalized_query_bound (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a s : Fin n → EuclideanSpace ℝ (Fin n)) (l : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hs : ∀ i,s i≠0)
    (hV : IsUnit (windowMatrix (unitWindow s)).det)
    {C ε γ : ℝ} (hC : 0≤C)
    (hinv : ‖(windowMatrix (unitWindow s))⁻¹‖≤C)
    (hdata : ‖ss1FNormalizedError f G a s l‖≤ε)
    (hsmall : C^2*ε≤1/2) (hgrad : ‖G x-x‖≤γ*‖x‖) :
    let M := inverseCongruence (windowMatrix (unitWindow s)) (ss1FNormalizedModel f G a s l)
    IsUnit M.det ∧‖ss1FPoint f G a s l x‖≤2*(C^2*ε+γ)*‖x‖ := by
  dsimp only
  let M := inverseCongruence (windowMatrix (unitWindow s)) (ss1FNormalizedModel f G a s l)
  have herror : ‖M-1‖≤C^2*ε := by
    rw [ss1F_normalized_model_error _ _ _ _ _ hV]
    exact (inverseCongruence_norm _ _).trans
      ((mul_le_mul (sq_le_sq₀ (norm_nonneg _) hC |>.mpr hinv) hdata
        (norm_nonneg _) (sq_nonneg _)))
  have hdomain := secant_inverse_norm_le_two M (herror.trans hsmall)
  refine ⟨hdomain.1,?_⟩
  rw [ss1FPoint_normalized_model _ _ _ _ _ _ hs hV]
  apply (secant_query_error_bound M hdomain.1 x (G x)).trans
  calc
    _ ≤ 2*((C^2*ε)*‖x‖+γ*‖x‖) :=
      mul_le_mul hdomain.2 (add_le_add (mul_le_mul_of_nonneg_right herror (norm_nonneg _)) hgrad)
        (add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

end
end krylov.Convergence
