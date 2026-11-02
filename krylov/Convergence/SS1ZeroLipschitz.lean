import krylov.Convergence.OldestWindowSource

/-!
Article: main_krylov, thm:Ip, zero Lipschitz allowance.
Use: include the exact quadratic source case in the literal sharp estimate.
Source: the genuine secant source bound proves both inverse existence and
an exactly zero query, without dividing by a zero regularity constant.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- An actual identity-Hessian source with zero Lipschitz allowance is
solved exactly by any genuine independent full observed secant window. -/
theorem ss1Point_eq_zero_of_zero_lipschitz
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin n))∈S) (hH : LipschitzOnWith 0 H S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ _) (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (a b : Fin n → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (ha : ∀ i,a i∈S) (hb : ∀ i,b i∈S) (hx : x∈S)
    (hV : IsUnit (windowMatrix (unitWindow (fun i=>b i-a i))).det) :
    ss1Point (fun i=>b i-a i) (fun i=>G (b i)-G (a i)) (G x) x=0 := by
  let r := sourceWindowRadius a b+‖x‖
  let C := ‖(windowMatrix (unitWindow (fun i=>b i-a i)))⁻¹‖
  have hr : 0≤r := add_nonneg (sourceWindowRadius_nonneg _ _) (norm_nonneg _)
  have hrad (i : Fin n) : ‖a i‖+‖b i‖≤r := by
    apply (Finset.single_le_sum (fun j _=>add_nonneg (norm_nonneg (a j)) (norm_nonneg (b j)))
      (Finset.mem_univ i)).trans
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hh := ss1_local_step_bound G H S hS h₀ hH hH₀ hG hG₀ a b x ha hb hx hr (norm_nonneg _)
    (fun i=>(le_add_of_nonneg_right (norm_nonneg _)).trans (hrad i))
    (fun i=>(le_add_of_nonneg_left (norm_nonneg _)).trans (hrad i))
    (le_add_of_nonneg_left (sourceWindowRadius_nonneg _ _)) hV (le_refl C) (by norm_num)
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [NNReal.coe_zero,mul_zero,zero_mul] using hh) (norm_nonneg _)

end
end krylov.Convergence
