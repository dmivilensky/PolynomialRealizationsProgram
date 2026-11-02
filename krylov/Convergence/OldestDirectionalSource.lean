import krylov.Convergence.OldestDirectionalModel

/-!
Article: main_krylov, thm:Ip, RFC's correction-angle source estimate.
Use: preserve the actual perpendicular error through the genuine observed
model solve. Source: actual oldest-dual annihilation of the newest probe,
sharp endpoint secant estimates and the true radial gradient remainder.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Secant krylov.LinearAlgebra krylov.Reference krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- A genuine full observed RFC model sees the current error's angular
component in its oldest term. The real latest column is the actual probe. -/
theorem ss1_oldest_perpendicular_source_bound
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ] EuclideanSpace ℝ (Fin (n+2)))
    (S : Set (EuclideanSpace ℝ (Fin (n+2)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈S) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ _) (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (a b : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2))) (x : EuclideanSpace ℝ (Fin (n+2)))
    (ha : ∀ i,a i∈S) (hb : ∀ i,b i∈S) (hx : x∈S)
    {C : ℝ} (hC : 0≤C)
    (hV : IsUnit (windowMatrix (unitWindow (fun i=>b i-a i))).det)
    (hVi : ‖(windowMatrix (unitWindow (fun i=>b i-a i)))⁻¹‖≤C) :
    let s := fun i=>b i-a i
    let y := fun i=>G (b i)-G (a i)
    let V := windowMatrix (unitWindow s)
    let M := inverseCongruence V (ss1Model (unitWindow s) (unitWindowImages s y))
    IsUnit M.det →
    ‖ss1Point s y (G x) x‖≤‖M⁻¹‖*
      ((L:ℝ)/2*(‖a 0‖+‖b 0‖)*C^2*‖quadraticSearchPoint x (s (Fin.last (n+1)))‖+
        (C^2*((n+2:ℕ):ℝ)*((L:ℝ)/2)*newerWindowRadius a b+(L:ℝ)/2*‖x‖)*‖x‖) := by
  dsimp only
  intro hM
  let s := fun i=>b i-a i
  let y := fun i=>G (b i)-G (a i)
  let V := windowMatrix (unitWindow s)
  let X := windowDataError (unitWindow s) (unitWindowImages s y)
  let M := inverseCongruence V (ss1Model (unitWindow s) (unitWindowImages s y))
  have hs (i : Fin (n+2)) : s i≠0 := by
    intro hi
    apply windowMatrix_step_ne_zero (unitWindow s) hV i
    simp only [unitWindow,rescaleWindow,hi,smul_zero]
  have hd : inner ℝ (oldestDual V) (s (Fin.last (n+1)))=0 := by
    have hh := oldestDual_pair_column V hV (Fin.last (n+1))
    rw [ite_eq_right (by exact fun h=>by have hv := congrArg Fin.val h; simp only [Fin.val_last,Fin.val_zero] at hv; omega)] at hh
    change inner ℝ (oldestDual V) (‖s (Fin.last (n+1))‖⁻¹ • s (Fin.last (n+1)))=0 at hh
    rw [real_inner_smul_right] at hh
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr (hs _)))
  have hdiag := source_window_entry_bound G H S hS h₀ hH hH₀ hG a b ha hb hs 0 0
  have hrest := source_window_newer_bound G H S hS h₀ hH hH₀ hG a b ha hb hs
  have haction := oldest_model_perpendicular_action V X x (s (Fin.last (n+1))) hd hC hVi
  have haction' : ‖cgOperator (inverseCongruence V X) x‖≤
      (L:ℝ)/2*(‖a 0‖+‖b 0‖)*C^2*‖quadraticSearchPoint x (s (Fin.last (n+1)))‖+
        C^2*((n+2:ℕ):ℝ)*((L:ℝ)/2)*newerWindowRadius a b*‖x‖ := by
    apply haction.trans
    have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiag (sq_nonneg C))
      (norm_nonneg (quadraticSearchPoint x (s (Fin.last (n+1)))))
    have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrest (sq_nonneg C)) (norm_nonneg x)
    simpa only [max_self,mul_assoc] using add_le_add h₁ h₂
  have hmodel : M-1=inverseCongruence V X := window_model_error _ _ hV
  have hrad := radial_gradient_endpoint_bound G H S hS h₀ hH hG hG₀ x hx
  rw [hH₀,ContinuousLinearMap.id_apply] at hrad
  rw [←ss1Point_rescale s y _ (unitWindow_diagonal_unit s hs)]
  change ‖ss1Point (unitWindow s) (unitWindowImages s y) (G x) x‖≤_
  rw [ss1Point_eq_model_step _ _ _ _ hV]
  have hh := secant_query_action_bound M hM x (G x)
  rw [hmodel] at hh
  apply hh.trans
  have he := mul_le_mul_of_nonneg_left (add_le_add haction' hrad) (norm_nonneg (M⁻¹))
  convert he using 1
  ring

end
end krylov.Convergence
