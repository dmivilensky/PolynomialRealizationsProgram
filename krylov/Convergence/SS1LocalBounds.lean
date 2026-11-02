import krylov.Convergence.SecantWindowSource

/-!
Article: main_krylov, lem:ss1-local and thm:Ip.
Use: a quantitative estimate for the actual data-only SS1 query. Local
gradient and model estimates are derived from the genuine Hessian; smallness
also proves the actual inverse domain.
Source: Appendix G, actual normalized multipoint secant error and radial FTC.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Secant krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The genuine model query is controlled by its actual operator error and
the actual gradient's deviation from the limiting radial model. -/
theorem secant_query_error_bound (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsUnit M.det) (x g : EuclideanSpace ℝ (Fin n)) :
    ‖x-cgOperator M⁻¹ g‖≤‖M⁻¹‖*(‖M-1‖*‖x‖+‖g-x‖) := by
  have hcancel : cgOperator M⁻¹ (cgOperator M x)=x := by
    change (Matrix.toEuclideanCLM (𝕜:=ℝ) M⁻¹)
      ((Matrix.toEuclideanCLM (𝕜:=ℝ) M) x)=x
    rw [←mul_apply_eq_comp,←map_mul,Matrix.nonsing_inv_mul _ hM,map_one]
    rfl
  have he : x-cgOperator M⁻¹ g=
      cgOperator M⁻¹ (cgOperator (M-1) x-(g-x)) := by
    have hm : cgOperator (M-1) x=cgOperator M x-x := by
      simp only [cgOperator,map_sub,map_one,_root_.sub_apply,one_apply_eq_self]
    rw [hm,show cgOperator M x-x-(g-x)=cgOperator M x-g by abel,map_sub,hcancel]
  rw [he]
  have houter := (cgOperator M⁻¹).le_opNorm (cgOperator (M-1) x-(g-x))
  have hinner := (norm_sub_le (cgOperator (M-1) x) (g-x)).trans
    (add_le_add ((cgOperator (M-1)).le_opNorm x) le_rfl)
  simp only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] at houter hinner
  exact houter.trans (mul_le_mul_of_nonneg_left hinner (norm_nonneg _))

/-- The printed local contraction estimate for a real SS1 query. All old
anchors, new endpoints, and the current point lie in the specified radius.
The actual inverse domain is obtained from the source radius condition. -/
theorem ss1_local_step_bound
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin n))∈S) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (a b : Fin n → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (ha : ∀ i,a i∈S) (hb : ∀ i,b i∈S) (hx : x∈S)
    {r C : ℝ} (hr : 0≤r) (hC : 0≤C)
    (har : ∀ i,‖a i‖≤r) (hbr : ∀ i,‖b i‖≤r) (hxr : ‖x‖≤r)
    (hind : IsUnit (windowMatrix (unitWindow (fun i=>b i-a i))).det)
    (hinv : ‖(windowMatrix (unitWindow (fun i=>b i-a i)))⁻¹‖≤C)
    (hsmall : C^2*(n*((L:ℝ)*r))≤1/2) :
    ‖ss1Point (fun i=>b i-a i) (fun i=>G (b i)-G (a i)) (G x) x‖≤
      2*(L:ℝ)*r*(1+n*C^2)*‖x‖ := by
  let s := fun i=>b i-a i
  let y := fun i=>G (b i)-G (a i)
  let V := windowMatrix (unitWindow s)
  let M := inverseCongruence V (ss1Model (unitWindow s) (unitWindowImages s y))
  have hs (i : Fin n) : s i≠0 := by
    intro hi
    have hh := windowMatrix_step_ne_zero (unitWindow s) hind i
    apply hh
    simp only [unitWindow,rescaleWindow,hi,smul_zero]
  have he (i : Fin n) : ‖unitWindowImages s y i-unitWindow s i‖≤(L:ℝ)*r := by
    apply unitWindow_image_error _ _ hs
    intro j
    have hh := secant_image_endpoint_bound G H S hS h₀ hH hG (a j) (b j) (ha j) (hb j)
    rw [hH₀,ContinuousLinearMap.id_apply] at hh
    have hp : (L:ℝ)/2*(‖a j‖+‖b j‖)≤(L:ℝ)*r := by
      nlinarith [har j,hbr j,L.coe_nonneg]
    exact hh.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  have hmodel : ‖M-1‖≤C^2*(n*((L:ℝ)*r)) := by
    have hh := window_model_norm_bound (unitWindow s) (unitWindowImages s y) hind
      (unitWindow_norm s hs) (mul_nonneg L.coe_nonneg hr) he
    exact hh.trans (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) hC).mpr hinv) (by positivity))
  have hdomain := secant_inverse_norm_le_two M (hmodel.trans hsmall)
  have hgrad := radial_gradient_endpoint_bound G H S hS h₀ hH hG hG₀ x hx
  rw [hH₀,ContinuousLinearMap.id_apply] at hgrad
  have hgr : ‖G x-x‖≤(L:ℝ)/2*r*‖x‖ := hgrad.trans (by
    rw [pow_two]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hxr (norm_nonneg x)) (show 0≤(L:ℝ)/2 by positivity))
  rw [←ss1Point_rescale s y (fun i=>‖s i‖⁻¹) (unitWindow_diagonal_unit s hs) (G x) x]
  change ‖ss1Point (unitWindow s) (unitWindowImages s y) (G x) x‖≤_
  rw [ss1Point_eq_model_step _ _ _ _ hind]
  have hh := secant_query_error_bound M hdomain.1 x (G x)
  apply hh.trans
  calc
    _ ≤ 2*(C^2*(n*((L:ℝ)*r))*‖x‖+(L:ℝ)/2*r*‖x‖) :=
      mul_le_mul hdomain.2 (add_le_add (mul_le_mul_of_nonneg_right hmodel (norm_nonneg _)) hgr)
        (add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) (by norm_num)
    _ ≤ _ := by
      have hp : 0≤(L:ℝ)*r*‖x‖ := mul_nonneg (mul_nonneg L.coe_nonneg hr) (norm_nonneg x)
      nlinarith only [hp]

end
end krylov.Convergence
