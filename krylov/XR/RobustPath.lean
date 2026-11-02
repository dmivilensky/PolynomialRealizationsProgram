import krylov.XR.RobustRegularizer

/-!
Article: main_krylov, thm:metric, full intermediate robust path.
Use: a radius strictly between the two genuine thresholds has an
attained Tikhonov correction, with exactly the article's scalar norm
equation for its positive regularizer. Source: proved endpoint necessity,
compact attainment, true Fermat optimality and actual matrix inversion.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {p : ℕ}

/-- The literal regularized solve leaves exactly lambda times the
regularized right-hand side as its true residual.
Article: main_krylov, thm:metric, scalar regularizer equation. -/
theorem robust_regularized_residual (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.IsHermitian)
    (rho : EuclideanSpace ℝ (Fin p)) (lambda : ℝ) (hl : 0<lambda) :
    rho+cgOperator N (-(cgOperator (robustRegularizedMatrix N lambda)⁻¹ (cgOperator N rho)))=
      lambda • cgOperator (robustRegularizedMatrix N lambda)⁻¹ rho := by
  let A := robustRegularizedMatrix N lambda
  let v := cgOperator A⁻¹ rho
  have hA : A.PosDef := robustRegularizedMatrix_posDef N hN lambda hl
  have hmatrix : N*A⁻¹=A⁻¹*N := robustRegularizedMatrix_inv_commute N hN lambda hl
  have hcomm : cgOperator N (cgOperator A⁻¹ rho)=cgOperator A⁻¹ (cgOperator N rho) := by
    simp only [cgOperator,←mul_apply_eq_comp,←map_mul,hmatrix]
  have hi : cgOperator A (cgOperator A⁻¹ rho)=rho := by
    simp only [cgOperator,←mul_apply_eq_comp,←map_mul,
      mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),map_one,one_apply_eq_self]
  have hsum : cgOperator N (cgOperator N v)+lambda • v=rho := by
    rw [←robustRegularizedMatrix_action]
    exact hi
  rw [←hcomm,map_neg]
  change rho+ -(cgOperator N (cgOperator N v))=lambda • v
  rw [←hsum]
  abel

/-- At every radius strictly between the actual Newton and zero
thresholds there exists a genuine globally optimal correction with the
printed ordinary Tikhonov inverse and its exact positive scalar equation.
Article: main_krylov, thm:metric, complete intermediate path. -/
theorem robust_tikhonov_path (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (rho : EuclideanSpace ℝ (Fin p)) (hrho : rho≠0) (omega : ℝ)
    (hlo : newtonThreshold N rho<omega) (hhi : omega<zeroThreshold N rho) :
    ∃ lambda : ℝ,0<lambda ∧
      (∀ z : EuclideanSpace ℝ (Fin p),
        robustModelObjective (cgOperator N) rho omega
          (-(cgOperator (robustRegularizedMatrix N lambda)⁻¹ (cgOperator N rho)))≤
        robustModelObjective (cgOperator N) rho omega z) ∧
      ‖cgOperator N (cgOperator (robustRegularizedMatrix N lambda)⁻¹ rho)‖=
        omega*‖cgOperator (robustRegularizedMatrix N lambda)⁻¹ rho‖ := by
  have hn₁ := threshold_action_ne_zero _ hN.inv rho hrho
  have hn₂ := threshold_action_ne_zero _ hN.inv _ hn₁
  have ho : 0<omega := (div_pos (norm_pos_iff.mpr hn₁) (norm_pos_iff.mpr hn₂)).trans hlo
  obtain ⟨b,hmin⟩ := robustModelObjective_exists_minimum (cgOperator N) rho omega ho
  have hb : b≠0 := by
    intro hz
    have hh := hmin
    rw [hz] at hh
    have hbudget := (robust_zeroThreshold_iff N hN rho hrho omega).mp hh
    linarith only [hbudget,hhi]
  have hr : rho+cgOperator N b≠0 := by
    intro hz
    have he := congrArg (cgOperator N⁻¹) hz
    rw [map_add,threshold_inverse_cancel N hN,map_zero] at he
    have hbn : b= -(cgOperator N⁻¹ rho) := eq_neg_of_add_eq_zero_right he
    have hh := hmin
    rw [hbn] at hh
    have hbudget := (robust_newtonThreshold_iff N hN rho hrho omega ho.le).mp hh
    linarith only [hbudget,hlo]
  obtain ⟨lambda,hl,hbalance,hlambda⟩ := robust_interior_regularizer (cgOperator N)
    (cgOperator_positive N hN).1 rho b omega ho hb hr hmin
  have hsolve := robust_regularized_solve N hN.1 rho b lambda hl hbalance
  have hcomm : cgOperator N (cgOperator (robustRegularizedMatrix N lambda)⁻¹ rho)=
      cgOperator (robustRegularizedMatrix N lambda)⁻¹ (cgOperator N rho) := by
    simp only [cgOperator,←mul_apply_eq_comp,←map_mul,robustRegularizedMatrix_inv_commute N hN.1 lambda hl]
  have hsol : b= -(cgOperator N (cgOperator (robustRegularizedMatrix N lambda)⁻¹ rho)) := by
    rw [hcomm]
    exact hsolve
  have hres : rho+cgOperator N b=lambda • cgOperator (robustRegularizedMatrix N lambda)⁻¹ rho := by
    rw [hsolve]
    exact robust_regularized_residual N hN.1 rho lambda hl
  have hnorm : ‖cgOperator N (cgOperator (robustRegularizedMatrix N lambda)⁻¹ rho)‖≠0 := by
    rw [←norm_neg,←hsol]
    exact norm_ne_zero_iff.mpr hb
  have heq := hlambda
  rw [hres,hsol,norm_smul,Real.norm_eq_abs,abs_of_nonneg hl.le,norm_neg] at heq
  have hprod := (eq_div_iff hnorm).mp heq
  refine ⟨lambda,hl,?_,?_⟩
  · rw [←hsolve]
    exact hmin
  · apply mul_left_cancel₀ hl.ne'
    nlinarith only [hprod]

end
end krylov.XR
