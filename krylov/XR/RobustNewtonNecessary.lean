import krylov.XR.RobustNewton

/-!
Article: main_krylov, thm:metric, necessity of the Newton threshold.
Use: a genuine global minimizer at the exact inverse solve forces the
printed inverse-norm threshold. Source: true one-sided directional
differentiation at the zero-residual branch, not a postulated subgradient.
-/
namespace krylov.XR
noncomputable section
open Set Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual scalar norm along a physical affine line has its true
directional derivative. Article: thm:metric. -/
theorem robust_norm_line_deriv (b h : E) (hb : b≠0) :
    HasDerivAt (fun t : ℝ=>‖b+t • h‖) (inner ℝ b h/‖b‖) 0 := by
  have hl : HasDerivAt (fun t : ℝ=>b+t • h) h 0 := by
    convert (hasDerivAt_const (0:ℝ) b).add ((hasDerivAt_id 0).smul_const h) using 1
    · rfl
    · simp only [zero_add,one_smul]
  have hv : b+(0:ℝ) • h≠0 := by simpa only [zero_smul,add_zero] using hb
  have hh := (robust_hasFDerivAt_norm _ hv).comp_hasDerivAt 0 hl
  convert hh using 1
  · rfl
  · simp only [zero_smul,add_zero,_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,
      div_eq_mul_inv,mul_comm]

/-- Global optimality of the literal inverse correction forces the
actual norm-ratio Newton budget. Article: thm:metric, necessity. -/
theorem robust_newton_budget_necessary (N R : E →L[ℝ] E)
    (hR : R.toLinearMap.IsSymmetric) (hNR : ∀ v : E,N (R v)=v)
    (rho : E) (hrho : rho≠0) (omega : ℝ)
    (hmin : ∀ z : E,robustModelObjective N rho omega (-(R rho))≤robustModelObjective N rho omega z) :
    omega*‖R (R rho)‖≤‖R rho‖ := by
  let b := -(R rho)
  let u := R b
  let h := -(R u)
  have hinj : Function.Injective R := by
    intro x y he
    simpa only [hNR] using congrArg N he
  have hb : b≠0 := by
    intro hz
    have hh : R rho=0 := neg_eq_zero.mp hz
    exact hrho (hinj (hh.trans (map_zero R).symm))
  have hu : u≠0 := by
    intro hz
    exact hb (hinj (hz.trans (map_zero R).symm))
  have hbn := norm_pos_iff.mpr hb
  have hun := norm_pos_iff.mpr hu
  have hNb : N b= -rho := by simp only [b,map_neg,hNR]
  have hNh : N h= -u := by simp only [h,map_neg,hNR]
  have hbh : inner ℝ b h= -(‖u‖^2) := by
    dsimp only [h]
    have hs : inner ℝ (R b) u=inner ℝ b (R u) := hR b u
    rw [inner_neg_right,←hs]
    exact congrArg Neg.neg (real_inner_self_eq_norm_sq u)
  let f : ℝ → ℝ := fun t=>t*‖u‖+omega*‖b+t • h‖
  have hminf : IsMinOn f (Ici 0) 0 := by
    intro t ht
    change 0≤t at ht
    change f 0≤f t
    have he : rho+N (b+t • h)=(-t) • u := by
      rw [map_add,map_smul,hNb,hNh]
      module
    have hh := hmin (b+t • h)
    change robustModelObjective N rho omega b≤_ at hh
    simpa only [robustModelObjective,hNb,add_neg_cancel,norm_zero,zero_add,he,norm_smul,
      Real.norm_eq_abs,abs_neg,abs_of_nonneg ht,f,zero_mul,zero_smul,add_zero] using hh
  have hf : HasDerivAt f (‖u‖+omega*(-(‖u‖^2)/‖b‖)) 0 := by
    have hh := ((hasDerivAt_id 0).mul_const ‖u‖).add
      ((robust_norm_line_deriv b h hb).const_mul omega)
    convert hh using 1
    · rfl
    · simp only [one_mul,hbh]
  have hnonneg := robust_right_min_deriv_nonneg f _ hminf hf
  have hdiv : omega*‖u‖^2/‖b‖≤‖u‖ := by
    have he : omega*(-(‖u‖^2)/‖b‖)= -(omega*‖u‖^2/‖b‖) := by ring
    rw [he] at hnonneg
    linarith only [hnonneg]
  have hbudget : omega*‖u‖≤‖b‖ :=
    (mul_le_mul_iff_left₀ hun).mp (by nlinarith only [(div_le_iff₀ hbn).mp hdiv])
  simpa only [u,b,map_neg,norm_neg] using hbudget

/-- The original Newton norm ratio is exactly the threshold for global
robust optimality of the literal matrix inverse correction.
Article: main_krylov, thm:metric, Omega_1. -/
theorem robust_newtonThreshold_iff {p : ℕ}
    (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (rho : EuclideanSpace ℝ (Fin p)) (hrho : rho≠0)
    (omega : ℝ) (homega : 0≤omega) :
    (∀ z : EuclideanSpace ℝ (Fin p),
      robustModelObjective (cgOperator N) rho omega (-(cgOperator N⁻¹ rho))≤
        robustModelObjective (cgOperator N) rho omega z) ↔ omega≤newtonThreshold N rho := by
  refine ⟨fun hmin=>?_,robust_newtonThreshold_minimum N hN rho hrho omega homega⟩
  have hi (v : EuclideanSpace ℝ (Fin p)) : cgOperator N (cgOperator N⁻¹ v)=v := by
    simp only [cgOperator,←mul_apply_eq_comp,←map_mul,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hN.det_pos.ne'),map_one,one_apply_eq_self]
  have h1 := threshold_action_ne_zero _ hN.inv rho hrho
  have h2 := threshold_action_ne_zero _ hN.inv _ h1
  exact (le_div_iff₀ (norm_pos_iff.mpr h2)).mpr
    (robust_newton_budget_necessary _ _ (cgOperator_positive _ hN.inv).1 hi rho hrho omega hmin)

end
end krylov.XR
