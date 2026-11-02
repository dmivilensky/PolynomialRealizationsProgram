import krylov.XR.RobustSupport

/-!
Article: main_krylov, thm:metric, actual Newton branch of robust least squares.
Use: prove global optimality of the true inverse-model correction up to
the original printed threshold, for general positive metrics.
Source: the explicit Hilbert norm support certificate; actual inverse
cancellation derives every domain used in the certificate.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true inverse-model correction is globally robust optimal on
its exact norm-ratio budget. Article: thm:metric, Newton endpoint. -/
theorem robust_newton_minimum (N R : E →L[ℝ] E) (hN : N.toLinearMap.IsSymmetric)
    (hNR : ∀ v : E,N (R v)=v) (rho : E) (hrho : rho≠0)
    (omega : ℝ) (homega : 0≤omega)
    (hbudget : omega*‖R (R rho)‖≤‖R rho‖) :
    ∀ z : E,robustModelObjective N rho omega (-(R rho))≤robustModelObjective N rho omega z := by
  let b := -(R rho)
  have hb : b≠0 := by
    intro hz
    have hh : R rho=0 := neg_eq_zero.mp hz
    have he := hNR rho
    rw [hh,map_zero] at he
    exact hrho he.symm
  have hn := norm_pos_iff.mpr hb
  let w := (‖b‖⁻¹ : ℝ) • b
  let v := -(omega/‖b‖) • R b
  have hw := robust_unit_support b hb
  have hbound : omega*‖R b‖≤‖b‖ := by simpa only [b,map_neg,norm_neg] using hbudget
  have hv : ‖v‖≤1 := by
    calc
      _=omega*‖R b‖/‖b‖ := by
        dsimp only [v]
        rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_div,
          abs_of_nonneg homega,abs_of_nonneg hn.le]
        ring
      _≤1 := (div_le_one hn).mpr hbound
  have hres : rho+N b=0 := by simp only [b,map_neg,hNR,add_neg_cancel]
  have hbalance : N v+omega • w=0 := by
    simp only [v,w,map_smul,hNR,smul_smul]
    rw [show -(omega/‖b‖)= -(omega*‖b‖⁻¹) by rw [div_eq_mul_inv]]
    module
  exact robust_support_minimum N hN rho b v w omega homega hv hw.1
    (by rw [hres,inner_zero_right,norm_zero]) hw.2 hbalance

/-- The original printed Newton threshold is a genuine global
optimality threshold for the actual positive matrix model.
Article: main_krylov, thm:metric, Omega_1. -/
theorem robust_newtonThreshold_minimum {p : ℕ}
    (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (rho : EuclideanSpace ℝ (Fin p)) (hrho : rho≠0)
    (omega : ℝ) (homega : 0≤omega) (hsmall : omega≤newtonThreshold N rho) :
    ∀ z : EuclideanSpace ℝ (Fin p),
      robustModelObjective (cgOperator N) rho omega (-(cgOperator N⁻¹ rho))≤
        robustModelObjective (cgOperator N) rho omega z := by
  have hi (v : EuclideanSpace ℝ (Fin p)) : cgOperator N (cgOperator N⁻¹ v)=v := by
    simp only [cgOperator,←mul_apply_eq_comp,←map_mul,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hN.det_pos.ne'),map_one,one_apply_eq_self]
  have hinv := hN.inv
  have h1 := threshold_action_ne_zero _ hinv rho hrho
  have h2 := threshold_action_ne_zero _ hinv _ h1
  apply robust_newton_minimum _ _ (cgOperator_positive N hN).1 hi rho hrho omega homega
  exact (le_div_iff₀ (norm_pos_iff.mpr h2)).mp hsmall

end
end krylov.XR
