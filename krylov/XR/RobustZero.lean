import krylov.XR.RobustNewtonNecessary

/-!
Article: main_krylov, thm:metric, exact zero-correction threshold.
Use: identify the original Omega-two formula with genuine global robust
optimality at zero. Source: explicit norm supports for sufficiency and
the actual one-sided derivative in direction minus N rho for necessity.
-/
namespace krylov.XR
noncomputable section
open Set Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Above the true zero threshold the literal zero correction is a
global minimizer. Article: main_krylov, thm:metric, Omega_2. -/
theorem robust_zero_minimum (N : E →L[ℝ] E) (hN : N.toLinearMap.IsSymmetric)
    (rho : E) (hrho : rho≠0) (omega : ℝ) (homega : 0<omega)
    (hbudget : ‖N rho‖/‖rho‖≤omega) :
    ∀ z : E,robustModelObjective N rho omega 0≤robustModelObjective N rho omega z := by
  let v := (‖rho‖⁻¹ : ℝ) • rho
  let w := -(omega⁻¹) • N v
  have hv := robust_unit_support rho hrho
  have hn := norm_pos_iff.mpr hrho
  have hNv : ‖N v‖≤omega := by
    simpa only [v,map_smul,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hn.le),div_eq_mul_inv,mul_comm] using hbudget
  have hw : ‖w‖≤1 := by
    calc
      _=‖N v‖/omega := by
        dsimp only [w]
        rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (inv_nonneg.mpr homega.le)]
        ring
      _≤1 := (div_le_one homega).mpr hNv
  have hbal : N v+omega • w=0 := by
    simp only [w,neg_smul,smul_neg,smul_smul,mul_inv_cancel₀ homega.ne',one_smul,add_neg_cancel]
  exact robust_support_minimum N hN rho 0 v w omega homega.le hv.1 hw
    (by simpa only [map_zero,add_zero] using hv.2) (by simp only [inner_zero_right,norm_zero]) hbal

/-- Genuine robust optimality at zero forces its actual norm-ratio
threshold. Article: main_krylov, thm:metric, necessity at zero. -/
theorem robust_zero_budget_necessary (N : E →L[ℝ] E) (hN : N.toLinearMap.IsSymmetric)
    (rho : E) (hrho : rho≠0) (hNrho : N rho≠0) (omega : ℝ)
    (hmin : ∀ z : E,robustModelObjective N rho omega 0≤robustModelObjective N rho omega z) :
    ‖N rho‖/‖rho‖≤omega := by
  let h := -(N rho)
  let f : ℝ → ℝ := fun t=>‖rho+t • N h‖+omega*(t*‖h‖)
  have hminf : IsMinOn f (Ici 0) 0 := by
    intro t ht
    change 0≤t at ht
    change f 0≤f t
    have hh := hmin (t • h)
    simpa only [robustModelObjective,map_zero,add_zero,norm_zero,mul_zero,map_smul,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,f,zero_smul,zero_add,zero_mul] using hh
  have hf := (robust_norm_line_deriv rho (N h) hrho).add
    (((hasDerivAt_id 0).mul_const ‖h‖).const_mul omega)
  have hinner : inner ℝ rho (N h)= -(‖N rho‖^2) := by
    have hs : inner ℝ (N rho) h=inner ℝ rho (N h) := hN rho h
    rw [←hs]
    simp only [h,inner_neg_right,real_inner_self_eq_norm_sq]
  have hh := robust_right_min_deriv_nonneg f _ hminf hf
  simp only [hinner,h,norm_neg,one_mul] at hh
  have hn := norm_pos_iff.mpr hrho
  have hNn := norm_pos_iff.mpr hNrho
  have hb : ‖N rho‖^2/‖rho‖≤omega*‖N rho‖ := by
    have he : -(‖N rho‖^2)/‖rho‖= -(‖N rho‖^2/‖rho‖) := by ring
    rw [he] at hh
    linarith only [hh]
  apply (div_le_iff₀ hn).mpr
  apply (mul_le_mul_iff_left₀ hNn).mp
  nlinarith only [(div_le_iff₀ hn).mp hb]

/-- The printed Omega-two ratio is precisely the threshold for global
optimality of zero for every original positive matrix model.
Article: main_krylov, thm:metric. -/
theorem robust_zeroThreshold_iff {p : ℕ}
    (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (rho : EuclideanSpace ℝ (Fin p)) (hrho : rho≠0) (omega : ℝ) :
    (∀ z : EuclideanSpace ℝ (Fin p),robustModelObjective (cgOperator N) rho omega 0≤
      robustModelObjective (cgOperator N) rho omega z) ↔ zeroThreshold N rho≤omega := by
  have hn := threshold_action_ne_zero N hN rho hrho
  constructor
  · exact robust_zero_budget_necessary _ (cgOperator_positive N hN).1 rho hrho hn omega
  · intro hbudget
    have ht : 0<zeroThreshold N rho := div_pos (norm_pos_iff.mpr hn) (norm_pos_iff.mpr hrho)
    exact robust_zero_minimum _ (cgOperator_positive N hN).1 rho hrho omega
      (ht.trans_le hbudget) hbudget

end
end krylov.XR
