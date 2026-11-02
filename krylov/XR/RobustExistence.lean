import krylov.XR.RobustZero

/-!
Article: main_krylov, thm:metric, attained general robust path.
Use: derive existence of a true global correction minimizer before
identifying its regularization parameter. Source: finite-dimensional
compactness and the actual positive norm penalty's coercive lower bound.
-/
namespace krylov.XR
noncomputable section
open Set Metric
open scoped InnerProductSpace

/-- Every positive robust radius has a genuine attained global
minimum for the original finite-dimensional objective.
Article: main_krylov, thm:metric, robust least-squares path. -/
theorem robustModelObjective_exists_minimum {p : ℕ}
    (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (rho : EuclideanSpace ℝ (Fin p)) (omega : ℝ) (homega : 0<omega) :
    ∃ b : EuclideanSpace ℝ (Fin p),∀ z,
      robustModelObjective N rho omega b≤robustModelObjective N rho omega z := by
  let R := ‖rho‖/omega+1
  have hR : 0<R := by dsimp only [R];positivity
  have hc : Continuous (robustModelObjective N rho omega) :=
    (continuous_const.add N.continuous).norm.add (continuous_const.mul continuous_norm)
  have hzero : (0 : EuclideanSpace ℝ (Fin p))∈closedBall 0 R := by
    simpa only [mem_closedBall,dist_self] using hR.le
  obtain ⟨b,hb,hmin⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin p)) R).exists_isMinOn
    ⟨0,hzero⟩ hc.continuousOn
  have hbound : robustModelObjective N rho omega b≤‖rho‖ := by
    have hh := (isMinOn_iff.mp hmin) 0 hzero
    simpa only [robustModelObjective,map_zero,add_zero,norm_zero,mul_zero] using hh
  refine ⟨b,?_⟩
  intro z
  by_cases hz : ‖z‖≤R
  · exact (isMinOn_iff.mp hmin) z (by simpa only [mem_closedBall,dist_zero_right] using hz)
  · have hlt : R<‖z‖ := lt_of_not_ge hz
    have hscale := mul_lt_mul_of_pos_left hlt homega
    have he : omega*R=‖rho‖+omega := by dsimp only [R];field_simp
    rw [he] at hscale
    dsimp only [robustModelObjective] at hbound ⊢
    linarith only [hbound,hscale,homega,norm_nonneg (rho+N z)]

end
end krylov.XR
