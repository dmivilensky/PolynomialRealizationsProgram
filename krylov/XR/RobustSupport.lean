import krylov.XR.RobustCalculus

/-!
Article: main_krylov, thm:metric, genuine robust least-squares optimality.
Use: derive global robust optimality from actual Hilbert norm supporting
vectors; this proves the endpoint and Tikhonov branches without assuming
that the desired correction minimizes the objective.
Source: Cauchy--Schwarz and the true self-adjoint model pairing.
-/
namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- True norm-support vectors with cancelling model gradient certify a
global minimum of the actual robust objective.
Article: main_krylov, thm:metric. -/
theorem robust_support_minimum (N : E →L[ℝ] E) (hN : N.toLinearMap.IsSymmetric)
    (rho b v w : E) (omega : ℝ) (homega : 0≤omega)
    (hv : ‖v‖≤1) (hw : ‖w‖≤1)
    (hres : inner ℝ v (rho+N b)=‖rho+N b‖) (hb : inner ℝ w b=‖b‖)
    (hbalance : N v+omega • w=0) :
    ∀ z : E,robustModelObjective N rho omega b≤robustModelObjective N rho omega z := by
  intro z
  have hpair (x : E) : inner ℝ v (N x)+omega*inner ℝ w x=0 := by
    have hh := congrArg (fun y : E=>inner ℝ y x) hbalance
    simp only [inner_add_left,real_inner_smul_left,inner_zero_left] at hh
    have hs : inner ℝ (N v) x=inner ℝ v (N x) := hN v x
    rw [hs] at hh
    exact hh
  have hz := (real_inner_le_norm v (rho+N z)).trans
    (by nlinarith only [mul_le_mul_of_nonneg_right hv (norm_nonneg (rho+N z))] :
      ‖v‖*‖rho+N z‖≤‖rho+N z‖)
  have hwz := (real_inner_le_norm w z).trans
    (by nlinarith only [mul_le_mul_of_nonneg_right hw (norm_nonneg z)] : ‖w‖*‖z‖≤‖z‖)
  have hscale := mul_le_mul_of_nonneg_left hwz homega
  have hpb := hpair b
  rw [hb] at hpb
  rw [inner_add_right] at hz hres
  dsimp only [robustModelObjective]
  linarith only [hpb,hpair z,hres,hz,hscale]

/-- The true normalized nonzero vector supports the actual norm exactly.
Article: main_krylov, thm:metric. -/
theorem robust_unit_support (b : E) (hb : b≠0) :
    ‖(‖b‖⁻¹ : ℝ) • b‖≤1 ∧ inner ℝ ((‖b‖⁻¹ : ℝ) • b) b=‖b‖ := by
  refine ⟨(norm_smul_inv_norm hb).le,?_⟩
  rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
  field_simp

end
end krylov.XR
