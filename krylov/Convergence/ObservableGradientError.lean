import krylov.Convergence.ObservableFCSource
import krylov.Nonlinear.GradientQuadratic

/-!
Article: main_krylov, apG:Dunif, genuine local gradient/error equivalence.
Use: convert the derived true terminal gradient bound into the actual
canonical solution error. Source: the actual radial gradient FTC with its
one-half Hessian Lipschitz remainder, not an assumed error equivalence.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every true local scalar source has the uniform actual canonical
gradient-to-error bound throughout its admitted metric ball.
Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.gradient_error {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (z : E) (hz : ‖z‖≤r) : ‖z‖≤2*‖coordinateGradient T G z‖ := by
  have hgzero : coordinateGradient T G 0=0 := by simp only [coordinateGradient,map_zero,S.gradient_zero]
  have hh := gradient_model_quadratic_error (coordinateGradient T G) (coordinateDerivative T H)
    (ContinuousLinearMap.id ℝ E) (closedBall 0 r) (convex_closedBall _ _)
    (mem_closedBall_self S.radius_pos.le) S.hessian_zero S.lipschitz
    (fun x hx=>S.coordinate_g x (by simpa only [mem_closedBall,dist_zero_right] using hx)) z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  rw [hgzero,sub_zero,ContinuousLinearMap.id_apply] at hh
  have hL : (L:ℝ)*‖z‖≤1/2 := (mul_le_mul_of_nonneg_left hz L.coe_nonneg).trans S.small
  have hbound : ‖coordinateGradient T G z-z‖≤‖z‖/4 := by
    have hm := mul_le_mul_of_nonneg_right hL (norm_nonneg z)
    exact hh.trans (by nlinarith only [hm])
  have hn := norm_sub_le (coordinateGradient T G z) (coordinateGradient T G z-z)
  rw [sub_sub_cancel] at hn
  nlinarith only [hn,hbound,norm_nonneg z]

end
end krylov.Convergence
