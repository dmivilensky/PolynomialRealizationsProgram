import krylov.Convergence.OneGradientSourceWitness
import krylov.OneGradient.JacobiCoordinates

/-!
Article: main_krylov, thm:LB, literal Jacobi cubic representation.
Use: identify the actual source's quadratic part with a genuine last-pivot
completion in its original orthogonal physical Lanczos coordinates.
Source: the exact actual completion operator and orthonormal Lanczos
compression identities already established for the original reference.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The genuine scalar cubic quadratic matrix is exactly another member
of the original physical missing-pivot family. Article: main_krylov, thm:LB. -/
theorem oneGradientCubicFibreMatrix_completion
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=k+1) (b d : ℝ) :
    oneGradientCubicFibreMatrix (lanczosCompletion A hA g hg hc b)
      (lastLanczosVector A hA g hg hc) d=lanczosCompletion A hA g hg hc (b+d) := by
  apply (Matrix.toEuclideanCLM (n:=Fin (k+1)) (𝕜:=ℝ)).injective
  change cgOperator (oneGradientCubicFibreMatrix _ _ _)=cgOperator _
  rw [oneGradientCubicFibreMatrix,physicalOperatorMatrix_operator,lanczos_completion_operator,lanczos_completion_operator]
  module

/-- Thus the actual cubic quadratic matrix has precisely the article's
literal J(b+d) Jacobi compression in the genuine fixed Lanczos frame.
Article: main_krylov, thm:LB. -/
theorem oneGradientCubicFibreMatrix_jacobi_coordinates
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=k+1) (b d : ℝ) (i j : Fin (k+1)) :
    ((physicalLanczosColumns A hA g hg hc)ᵀ*
      oneGradientCubicFibreMatrix (lanczosCompletion A hA g hg hc b) (lastLanczosVector A hA g hg hc) d*
      physicalLanczosColumns A hA g hg hc) i j=
      if i=Fin.last k ∧j=Fin.last k then b+d else
        ((physicalLanczosColumns A hA g hg hc)ᵀ*A*physicalLanczosColumns A hA g hg hc) i j := by
  rw [oneGradientCubicFibreMatrix_completion]
  exact physical_lanczos_completion A hA g hg hc (b+d) i j

/-- The literal source gradient at the original starting point is exactly
its prescribed force, with no hidden perturbation. Article: thm:LB. -/
theorem oneGradientCubicFibreGradient_zero
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (g a : E) (b t : ℝ) :
    oneGradientCubicFibreGradient (cgOperator A) g a b t 0=g := by
  rw [oneGradientCubicFibreGradient_eq]
  simp

/-- A constructed witness obeys the original diagonal canonical third
budget for every unit direction in its true minimizer metric.
Article: main_krylov, thm:LB. -/
theorem OneGradientCubicLowerWitness.canonical_third_bound
    {method : OneGradientMethod E} {A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ}
    {g a : E} {R B K : ℝ} (w : OneGradientCubicLowerWitness method A g a R B K)
    (v : E) (hv : ‖v‖=1) :
    |(rankOneCubic (cgOperator (metricRoot (oneGradientCubicTrueHessian A a w.curvature w.cubic w.minimizer))⁻¹ a)
      w.cubic).form v v v|≤B :=
  (oneGradientCubicThird_canonical_bound _ a w.cubic v hv).trans w.tensor_budget

/-- The constructed minimum lies strictly inside its certified source
ball, hence is a genuine local minimum of the smooth scalar cubic.
Article: main_krylov, thm:LB. -/
theorem OneGradientCubicLowerWitness.isLocalMin
    {method : OneGradientMethod E} {A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ}
    {g a : E} {R B K : ℝ} (w : OneGradientCubicLowerWitness method A g a R B K) (hR : 0<R) :
    IsLocalMin (oneGradientCubicFibreObjective A g a w.curvature w.cubic) w.minimizer := by
  apply w.minimum.isLocalMin
  have hx : w.minimizer∈Metric.ball (0:E) R := by
    rw [Metric.mem_ball,dist_zero_right]
    exact w.minimizer_size.trans_lt (half_lt_self hR)
  simpa only [Metric.closedBall,dist_zero_right] using Metric.closedBall_mem_nhds_of_mem hx

end
end krylov.Convergence
