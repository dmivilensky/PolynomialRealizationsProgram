import krylov.Convergence.ObservableFCTerminal
import krylov.Functions.GenericMetricPullback
import krylov.Functions.SelfConcordantLipschitz

/-!
Article: main_krylov, apG:Dunif, primitive actual self-concordant sources.
Use: derive one universal canonical source ball and the absolute Hessian
Lipschitz allowance four directly from the true scalar differential data.
Source: affine invariance of standard self-concordance, actual derivative
uniqueness and the proved Nesterov metric/Lipschitz theorem. No local
regularity or execution constant is supplied by the function as an input.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Matrix krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {n : ℕ}

/-- A genuine globally standard-self-concordant scalar function supplies
the same canonical source radius and Lipschitz constant for every positive
physical minimizer Hessian. The actual gradient and actual Hessian are used.
Article: main_krylov, apG:Dunif, original primitive function hypotheses. -/
theorem observable_selfConcordant_source
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : StandardSelfConcordantData f univ) (hgzero : gradient f 0=0)
    (hH : D.hessian 0=cgOperator base) :
    ObservableLocalSource (metricCoordinates base hb) f (gradient f) D.hessian (1/64) 4 := by
  let T := metricCoordinates base hb
  have hT := metricCoordinates_inverse_symmetric base hb
  obtain ⟨C⟩ := coordinateObjective_selfConcordant T hT f univ ⟨D⟩
  have hsame (z : EuclideanSpace ℝ (Fin n)) : C.hessian z=coordinateDerivative T D.hessian z := by
    exact (C.gradient_derivative z (by trivial)).unique
      (coordinateObjective_gradient_hasFDerivAt T hT f univ D z (by trivial))
  have hzero : C.hessian 0=ContinuousLinearMap.id ℝ _ := by
    rw [hsame]
    exact coordinateDerivative_metric_zero base hb D.hessian hH
  have hLip := standardSelfConcordant_hessian_lipschitz (coordinateObjective T f)
    (T.symm ⁻¹' univ) C (by trivial) hzero (R:=1/8) (by norm_num) (by intro z _;trivial)
  have hLip4 : LipschitzOnWith (4:ℝ≥0) C.hessian (Metric.ball 0 (1/8)) :=
    hLip.weaken (by norm_num)
  have hball : closedBall (0:EuclideanSpace ℝ (Fin n)) (1/64)⊆Metric.ball 0 (1/8) := by
    intro z hz
    rw [mem_closedBall,dist_zero_right] at hz
    rw [mem_ball,dist_zero_right]
    linarith
  have hCLip : LipschitzOnWith (4:ℝ≥0) (coordinateDerivative T D.hessian) (closedBall 0 (1/64)) := by
    have hh := hLip4.mono hball
    rw [funext hsame] at hh
    exact hh
  refine ⟨hT,by norm_num,hgzero,coordinateDerivative_metric_zero base hb D.hessian hH,
    by norm_num,hCLip,?_,?_⟩
  · intro z _hz
    exact (D.differentiable.differentiableAt (D.open_domain.mem_nhds (by trivial))).hasGradientAt.hasFDerivAt
  · intro z _hz
    exact D.gradient_derivative z (by trivial)

end
end krylov.Convergence
