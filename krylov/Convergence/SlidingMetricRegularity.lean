import krylov.Convergence.SlidingMetricSource

/-!
Article: main_krylov, thm:G and thm:Ip, original local source normalization.
Use: derive one admitted normalized source radius from the original
physical neighbourhood, true scalar/gradient derivatives, Hstar and LE.
Source: positive-root congruence and the actual Frechet chain rule.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Original physical C2,1 data provide all genuine normalized source
hypotheses, with the exact printed inverse-root Lipschitz allowance. -/
theorem physical_metric_source_radius
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (center : EuclideanSpace ℝ (Fin n)) (S : Set (EuclideanSpace ℝ (Fin n)))
    (hn : S∈𝓝 center) (hbase : H center=cgOperator base) (hG₀ : G center=0)
    {LE : ℝ≥0} (hH : LipschitzOnWith LE H S)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z) (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    {mu : ℝ} (hmu : 0<mu) (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v)) :
    let T:=metricCoordinates base hb
    let L:ℝ≥0:=Real.toNNReal ((LE:ℝ)*mu^(-(3/2:ℝ)))
    ∃ R : ℝ,0<R ∧ ∀ r : ℝ,0<r → r≤R →
      (L:ℝ)*r≤1/2 ∧
      LipschitzOnWith L (centeredMetricHessian T center H) (Metric.closedBall 0 r) ∧
      centeredMetricHessian T center H 0=ContinuousLinearMap.id ℝ _ ∧
      centeredMetricGradient T center G 0=0 ∧
      (∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin n)) r,
        HasFDerivAt (centeredMetricObjective T center f) (innerSL ℝ (centeredMetricGradient T center G z)) z) ∧
      (∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin n)) r,
        HasFDerivAt (centeredMetricGradient T center G) (centeredMetricHessian T center H z) z) := by
  let T:=metricCoordinates base hb
  let L:ℝ≥0:=Real.toNNReal ((LE:ℝ)*mu^(-(3/2:ℝ)))
  obtain ⟨R,hR,hRsource⟩:=local_source_closedBall_radius (centeredMetricDomain T center S)
    (centeredMetricDomain_mem_nhds T center hn) L
  refine ⟨R,hR,fun r hr hrr=>?_⟩
  obtain ⟨hball,hLr⟩:=hRsource r hr hrr
  refine ⟨hLr,(centeredMetricHessian_lipschitz base hb center H hH hmu hlower).mono hball,?_,?_,?_,?_⟩
  · exact coordinateDerivative_metric_zero base hb (fun z=>H (center+z)) (by simpa only [add_zero] using hbase)
  · simp only [centeredMetricGradient,coordinateGradient,map_zero,add_zero,hG₀]
  · intro z hz
    exact centeredMetricObjective_hasFDerivAt T (metricCoordinates_inverse_symmetric base hb) center f G z (hf _ (hball hz))
  · intro z hz
    exact centeredMetricGradient_hasFDerivAt T center G H z (hG _ (hball hz))

end
end krylov.Convergence
