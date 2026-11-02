import krylov.Envelope.ScenarioVariation

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, genuine first variation without global consistency.
Use: identify the actual canonical source-axis derivative of every real differentiable executed scenario map, including genuine methods consistent only at one reference.
Source: the true finite canonical scenario map and standard real Frechet chain rule along its actual linear scenario axis.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant Matrix
open scoped Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- Every actual differentiable finite scenario output has its genuine explored variation equal to the true projected canonical scenario-axis derivative.
Use: Every actual differentiable finite scenario output has its genuine explored variation equal to the true projected canonical scenario-axis derivative.
Article: main_krylov, apB:prop:consist, genuine first variation without global consistency.
Proof: Differentiate the real linear scenario axis and compose the actual executed output derivative with its genuine metric and flag projection. -/
theorem scenarioVariation_of_differentiable (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hG : DifferentiableAt ℝ (scenarioGradient m base g N) 0) (Θ : CanonicalScenario n N) :
    scenarioVariation m base g N Θ=(exploredFlag base g N).starProjection
      (cgOperator (metricRoot base)⁻¹ (deriv (fun t : ℝ => scenarioGradient m base g N (t • Θ)) 0)) := by
  -- The real scenario axis has the actual source array as its true tangent, with no consistency hypothesis.
  have ht : HasDerivAt (fun t : ℝ => t • Θ) Θ 0 := by
    simpa only [id_eq,one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const Θ
  have hF : HasFDerivAt (scenarioGradient m base g N) (fderiv ℝ (scenarioGradient m base g N) 0) ((0 : ℝ) • Θ) := by
    rw [zero_smul]
    exact hG.hasFDerivAt
  have he := hF.comp_hasDerivAt (0 : ℝ) ht
  change (exploredFlag base g N).starProjection (cgOperator (metricRoot base)⁻¹ ((fderiv ℝ (scenarioGradient m base g N) 0) Θ))=_
  change HasDerivAt (fun t : ℝ => scenarioGradient m base g N (t • Θ))
    ((fderiv ℝ (scenarioGradient m base g N) 0) Θ) 0 at he
  rw [he.deriv]
end
end krylov.Envelope
