import krylov.Envelope.ScenarioCoordinates

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, genuine analytic finite canonical scenario paths.
Use: derive actual line and correction path analyticity for every real
finite canonical source scenario, including its genuine independent
correction defects, without any presumed method response.
Source: true scenario scaling identities and the actual affine canonical
segment calculus with real positive-root defect congruence.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The actual line-operator path along every genuine finite canonical scenario is real analytic.
Use: The actual line-operator path along every genuine finite canonical scenario is real analytic.
Article: main_krylov, thm:select, genuine analytic finite canonical scenario paths.
Proof: The true scaled finite scenario is exactly the actual affine canonical line path. -/
theorem scenarioProbe_path_analytic (base : Matrix (Fin n) (Fin n) ℝ) (Θ : CanonicalScenario n N) (k : ℕ) :
    AnalyticAt ℝ (fun t : ℝ => scenarioProbe base (t • Θ) k) 0 := by
  simpa only [scenarioProbe_scale] using (canonicalFCPath_calculus base (matrixSequenceExtension (N-1) Θ.1) k).1

/-- The actual correction-operator path along every genuine finite canonical scenario is real analytic.
Use: The actual correction-operator path along every genuine finite canonical scenario is real analytic.
Article: main_krylov, thm:select, genuine analytic finite canonical scenario paths.
Proof: The genuine scaled correction segment is its true analytic line path plus the real parameter times the actual fixed correction defect. -/
theorem scenarioCorrection_path_analytic (base : Matrix (Fin n) (Fin n) ℝ) (Θ : CanonicalScenario n N) (k : ℕ) :
    AnalyticAt ℝ (fun t : ℝ => scenarioCorrection base (t • Θ) k) 0 := by
  have he : (fun t : ℝ => scenarioCorrection base (t • Θ) k)=fun t => canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1) t k+
      t • cgOperator (metricRoot base*matrixSequenceExtension N Θ.2 k*metricRoot base) :=
    funext (fun t => scenarioCorrection_scale base Θ t k)
  rw [he]
  exact (canonicalFCPath_calculus base (matrixSequenceExtension (N-1) Θ.1) k).1.add
    (analyticAt_id.smul analyticAt_const)
end
end krylov.Envelope
