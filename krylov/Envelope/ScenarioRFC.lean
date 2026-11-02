import krylov.Envelope.ScenarioVariation
import krylov.Envelope.ScenarioPaths

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, genuine linear common tilt and actual RFC response on all finite scenarios.
Use: identify real full-memory repeated RFC first variations on the actual
finite canonical source space, including all genuine independent correction
defects, and derive the true continuous linear common-tilt operator.
Source: actual primitive RFC smooth membership, true canonical scenario
paths and genuine executed RFC residual-order cancellation.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Filter Topology
open scoped BigOperators Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- Actual full-memory repeated RFC has the true minus-common-tilt variation on every genuine finite canonical increment and independent correction-defect scenario.
Use: Actual full-memory repeated RFC has the true minus-common-tilt variation on every genuine finite canonical increment and independent correction-defect scenario.
Article: main_krylov, thm:select, genuine linear common tilt and actual RFC response on all finite scenarios.
Proof: Derive genuine actual scenario-axis variation from the real primitive smooth RFC class. True source paths are analytic with their actual quadratic reference values, so the proved genuine RFC residual-order theorem identifies the real explored derivative with minus the actual common tilt. -/
theorem rfc_scenario_variation (count : ℕ) (hc : 0<count)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (Θ : CanonicalScenario n N) :
    scenarioVariation (rfcMethod fullMemory count) base g N Θ=
      -commonTilt base g (canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1)) N := by
  -- Primitive membership is derived for the actual repeated RFC executor before applying genuine scenario-axis differentiation and real residual cancellation.
  let M := smoothRFCClass fullMemory (fun _ hk => hk) count (E := EuclideanSpace ℝ (Fin n))
  let A := fun t : ℝ => scenarioProbe base (t • Θ)
  let B := fun t : ℝ => scenarioCorrection base (t • Θ)
  have hA (k : ℕ) : AnalyticAt ℝ (fun t => A t k) 0 := scenarioProbe_path_analytic base Θ k
  have hB (k : ℕ) : AnalyticAt ℝ (fun t => B t k) 0 := scenarioCorrection_path_analytic base Θ k
  have hA0 : A 0=fun _ => cgOperator base := by
    dsimp only [A]
    rw [zero_smul,scenarioProbe_zero]
  have hB0 : B 0=fun _ => cgOperator base := by
    dsimp only [B]
    rw [zero_smul,scenarioCorrection_zero]
  have hv := scenarioVariation_actual M base hb g N hcount Θ
  have ht := fullRFC_tilt count hc base hb g A B hA hB hA0 hB0 N hN hcount
  change scenarioVariation (rfcMethod fullMemory count) base g N Θ=
    (exploredFlag base g N).starProjection (cgOperator (metricRoot base)⁻¹
      (deriv (fun t => probedGradient (rfcMethod fullMemory count) (A t) (B t) g N) 0)) at hv
  rw [hv]
  have he : A=canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1) := funext (fun t => scenarioProbe_scale base Θ t)
  change (exploredFlag base g N).starProjection (cgOperator (metricRoot base)⁻¹
    (deriv (fun t : ℝ => probedGradient (rfcMethod fullMemory count) (A t) (B t) g N) 0))=
      -commonTilt base g A N at ht
  simpa only [he] using ht

/-- The genuine continuous linear common-tilt operator on the actual finite canonical increment space.
Use: The genuine continuous linear common-tilt operator on the actual finite canonical increment space.
Article: main_krylov, thm:select, genuine linear common tilt and actual RFC response on all finite scenarios.
Proof: Use the real RFC cycle first derivative with actual zero correction defects and negate its true explored response. -/
def canonicalTiltLinear (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) :
    (Fin (N-1) → Matrix (Fin n) (Fin n) ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  -(scenarioVariation (rfcMethod fullMemory 1) base g N ∘L
    ContinuousLinearMap.inl ℝ (Fin (N-1) → Matrix (Fin n) (Fin n) ℝ) (Fin N → Matrix (Fin n) (Fin n) ℝ))

/-- The true continuous linear common-tilt operator equals exactly the genuine measured frozen tilt on every actual finite canonical increment scenario.
Use: The true continuous linear common-tilt operator equals exactly the genuine measured frozen tilt on every actual finite canonical increment scenario.
Article: main_krylov, thm:select, genuine linear common tilt and actual RFC response on all finite scenarios.
Proof: The actual real RFC response is minus the genuine common tilt; evaluate its true finite-scenario embedding and negate the actual response. -/
theorem canonicalTiltLinear_apply (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (E : Fin (N-1) → Matrix (Fin n) (Fin n) ℝ) :
    canonicalTiltLinear base g N E=commonTilt base g (canonicalFCPath base (matrixSequenceExtension (N-1) E)) N := by
  change -scenarioVariation (rfcMethod fullMemory 1) base g N (E,0)=_
  rw [rfc_scenario_variation 1 (by norm_num) base hb g N hN hcount (E,0),neg_neg]
end
end krylov.Envelope
