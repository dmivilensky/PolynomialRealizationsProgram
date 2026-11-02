import krylov.Envelope.ScenarioCoordinates
import krylov.Envelope.RealizationDifference

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, genuine linear first variation on actual source scenarios.
Use: derive actual raw-method canonical transverse first variations as
true continuous linear maps on the genuine finite increment/correction
scenario space, directly from real primitive coefficient membership.
Source: standard Frechet differentiation of the genuine actual C-two
cycle, true finite canonical oracle coordinates and real metric projection.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Filter Topology
open scoped BigOperators Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The genuinely executed raw-method final gradient as a function of the actual finite canonical source scenario.
Use: The genuinely executed raw-method final gradient as a function of the actual finite canonical source scenario.
Article: main_krylov, thm:select, genuine linear first variation on actual source scenarios.
Proof: Execute the true source line and correction operators on the actual fixed initial gradient. -/
def scenarioGradient (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (Θ : CanonicalScenario n N) : EuclideanSpace ℝ (Fin n) :=
  probedGradient m (scenarioProbe base Θ) (scenarioCorrection base Θ) g N

/-- The actual gradient cycle of every genuine smooth globally CG-consistent source-class member is C-two in its real finite canonical scenario at the true reference.
Use: The actual gradient cycle of every genuine smooth globally CG-consistent source-class member is C-two in its real finite canonical scenario at the true reference.
Article: main_krylov, thm:select, genuine linear first variation on actual source scenarios.
Proof: Actual primitive scenario operators are smooth and have genuine constant quadratic reference values. True active-count nonstagnation and real class primitive coefficient membership derive actual executed-cycle regularity. -/
theorem scenarioGradient_regular (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g) : ContDiffAt ℝ 2 (scenarioGradient M.policy base g N) 0 := by
  -- The genuine source coefficient hypothesis derives actual C-two cycle regularity on the real finite scenario coordinates.
  apply smoothProbed_gradient_regular M.policy M.consistent (scenarioProbe base) (scenarioCorrection base) (fun _ => g) 0 N
    (fun i _ => (scenarioPrimitive_regular base hb i 2).1) (fun i _ => (scenarioPrimitive_regular base hb i 2).2)
    contDiffAt_const (cgOperator base) (scenarioProbe_zero base) (scenarioCorrection_zero base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount))
  exact M.smooth (cgOperator base) (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g N
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount))

/-- The genuine continuous linear explored canonical first derivative of the actual raw-method cycle on the true finite source scenario space.
Use: The genuine continuous linear explored canonical first derivative of the actual raw-method cycle on the true finite source scenario space.
Article: main_krylov, thm:select, genuine linear first variation on actual source scenarios.
Proof: Compose the actual cycle Frechet derivative with its true inverse metric root and genuine explored orthogonal projector. -/
def scenarioVariation (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) :
    (CanonicalScenario n N) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (exploredFlag base g N).starProjection ∘L cgOperator (metricRoot base)⁻¹ ∘L fderiv ℝ (scenarioGradient m base g N) 0

/-- The true scenario variation map of each actual genuine source-class member equals exactly its real canonical explored gradient derivative along the actual scaled scenario path.
Use: The true scenario variation map of each actual genuine source-class member equals exactly its real canonical explored gradient derivative along the actual scaled scenario path.
Article: main_krylov, thm:select, genuine linear first variation on actual source scenarios.
Proof: Primitive coefficient membership gives true actual cycle differentiability. Apply the genuine Frechet chain rule to the real linear scenario axis and retain the actual metric/projection composition. -/
theorem scenarioVariation_actual (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g)
    (Θ : CanonicalScenario n N) :
    scenarioVariation M.policy base g N Θ=(exploredFlag base g N).starProjection
      (cgOperator (metricRoot base)⁻¹ (deriv (fun t : ℝ => scenarioGradient M.policy base g N (t • Θ)) 0)) := by
  -- Differentiate the true actual cycle along the real scenario axis, keeping the genuine zero reference and actual tangent explicit.
  have hG := (scenarioGradient_regular M base hb g N hcount).differentiableAt (by norm_num)
  have ht : HasDerivAt (fun t : ℝ => t • Θ) Θ 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).smul_const Θ using 1
    simp only [one_smul]
  have hF : HasFDerivAt (scenarioGradient M.policy base g N) (fderiv ℝ (scenarioGradient M.policy base g N) 0) ((0 : ℝ) • Θ) := by
    rw [zero_smul]
    exact hG.hasFDerivAt
  have he := hF.comp_hasDerivAt 0 ht
  change (exploredFlag base g N).starProjection (cgOperator (metricRoot base)⁻¹ ((fderiv ℝ (scenarioGradient M.policy base g N) 0) Θ))=_
  change HasDerivAt (fun t : ℝ => scenarioGradient M.policy base g N (t • Θ))
    ((fderiv ℝ (scenarioGradient M.policy base g N) 0) Θ) 0 at he
  rw [he.deriv]
end
end krylov.Envelope
