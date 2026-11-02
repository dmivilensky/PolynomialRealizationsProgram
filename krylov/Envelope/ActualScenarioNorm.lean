import krylov.Envelope.CompactScenarioTaylor
import krylov.Envelope.ScenarioBudgetNorm

set_option autoImplicit false
/-!
Article: main_krylov, s3:cor:qn, actual finite-output scenario gradient norms.
Use: compare genuinely executed output norms to their real first-jet
envelopes and transfer actual absorbed information fibres to finite outputs.
Source: true canonical raw-cycle execution, the genuine reverse triangle
inequality and proved actual compact first-jet maxima and absorbed envelopes.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual final canonical gradient norm of a genuine raw method on the true finite source scenario.
Use: The actual final canonical gradient norm of a genuine raw method on the true finite source scenario.
Article: main_krylov, s3:cor:qn, actual finite-output scenario gradient norms.
Proof: Execute the real source cycle and take its genuine inverse-metric-root norm. -/
def actualScenarioNorm (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (Θ : CanonicalScenario n N) : ℝ :=
  ‖cgOperator (metricRoot base)⁻¹ (scenarioGradient m base g N Θ)‖

/-- The genuine worst actual finite-output canonical gradient norm over the true independent source scenario budget.
Use: The genuine worst actual finite-output canonical gradient norm over the true independent source scenario budget.
Article: main_krylov, s3:cor:qn, actual finite-output scenario gradient norms.
Proof: Take the real supremum of the actual executed norm image on the genuine source budget. -/
def worstScenarioNorm (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (ω : Fin (N-1) → ℝ≥0) : ℝ :=
  sSup (actualScenarioNorm m base g N '' scenarioBudget N ω)

/-- The difference between the real finite-output norm and its genuine first-jet envelope is bounded by the true vector remainder.
Use: The difference between the real finite-output norm and its genuine first-jet envelope is bounded by the true vector remainder.
Article: main_krylov, s3:cor:qn, actual finite-output scenario gradient norms.
Proof: Apply the genuine norm reverse triangle inequality to the actual output and its real first jet. -/
theorem actualScenarioNorm_envelope_bound (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (Θ : CanonicalScenario n N) :
    |actualScenarioNorm m base g N Θ-scenarioEnvelope m base g N Θ|≤
      ‖cgOperator (metricRoot base)⁻¹ (scenarioGradient m base g N Θ)-
        (cgCanonicalError base g N+scenarioUnexplored base g N Θ+scenarioVariation m base g N Θ)‖ :=
  abs_norm_sub_norm_le _ _

/-- A genuine uniform norm-envelope remainder makes the actual finite-output norm image bounded above on the true source budget.
Use: A genuine uniform norm-envelope remainder makes the actual finite-output norm image bounded above on the true source budget.
Article: main_krylov, s3:cor:qn, actual finite-output scenario gradient norms.
Proof: The real continuous first-jet envelope attains a true compact maximum; add the actual uniform remainder to bound every genuine nonlinear output. -/
theorem actualScenarioNorm_bddAbove (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (ω : Fin (N-1) → ℝ≥0) (R : ℝ)
    (hR : ∀ Θ∈scenarioBudget N ω,
      |actualScenarioNorm m base g N Θ-scenarioEnvelope m base g N Θ|≤R) :
    BddAbove (actualScenarioNorm m base g N '' scenarioBudget N ω) := by
  refine ⟨sSup (scenarioEnvelope m base g N '' scenarioBudget N ω)+R,?_⟩
  rintro z ⟨Θ,hΘ,rfl⟩
  have he := (scenario_function_maximum N ω _ (scenarioEnvelope_continuous m base g N)).2 ⟨Θ,hΘ,rfl⟩
  have hr := (abs_le.mp (hR Θ hΘ)).2
  linarith

/-- The true actual RFC output norm is at most the genuine competing-method output on its real absorbed scenario plus the two actual remainder bounds.
Use: The true actual RFC output norm is at most the genuine competing-method output on its real absorbed scenario plus the two actual remainder bounds.
Article: main_krylov, s3:cor:qn, actual finite-output scenario gradient norms.
Proof: The actual first-jet envelopes agree on the genuine information fibre; retain both real finite-output norm remainders. -/
theorem actualScenarioNorm_absorption_comparison
    (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (Θ : CanonicalScenario n N) (hE : ∀ i, (Θ.1 i).IsSymm) (R S : ℝ)
    (hr : |actualScenarioNorm (rfcMethod fullMemory 1) base g N Θ-
      scenarioEnvelope (rfcMethod fullMemory 1) base g N Θ|≤R)
    (hs : |actualScenarioNorm M.policy base g N (absorbedScenario base g Θ)-
      scenarioEnvelope M.policy base g N (absorbedScenario base g Θ)|≤S) :
    actualScenarioNorm (rfcMethod fullMemory 1) base g N Θ≤
      actualScenarioNorm M.policy base g N (absorbedScenario base g Θ)+(R+S) := by
  have he := (absorbed_envelope_eq_rfc M base hb g N hN hcount Θ hE).1
  have hr' := (abs_le.mp hr).2
  have hs' := (abs_le.mp hs).1
  rw [he] at hs'
  linarith
end
end krylov.Envelope
