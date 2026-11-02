import krylov.Envelope.ScenarioAbsorption
import krylov.Envelope.ScenarioMaximum

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, genuine actual information-forced selection lower bound.
Use: construct a real admissible absorbed scenario forcing every actual
smooth globally CG-consistent source-class member to attain at least the
true common-tilt selection value, including genuine degenerate budgets.
Source: actual compact common-tilt maximizers, true budget-preserving
absorbed scenarios and the genuine class-quantified quadratic information fibre.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Every actual genuine smooth globally CG-consistent method has a real admissible absorbed source scenario whose true transverse variation norm equals the actual common-tilt selection value.
Use: Every actual genuine smooth globally CG-consistent method has a real admissible absorbed source scenario whose true transverse variation norm equals the actual common-tilt selection value.
Article: main_krylov, thm:select, genuine actual information-forced selection lower bound.
Proof: Choose a genuine attained common-tilt increment maximizer, add actual zero correction defects and absorb its true canonical increments. Real budgets are preserved and the actual information fibre forces minus the original genuine common tilt. -/
theorem selection_lower_witness (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    ∃ Θ∈scenarioBudget N ω, ‖scenarioVariation M.policy base g N Θ‖=selectionValue base g N ω := by
  -- Choose a genuine actual common-tilt maximizer and compress its true canonical increments without exceeding any real source budget.
  obtain ⟨E,hE,hval⟩ := (selectionValue_attained base g N ω).1
  let Θ : CanonicalScenario n N := (E,0)
  have hΘ : Θ∈scenarioBudget N ω := ⟨hE,(scenarioBudget_zero_mem (n := n) ω).2⟩
  refine ⟨absorbedScenario base g Θ,absorbedScenario_budget base g ω Θ hΘ,?_⟩
  have hv := forced_absorbed_scenarioVariation M base hb g N hN hcount Θ (fun i => (hE i).1)
  rw [hv,norm_neg]
  change ‖commonTilt base g (canonicalFCPath base (matrixSequenceExtension (N-1) E)) N‖=_
  rw [← canonicalTiltLinear_apply base hb g N hN hcount E]
  exact hval

/-- The genuine common-tilt selection value is a true lower bound for the actual worst transverse variation of every real smooth globally CG-consistent source-class member.
Use: The genuine common-tilt selection value is a true lower bound for the actual worst transverse variation of every real smooth globally CG-consistent source-class member.
Article: main_krylov, thm:select, genuine actual information-forced selection lower bound.
Proof: Use the constructed genuine absorbed forcing scenario in the actual attained worst-scenario upper bound. -/
theorem selection_le_worstTransverse (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    selectionValue base g N ω≤worstTransverse M.policy base g N ω := by
  obtain ⟨Θ,hΘ,hval⟩ := selection_lower_witness M base hb g N hN hcount ω
  exact (worstTransverse_attained M.policy base g N ω).2 ⟨Θ,hΘ,hval⟩
end
end krylov.Envelope
