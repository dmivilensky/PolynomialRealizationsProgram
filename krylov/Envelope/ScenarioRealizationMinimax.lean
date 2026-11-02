import krylov.Envelope.ScenarioFrozenLinearity
import krylov.Envelope.SelectionInformationBound
import krylov.Envelope.RFCSelectionValue

set_option autoImplicit false
/-!
Article: main_krylov, s3:cor:qn, actual exact minimax envelope and realization term.
Use: prove one-correction RFC minimizes the genuine worst common
first-jet envelope and its actual realization penalty over every true
symmetric source scenario budget.
Source: actual continuous linear first variations, real compact budget
maxima and genuine budget-preserving absorbed information fibres.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.LinearAlgebra Matrix Set
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual common first-jet canonical envelope norm of a real method on a genuine source scenario.
Use: The actual common first-jet canonical envelope norm of a real method on a genuine source scenario.
Article: main_krylov, s3:cor:qn, actual exact minimax envelope and realization term.
Proof: Add the true reference error, actual common unexplored response and real method explored variation. -/
def scenarioEnvelope (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (Θ : CanonicalScenario n N) : ℝ :=
  ‖cgCanonicalError base g N+scenarioUnexplored base g N Θ+scenarioVariation m base g N Θ‖

/-- The true realization penalty above the actual common reference-plus-unexplored norm.
Use: The true realization penalty above the actual common reference-plus-unexplored norm.
Article: main_krylov, s3:cor:qn, actual exact minimax envelope and realization term.
Proof: Subtract the genuine common norm from the real first-jet envelope. -/
def scenarioPenalty (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (Θ : CanonicalScenario n N) : ℝ :=
  scenarioEnvelope m base g N Θ-‖cgCanonicalError base g N+scenarioUnexplored base g N Θ‖

/-- Every continuous genuine real scenario functional attains its actual supremum on each true finite source budget.
Use: Every continuous genuine real scenario functional attains its actual supremum on each true finite source budget.
Article: main_krylov, s3:cor:qn, actual exact minimax envelope and realization term.
Proof: The actual scenario budget is compact and contains the real zero scenario. -/
theorem scenario_function_maximum (N : ℕ) (ω : Fin (N-1) → ℝ≥0)
    (f : CanonicalScenario n N → ℝ) (hf : Continuous f) :
    IsGreatest (f '' scenarioBudget N ω) (sSup (f '' scenarioBudget N ω)) := by
  have hn : (f '' scenarioBudget N ω).Nonempty := ⟨_,0,scenarioBudget_zero_mem ω,rfl⟩
  obtain ⟨V,hV⟩ := ((scenarioBudget_compact ω).image hf).exists_isGreatest hn
  rw [hV.csSup_eq]
  exact hV

/-- The actual source first-jet envelope is continuous on the true finite scenario space.
Use: The actual source first-jet envelope is continuous on the true finite scenario space.
Article: main_krylov, s3:cor:qn, actual exact minimax envelope and realization term.
Proof: Add the genuine continuous linear first variations to the actual constant reference error and take the real norm. -/
theorem scenarioEnvelope_continuous (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) :
    Continuous (scenarioEnvelope m base g N) :=
  ((continuous_const.add (scenarioUnexplored base g N).continuous).add (scenarioVariation m base g N).continuous).norm

/-- The actual source realization penalty is continuous on the true finite scenario space.
Use: The actual source realization penalty is continuous on the true finite scenario space.
Article: main_krylov, s3:cor:qn, actual exact minimax envelope and realization term.
Proof: Subtract the genuine continuous common norm from the actual continuous first-jet envelope. -/
theorem scenarioPenalty_continuous (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) :
    Continuous (scenarioPenalty m base g N) :=
  (scenarioEnvelope_continuous m base g N).sub (continuous_const.add (scenarioUnexplored base g N).continuous).norm

/-- Every actual smooth globally CG-consistent method on a genuine absorbed scenario has exactly the true RFC first-jet envelope and realization penalty of the original scenario.
Use: Every actual smooth globally CG-consistent method on a genuine absorbed scenario has exactly the true RFC first-jet envelope and realization penalty of the original scenario.
Article: main_krylov, s3:cor:qn, actual exact minimax envelope and realization term.
Proof: Actual absorption preserves the genuine common unexplored response and forces the real explored variation to the true RFC minus-tilt value. -/
theorem absorbed_envelope_eq_rfc (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (Θ : CanonicalScenario n N) (hE : ∀ i, (Θ.1 i).IsSymm) :
    scenarioEnvelope M.policy base g N (absorbedScenario base g Θ)=
      scenarioEnvelope (rfcMethod fullMemory 1) base g N Θ ∧
    scenarioPenalty M.policy base g N (absorbedScenario base g Θ)=
      scenarioPenalty (rfcMethod fullMemory 1) base g N Θ := by
  -- Actual absorption preserves the genuine common norm and forces the real explored variation to the true RFC response.
  have hu := scenarioUnexplored_absorbed base hb g N hcount Θ
  have hv : scenarioVariation M.policy base g N (absorbedScenario base g Θ)=
      scenarioVariation (rfcMethod fullMemory 1) base g N Θ := by
    rw [forced_absorbed_scenarioVariation M base hb g N hN hcount Θ hE,
      rfc_scenario_variation 1 (by norm_num) base hb g N hN hcount Θ]
  constructor
  · unfold scenarioEnvelope
    rw [hu,hv]
  · unfold scenarioPenalty scenarioEnvelope
    rw [hu,hv]

/-- The genuine worst actual RFC first-jet envelope is at most that of every real smooth globally CG-consistent source method.
Use: The genuine worst actual RFC first-jet envelope is at most that of every real smooth globally CG-consistent source method.
Article: main_krylov, s3:cor:qn, actual exact minimax envelope and realization term.
Proof: Choose an actual attained RFC budget maximizer and absorb its genuine scenario without exceeding any true budget; the real information fibre forces the same actual envelope for the competing method. -/
theorem rfc_worst_envelope_le (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    sSup (scenarioEnvelope (rfcMethod fullMemory 1) base g N '' scenarioBudget N ω)≤
      sSup (scenarioEnvelope M.policy base g N '' scenarioBudget N ω) := by
  obtain ⟨Θ,hΘ,hmax⟩ := (scenario_function_maximum N ω _ (scenarioEnvelope_continuous (rfcMethod fullMemory 1) base g N)).1
  rw [← hmax]
  have he := (absorbed_envelope_eq_rfc M base hb g N hN hcount Θ (fun i => (hΘ.1 i).1)).1
  exact (scenario_function_maximum N ω _ (scenarioEnvelope_continuous M.policy base g N)).2
    ⟨absorbedScenario base g Θ,absorbedScenario_budget base g ω Θ hΘ,he⟩

/-- The genuine worst actual RFC realization penalty is minimal over all real smooth globally CG-consistent source methods.
Use: The genuine worst actual RFC realization penalty is minimal over all real smooth globally CG-consistent source methods.
Article: main_krylov, s3:cor:qn, actual exact minimax envelope and realization term.
Proof: Absorb an actual attained RFC realization-penalty maximizer. The genuine admissible forcing scenario gives the same true competing penalty and therefore bounds its actual maximum below. -/
theorem rfc_worst_penalty_le (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    sSup (scenarioPenalty (rfcMethod fullMemory 1) base g N '' scenarioBudget N ω)≤
      sSup (scenarioPenalty M.policy base g N '' scenarioBudget N ω) := by
  obtain ⟨Θ,hΘ,hmax⟩ := (scenario_function_maximum N ω _ (scenarioPenalty_continuous (rfcMethod fullMemory 1) base g N)).1
  rw [← hmax]
  have he := (absorbed_envelope_eq_rfc M base hb g N hN hcount Θ (fun i => (hΘ.1 i).1)).2
  exact (scenario_function_maximum N ω _ (scenarioPenalty_continuous M.policy base g N)).2
    ⟨absorbedScenario base g Θ,absorbedScenario_budget base g ω Θ hΘ,he⟩
end
end krylov.Envelope
