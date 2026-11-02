import krylov.Envelope.CompactBudgetEnvelope
import krylov.Envelope.CompactScenarioDerivative
import krylov.Envelope.ScenarioEnvelopeGeometry

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm, actual compact-uniform first-order budget comparison near exhaustion.
Use: give a genuine common first-order norm-comparison bound for actual
smooth methods even when the true final reference error vanishes.
Source: actual compact budget envelopes, genuine weighted source derivative
bounds and true orthogonal explored/common norm comparison.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator NNReal
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- Any two actual smooth source methods have a genuine compact-uniform first-order largest-budget norm difference bound, including actual exhausted references.
Use: Any two actual smooth source methods have a genuine compact-uniform first-order largest-budget norm difference bound, including actual exhausted references.
Article: main_krylov, cor:lm, actual compact-uniform first-order budget comparison near exhaustion.
Proof: Bound the real explored first variations by the true compact weighted derivative estimates. Orthogonal comparison controls their genuine common envelopes by the actual larger explored norm; add both real quadratic remainders and use the true unit budget radius. -/
theorem compact_budget_method_linear (M L : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 0<N) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K), N≤referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ ω : Fin (N-1) → ℝ≥0,
      (maximalBudget ω : ℝ)≤δ → ∀ Θ∈scenarioBudget N ω,
      |actualScenarioNorm M.policy (base x) (g x) N Θ-actualScenarioNorm L.policy (base x) (g x) N Θ|≤
        C*(maximalBudget ω : ℝ)*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Derive true uniform vector and norm derivative bounds for both actual source methods without a final-error denominator.
  obtain ⟨δM,CM,hδM,hCM,hM⟩ := compact_budget_norm_envelope M base g N hN K hK hb hpos hg hcount
  obtain ⟨δL,CL,hδL,hCL,hL⟩ := compact_budget_norm_envelope L base g N hN K hK hb hpos hg hcount
  obtain ⟨JM,hJM,hjM⟩ := compact_scenario_derivative_bound M base g N hN K hK hb hpos hg hcount
  obtain ⟨JL,hJL,hjL⟩ := compact_scenario_derivative_bound L base g N hN K hK hb hpos hg hcount
  refine ⟨min (min δM δL) 1,JM+JL+CM+CL,lt_min (lt_min hδM hδL) zero_lt_one,by positivity,?_⟩
  intro x hx ω hω Θ hΘ
  let w : ℝ := maximalBudget ω
  let e0 := ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖
  have hw0 : 0≤w := (maximalBudget ω).coe_nonneg
  have hw1 : w≤1 := hω.trans (min_le_right _ _)
  have hn : ‖Θ‖≤w := scenarioBudget_norm_le ω Θ hΘ
  have hsmall : w≤min δM δL := hω.trans (min_le_left _ _)
  have hm := hM x hx ω (hsmall.trans (min_le_left _ _)) Θ hΘ
  have hl := hL x hx ω (hsmall.trans (min_le_right _ _)) Θ hΘ
  -- Genuine explored projections contract the actual canonical first derivatives on the true source scenario.
  have hνM : ‖scenarioVariation M.policy (base x) (g x) N Θ‖≤JM*w*e0 := by
    apply ((exploredFlag (base x) (g x) N).norm_starProjection_apply_le _).trans
    apply (hjM x hx Θ).trans
    gcongr
  have hνL : ‖scenarioVariation L.policy (base x) (g x) N Θ‖≤JL*w*e0 := by
    apply ((exploredFlag (base x) (g x) N).norm_starProjection_apply_le _).trans
    apply (hjL x hx Θ).trans
    gcongr
  -- The real common component is orthogonal to both genuine explored variations, including actual exhausted references.
  have he := orthogonal_norm_comparison
    (cgCanonicalError (base x) (g x) N+scenarioUnexplored (base x) (g x) N Θ)
    (scenarioVariation M.policy (base x) (g x) N Θ) (scenarioVariation L.policy (base x) (g x) N Θ)
    (scenarioEnvelope_orthogonal (base x) (hpos x hx).self_of_nhds (g x) N (hcount x hx) M.policy Θ)
    (scenarioEnvelope_orthogonal (base x) (hpos x hx).self_of_nhds (g x) N (hcount x hx) L.policy Θ)
  have he' : |scenarioEnvelope M.policy (base x) (g x) N Θ-scenarioEnvelope L.policy (base x) (g x) N Θ|≤
      (JM+JL)*w*e0 := by
    apply he.trans
    apply max_le
    · exact hνM.trans (by nlinarith [mul_nonneg hJL (mul_nonneg hw0 (norm_nonneg (cgOperator (metricRoot (base x))⁻¹ (g x))))])
    · exact hνL.trans (by nlinarith [mul_nonneg hJM (mul_nonneg hw0 (norm_nonneg (cgOperator (metricRoot (base x))⁻¹ (g x))))])
  -- Retain both actual finite-output remainders, then absorb their genuine quadratic budgets into the true first-order radius.
  have hsplit : actualScenarioNorm M.policy (base x) (g x) N Θ-actualScenarioNorm L.policy (base x) (g x) N Θ=
      (actualScenarioNorm M.policy (base x) (g x) N Θ-scenarioEnvelope M.policy (base x) (g x) N Θ)+
      (scenarioEnvelope M.policy (base x) (g x) N Θ-scenarioEnvelope L.policy (base x) (g x) N Θ)-
      (actualScenarioNorm L.policy (base x) (g x) N Θ-scenarioEnvelope L.policy (base x) (g x) N Θ) := by ring
  rw [hsplit]
  apply (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hm he')) hl).trans _)
  have hsq : w^2≤w := by nlinarith
  calc
    _ =(JM+JL)*w*e0+(CM+CL)*w^2*e0 := by ring
    _ ≤(JM+JL)*w*e0+(CM+CL)*w*e0 := by gcongr
    _ = _ := by ring
end
end krylov.Envelope
