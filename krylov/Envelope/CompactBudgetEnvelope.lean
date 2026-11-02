import krylov.Envelope.ActualScenarioNorm

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and s3:cor:qn, true budget-uniform actual norm envelope.
Use: specialize the genuine compact actual source-cycle remainder to all
independent symmetric spectral budget profiles with one real common radius.
Source: actual finite-scenario Taylor remainder, genuine source budget
product norm bounds and the true norm reverse triangle inequality.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator NNReal
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The actual finite-output gradient norm of every genuine smooth method has a true compact-uniform first-jet envelope with remainder bounded by the largest actual source budget squared times the real initial error.
Use: The actual finite-output gradient norm of every genuine smooth method has a true compact-uniform first-jet envelope with remainder bounded by the largest actual source budget squared times the real initial error.
Article: main_krylov, thm:E and s3:cor:qn, true budget-uniform actual norm envelope.
Proof: Use the actual finite-scenario vector remainder, the genuine scenario norm bound by the real largest budget, and the true reverse triangle inequality. -/
theorem compact_budget_norm_envelope (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 0<N) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K), N≤referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ ω : Fin (N-1) → ℝ≥0,
      (maximalBudget ω : ℝ)≤δ → ∀ Θ∈scenarioBudget N ω,
        |actualScenarioNorm M.policy (base x) (g x) N Θ-scenarioEnvelope M.policy (base x) (g x) N Θ|≤
          C*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
  -- The same real compact tube applies to every genuine budget profile; only the actual scenario norm is enlarged to its true budget radius.
  obtain ⟨δ,C,hδ,hC,ht⟩ := compact_scenario_taylor M base g N hN K hK hb hpos hg hcount
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx ω hω Θ hΘ
  have hn := scenarioBudget_norm_le ω Θ hΘ
  have hbnd := ht x hx Θ (hn.trans hω)
  have hscale : C*‖Θ‖^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖≤
      C*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
    gcongr
  exact (actualScenarioNorm_envelope_bound M.policy (base x) (g x) N Θ).trans (hbnd.trans hscale)
end
end krylov.Envelope
