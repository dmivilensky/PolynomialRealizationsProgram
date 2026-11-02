import krylov.Envelope.CompactBudgetEnvelope

set_option autoImplicit false
/-!
Article: Corollary B.20 [s3:cor:qn] of krylov.tex.
Use: compare the genuine finite-output RFC worst canonical gradient norm
to every fixed actual smooth source method, uniformly on true compact
reference families and all sufficiently small real source budget profiles.
Source: proved actual compact budget-weighted norm envelopes and genuine
budget-preserving absorbed information fibres, with true finite supremum bounds.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator NNReal
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The genuine worst actual RFC output norm is at most that of every fixed true smooth source method plus a compact-uniform largest-budget-squared initial-error remainder.
Use: The genuine worst actual RFC output norm is at most that of every fixed true smooth source method plus a compact-uniform largest-budget-squared initial-error remainder.
Article: main_krylov, s3:cor:qn, actual compact-uniform worst-gradient comparison.
Proof: Use the actual two methods common compact tubes. Each real RFC scenario has a genuine feasible absorbed competitor with exactly the same first-jet envelope. Both actual norm remainders give the pointwise comparison; a true compact first-jet maximum proves the real nonlinear norm image bounded, so the genuine scenario suprema preserve the estimate. -/
theorem rfc_compact_worst_norm_comparison (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K), N≤referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ ω : Fin (N-1) → ℝ≥0,
      (maximalBudget ω : ℝ)≤δ →
      worstScenarioNorm (rfcMethod fullMemory 1) (base x) (g x) N ω≤
        worstScenarioNorm M.policy (base x) (g x) N ω+
          C*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Obtain genuine compact output remainder constants for the actual RFC executor and the fixed real competitor.
  let F := smoothRFCClass fullMemory (fun _ hk => hk) 1 (E := EuclideanSpace ℝ (Fin n))
  obtain ⟨δR,CR,hδR,hCR,hR⟩ := compact_budget_norm_envelope F base g N (by omega) K hK hb hpos hg hcount
  obtain ⟨δM,CM,hδM,hCM,hM⟩ := compact_budget_norm_envelope M base g N (by omega) K hK hb hpos hg hcount
  refine ⟨min δR δM,CR+CM,lt_min hδR hδM,add_nonneg hCR hCM,?_⟩
  intro x hx ω hω
  have hr := hR x hx ω (hω.trans (min_le_left _ _))
  have hm := hM x hx ω (hω.trans (min_le_right _ _))
  -- Derive real nonlinear output boundedness from the actual envelope; no nonlinear maximizer is assumed.
  have hbounded := actualScenarioNorm_bddAbove M.policy (base x) (g x) N ω
    (CM*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖) hm
  apply csSup_le
  · exact ⟨_,0,scenarioBudget_zero_mem ω,rfl⟩
  · rintro r ⟨Θ,hΘ,rfl⟩
    -- The actual absorbed scenario stays in every true budget and forces the genuine RFC first-jet envelope for the real competing method.
    have hΞ := absorbedScenario_budget (base x) (g x) ω Θ hΘ
    have hc := actualScenarioNorm_absorption_comparison M (base x) (hpos x hx).self_of_nhds (g x) N hN
      (hcount x hx) Θ (fun i => (hΘ.1 i).1)
      (CR*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖)
      (CM*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖) (hr Θ hΘ) (hm _ hΞ)
    have hs : actualScenarioNorm M.policy (base x) (g x) N (absorbedScenario (base x) (g x) Θ)≤
        worstScenarioNorm M.policy (base x) (g x) N ω := le_csSup hbounded ⟨_,hΞ,rfl⟩
    calc
      _ ≤ actualScenarioNorm M.policy (base x) (g x) N (absorbedScenario (base x) (g x) Θ)+
          (CR*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖+
          CM*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖) := hc
      _ ≤ worstScenarioNorm M.policy (base x) (g x) N ω+
          (CR*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖+
          CM*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖) := add_le_add hs le_rfl
      _ = _ := by ring
end
end krylov.Envelope
