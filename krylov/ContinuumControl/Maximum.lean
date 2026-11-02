import krylov.ContinuumControl.CanonicalGraph
import krylov.ContinuumBV.FiniteRewardBound
import krylov.Strings.OptimizerOrbitAttainment

/-!
Article: main_krylov, thm:value, the attained global continuum value.
Use: assemble the actual constructed graphs, the unrestricted BV upper bound
and the genuine RN-defined attaining masses. State admissibility contains
only continuity, normalization and the original Volterra equation.
Source: the proved general state construction, fundamental identity and shooting.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open krylov.ContinuumControl krylov.ContinuumBV krylov.LotkaVolterra
open scoped Topology NNReal ENNReal

/-- The source's normalized position equation, with slope and energy
reconstructed from its actual mass. Positivity and monotonicity are derived. -/
def IsState (M : Mass) (φ : ℝ → ℝ) : Prop :=
  Continuous φ ∧ φ 0 = 1 ∧
    ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t

/-- Actual reward is independent of any extension to negative positions. -/
theorem Mass.reward_eq_of_eqOn (M : Mass) (γ : ℝ) {φ ψ : ℝ → ℝ}
    (h : EqOn φ ψ (Ici 0)) : M.reward γ φ = M.reward γ ψ := by
  rw [Mass.reward_eq_iSup_prefix, Mass.reward_eq_iSup_prefix]
  congr 1
  funext n
  exact M.rewardPrefix_eq_of_eqOn γ (fun _ ht ↦ h ht.1)

/-- Universal half-line bound from the original state equation alone.
Monotonicity is derived by comparison with the constructed unique state. -/
theorem IsState.reward_le {M : Mass} {φ : ℝ → ℝ} (h : IsState M φ)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r) :
    M.reward γ φ ≤ ENNReal.ofReal (feedbackValue γ σ 1) := by
  obtain ⟨ψ, hc, h₀, hm, _, he⟩ := M.exists_global_state
  rw [M.reward_eq_of_eqOn γ (M.global_state_unique h.1 hc h.2.2 he)]
  exact actual_reward_le M hc hm h₀ he hγ hσ hgraph

/-- Rewriting a genuine physical coordinate solution gives the original
Volterra state, without a feedback or regularity certificate in admissibility. -/
theorem isState_of_coordinates (M : Mass) {φ p : ℝ → ℝ}
    (hc : Continuous φ) (h₀ : φ 0 = 1)
    (he : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, p t ∧
      p x = integralSlope M.measure φ x) : IsState M φ := by
  refine ⟨hc, h₀, fun x hx ↦ ?_⟩
  rw [(he x hx).1]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  exact (he t ht.1.le).2

namespace OptimizerQuadratures

/-- The actual endpoint candidate attains the crossing value of any named
analytic endpoint graph. Scalar gap uniqueness supplies the exact association. -/
theorem endpoint_attainment_for_graph {σ : ℝ → ℝ}
    (hb : ∀ r ≥ 1, r + 1 < σ r ∧ σ r < r + 3)
    (hd : ∀ r ≥ 1, HasDerivAt σ
      (2 * σ r * (σ r - 1 - r) / (r * (σ r + 1 - r))) r) :
    ∃ M : Mass, ∃ φ : ℝ → ℝ, IsState M φ ∧
      M.reward 1 φ = ENNReal.ofReal (Real.sqrt (σ 1) / 2) := by
  obtain ⟨e, he, s, U, hs, hU, hU₀, hs₂, hode, hc, hgraph⟩ := exists_endpoint_data_with_graph
  have hp : ∀ t, 0 < s t := fun t ↦ lt_of_lt_of_le (by norm_num) (hs₂ t)
  have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ by linarith [hs₂ t]
  have hcorr : ∀ t ≥ 0, 1 ≤ U t ∧ U t + 1 ≤ s t ∧ s t ≤ 4 * U t := by
    intro t ht
    have hexp : 1 ≤ Real.exp (2 * t) := Real.one_le_exp_iff.mpr (by positivity)
    exact ⟨hexp.trans (hc t ht).2.2.2, (hc t ht).1.le, (hc t ht).2.2.1⟩
  have hUinf : Tendsto U atTop atTop := by
    apply tendsto_atTop_mono' atTop
      ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht ↦ (hc t ht).2.2.2))
    exact Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hcross : s 0 = σ 1 := by
    have hh := hgraph 0 le_rfl
    rw [hU₀] at hh
    rw [endpoint_graph_eq_of_gap hb hd he 1 le_rfl]
    exact hh
  obtain ⟨hφ, _, _⟩ := extended_coordinates_continuous hs hU hp h₁
  obtain ⟨hφ₀, _, _⟩ := extended_initial (U := U) hs hp
  refine ⟨constructedMass s hs hp h₁, extendedPosition s,
    isState_of_coordinates _ (p := extendedSlope s) hφ hφ₀ (fun x hx ↦ ?_), ?_⟩
  · obtain ⟨hφx, hpx, _⟩ := constructedMass_state hs hU hp h₁ hU₀
      (fun t ht ↦ (hode t ht).2) hx
    exact ⟨hφx, hpx⟩
  · rw [constructedMass_reward hs hU hp h₁ hU₀ hode hcorr hUinf, hcross]

end OptimizerQuadratures

/-- The continuum maximum is attained for every 0<γ≤1 by an actual mass.
The inequality quantifies over all actual admissible half-line strings,
including atoms, singular continuous mass and zero-density intervals. -/
theorem exists_actual_continuum_maximum {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) :
    ∃ σ : ℝ → ℝ,
      (∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt γ σ r) ∧
      ∃ M : Mass, ∃ φ : ℝ → ℝ, IsState M φ ∧
        M.reward γ φ = ENNReal.ofReal (Real.sqrt (σ 1) / (2 * γ)) ∧
        ∀ N : Mass, ∀ ψ : ℝ → ℝ, IsState N ψ → N.reward γ ψ ≤ M.reward γ φ := by
  have hfinish (σ : ℝ → ℝ)
      (hσ : ∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt γ σ r)
      (ha : ∃ M : Mass, ∃ φ : ℝ → ℝ, IsState M φ ∧
        M.reward γ φ = ENNReal.ofReal (Real.sqrt (σ 1) / (2 * γ))) :
      ∃ σ : ℝ → ℝ,
        (∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt γ σ r) ∧
        ∃ M : Mass, ∃ φ : ℝ → ℝ, IsState M φ ∧
          M.reward γ φ = ENNReal.ofReal (Real.sqrt (σ 1) / (2 * γ)) ∧
          ∀ N : Mass, ∀ ψ : ℝ → ℝ, IsState N ψ → N.reward γ ψ ≤ M.reward γ φ := by
    obtain ⟨M, φ, hstate, hvalue⟩ := ha
    refine ⟨σ, hσ, M, φ, hstate, hvalue, fun N ψ hN ↦ ?_⟩
    rw [hvalue, ← feedbackValue_one γ σ (hσ 1 le_rfl).2.positive]
    exact hN.reward_le hγ (fun r hr ↦ (hσ r hr).1.contDiffAt) (fun r hr ↦ (hσ r hr).2)
  rcases eq_or_lt_of_le hγ₁ with rfl | hlt
  · obtain ⟨σ, ε, hε, ha, hb⟩ := exists_analytic_endpoint_graph
    have hgraphs : ∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt 1 σ r := by
      intro r hr
      have hh := ha r (by linarith)
      refine ⟨hh.1, hh.2.1, hh.1.differentiableAt, ?_⟩
      rw [hh.2.2.2.deriv]
      have hr₀ : r ≠ 0 := by linarith
      have hden : σ r + 1 - r ≠ 0 := hh.2.2.1.ne'
      field_simp
    apply hfinish σ hgraphs
    simpa only [mul_one] using OptimizerQuadratures.endpoint_attainment_for_graph
      (fun r hr ↦ ⟨(hb r hr).1, (hb r hr).2.1⟩)
      (fun r hr ↦ (ha r (by linarith)).2.2.2)
  · obtain ⟨G⟩ := exists_subcriticalGraph hγ hlt
    apply hfinish G.σ (fun r hr ↦ ⟨G.analyticAt hγ hlt (by linarith),
      subcritical_feedbackGraphAt G hγ hlt (by linarith)⟩)
    obtain ⟨s₀, _, hcross, M, φ, p, K, v, hc, _, hz, _, _, _, he, _, _, _, hvalue⟩ :=
      OptimizerQuadratures.exists_actual_global_subcritical_attainment hγ hlt
    refine ⟨M, φ, isState_of_coordinates M (p := p) hc hz (fun x hx ↦
      ⟨(he x hx).1, (he x hx).2.1⟩), ?_⟩
    rw [hvalue, hcross G]

end
end krylov.Strings
