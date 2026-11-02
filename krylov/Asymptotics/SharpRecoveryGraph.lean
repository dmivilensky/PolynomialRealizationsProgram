import krylov.Asymptotics.OptimizerRecoveryState

/-!
Article: main_krylov, thm:limit, matching sharp upper and lower constants.
Use: one and the same actually constructed separating graph has the sharp
logarithmic slope bound and supplies genuine compact smooth recovery states
arbitrarily close to its Bellman value. Both gamma branches are constructed.
Source: stage-9 global shooting, analytic graph regularity and actual optimizer
quadratures, together with the proved physical-to-type reward identity.
-/
namespace krylov.Asymptotics
noncomputable section
open Set Real Filter MeasureTheory
open krylov.Strings krylov.Strings.OptimizerQuadratures
open krylov.LotkaVolterra krylov.ContinuumControl
open scoped Topology

/-- At the endpoint the two independently used potential formulas are the
same actual function, including all quadrature normalizations. -/
theorem physicalOrbitValue_one (s U : ℝ → ℝ) :
    physicalOrbitValue 1 s U = physicalEndpointValue s U := by
  funext x
  simp only [physicalOrbitValue, orbitValue, physicalEndpointValue, endpointOrbitValue,
    rpow_neg_one, div_eq_mul_inv, mul_inv_rev]
  ring

/-- A single genuine graph gives both the discrete sharp upper bound and
actual smooth near-optimal recovery states, for every source exponent. -/
theorem exists_sharp_recovery_graph {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) :
    ∃ σ : ℝ → ℝ, (∀ r ≥ 1, AnalyticAt ℝ σ r) ∧
      (∀ r ≥ 1, FeedbackGraphAt γ σ r) ∧
      (∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ graphBound γ) ∧
      ∀ ε > (0 : ℝ), ∃ Y > (0 : ℝ), ∃ R : RecoveryState Y,
        feedbackValue γ σ 1 - ε < ∫ y in 0..Y, R.energy y ^ (-γ) := by
  rcases eq_or_lt_of_le hγ₁ with rfl | hlt
  · obtain ⟨σ, ε₀, hε₀, ha, hb⟩ := exists_analytic_endpoint_graph
    have hd (r : ℝ) (hr : 1 ≤ r) := (ha r (by linarith)).2.2.2
    have hgraph : ∀ r ≥ 1, FeedbackGraphAt 1 σ r := by
      intro r hr
      have hh := ha r (by linarith)
      refine ⟨hh.2.1, hh.1.differentiableAt, ?_⟩
      rw [(hd r hr).deriv]
      have hrn : r ≠ 0 := by linarith
      have hden := hh.2.2.1.ne'
      field_simp
    refine ⟨σ, fun r hr ↦ (ha r (by linarith)).1, hgraph, ?_, ?_⟩
    · intro r hr
      simpa only [graphBound, lt_self_iff_false, ite_false] using
        endpoint_logSlope_bounds (fun r hr ↦ ⟨(hb r hr).1, (hb r hr).2.1⟩) hd hr
    · intro ε hε
      obtain ⟨e, he, s, U, hs, hU, hU₀, hs₂, hode, hc, hpath⟩ := exists_endpoint_data_with_graph
      have hp : ∀ t, 0 < s t := fun t ↦ lt_of_lt_of_le (by norm_num) (hs₂ t)
      have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ by linarith [hs₂ t]
      have hcorr : ∀ t ≥ 0, 1 ≤ U t ∧ U t + 1 ≤ s t ∧ s t ≤ 4 * U t := by
        intro t ht
        have hexp : 1 ≤ exp (2 * t) := one_le_exp_iff.mpr (by positivity)
        exact ⟨hexp.trans (hc t ht).2.2.2, (hc t ht).1.le, (hc t ht).2.2.1⟩
      have hUp : ∀ t ≥ 0, 0 < U t := fun t ht ↦ zero_lt_one.trans_le (hcorr t ht).1
      have hUinf : Tendsto U atTop atTop := by
        apply tendsto_atTop_mono' atTop
          ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht ↦ (hc t ht).2.2.2))
        exact Real.tendsto_exp_atTop.comp
          (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
      have hcross : s 0 = σ 1 := by
        have hh := hpath 0 le_rfl
        rw [hU₀] at hh
        rw [endpoint_graph_eq_of_gap (fun r hr ↦ ⟨(hb r hr).1, (hb r hr).2.1⟩) hd he 1 le_rfl]
        exact hh
      have ht : Tendsto (physicalOrbitValue 1 s U) atTop (𝓝 0) := by
        rw [physicalOrbitValue_one]
        exact physicalEndpointValue_tendsto_zero hs hp h₁ hcorr hUinf
      obtain ⟨Y, hY, R, hR⟩ := exists_optimizerRecoveryState_near_value (by norm_num : (1 : ℝ) ≠ 0)
        hs hU hp h₁ hU₀ hUp (by simpa only [one_mul] using hode) ht hε
      refine ⟨Y, hY, R, ?_⟩
      rw [feedbackValue_one 1 σ (hgraph 1 le_rfl).positive, ← hcross]
      exact hR
  · obtain ⟨G⟩ := exists_subcriticalGraph hγ hlt
    refine ⟨G.σ, fun r hr ↦ G.analyticAt hγ hlt (by linarith),
      fun r hr ↦ subcritical_feedbackGraphAt G hγ hlt (by linarith), ?_, ?_⟩
    · intro r hr
      simpa only [graphBound, hlt, ite_true] using
        SubcriticalGraph.logSlope_bounds G hγ hlt (show 0 < r by linarith)
    · intro ε hε
      obtain ⟨s, U, hs, hU, hU₀, hpos, hUone, _hcorr, hode, hsinf, hUinf,
        _hexp, hcanonical, _hpath⟩ := exists_subcritical_data hγ hlt
      have hp : ∀ t, 0 < s t := fun t ↦ zero_lt_one.trans (hpos t).1
      have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ (hpos t).1.le
      have ht := (orbitValue_tendsto_zero_of_finite_state hγ (saddleS_pos hγ hlt)
        (saddleU_pos hlt) hsinf hUinf (expPrimitive_tendsto_atTop hU hUone)).comp
          (inverseClock_tendsto_atTop hs hp h₁)
      obtain ⟨Y, hY, R, hR⟩ := exists_optimizerRecoveryState_near_value hγ.ne'
        hs hU hp h₁ hU₀ (fun t _ ↦ (hpos t).2) (fun t _ ↦ hode t) ht hε
      refine ⟨Y, hY, R, ?_⟩
      rw [feedbackValue_one γ G.σ (subcritical_feedbackGraphAt G hγ hlt zero_lt_one).positive,
        ← hcanonical G]
      exact hR

end
end krylov.Asymptotics
