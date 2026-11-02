import krylov.Asymptotics.LogLipschitz

/-!
Article: main_krylov, apC:lem:B.
Use: existence of an actual analytic separating graph with the sharp
logarithmic Lipschitz bound for every source exponent, including γ=1.
Source: the constructed subcritical and endpoint graphs from stage 9.
-/

/-!
Article: krylov, Lemma D.19 [apC:lem:B].

The constructed subcritical/endpoint graphs satisfy the sharp logarithmic slope bound
throughout r≥1, including the saddle via its analytic derivative.
The derivative quotient is interpreted continuously at the saddle, as in the article;
graphBound has the special endpoint value 1/2.
-/

namespace krylov.Asymptotics
noncomputable section
open krylov.LotkaVolterra krylov.ContinuumControl

/-- The full graph regularity used by the discrete-to-continuum proof is
proved for an actually constructed graph for every source exponent. -/
theorem exists_analytic_logLipschitz_graph {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) :
    ∃ σ : ℝ → ℝ, (∀ r ≥ 1, AnalyticAt ℝ σ r) ∧
      (∀ r ≥ 1, FeedbackGraphAt γ σ r) ∧
      (∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ graphBound γ) := by
  rcases eq_or_lt_of_le hγ₁ with rfl | hlt
  · obtain ⟨σ, ε, hε, ha, hb⟩ := exists_analytic_endpoint_graph
    have hd (r : ℝ) (hr : 1 ≤ r) := (ha r (by linarith)).2.2.2
    refine ⟨σ, fun r hr ↦ (ha r (by linarith)).1, ?_, ?_⟩
    · intro r hr
      have hh := ha r (by linarith)
      refine ⟨hh.2.1, hh.1.differentiableAt, ?_⟩
      rw [(hd r hr).deriv]
      have hrn : r ≠ 0 := by linarith
      have hden := hh.2.2.1.ne'
      field_simp
    · intro r hr
      simpa only [graphBound, lt_self_iff_false, ite_false] using
        endpoint_logSlope_bounds (fun r hr ↦ ⟨(hb r hr).1, (hb r hr).2.1⟩) hd hr
  · obtain ⟨G⟩ := exists_subcriticalGraph hγ hlt
    refine ⟨G.σ, fun r hr ↦ G.analyticAt hγ hlt (by linarith),
      fun r hr ↦ subcritical_feedbackGraphAt G hγ hlt (by linarith), ?_⟩
    intro r hr
    simpa only [graphBound, hlt, ite_true] using
      SubcriticalGraph.logSlope_bounds G hγ hlt (show 0 < r by linarith)

end
end krylov.Asymptotics
