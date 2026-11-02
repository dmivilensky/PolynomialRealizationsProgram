import krylov.ContinuumControl.SmoothIdentity
import krylov.LotkaVolterra.GlobalGraphAnalyticAll
import krylov.LotkaVolterra.GlobalEndpointAnalytic

/-!
Article: main_krylov, apC:eq:f and thm:value.
Use: supply the Bellman and BV arguments with the actual constructed analytic
graphs for every 0<γ≤1. The graph equation is multiplied before use at the
subcritical saddle; the endpoint graph has a genuine open analytic extension.
Source: the global shooting, analytic matching and rational ODE theorems.
-/

namespace krylov.ContinuumControl
noncomputable section
open Set Filter
open krylov.LotkaVolterra
open scoped Topology

/-- The constructed subcritical graph satisfies the exact Bellman graph
identity, including its stationary saddle point. -/
theorem subcritical_feedbackGraphAt {γ r : ℝ} (G : SubcriticalGraph γ)
    (hγ : 0 < γ) (hγ₁ : γ < 1) (hr : 0 < r) : FeedbackGraphAt γ G.σ r := by
  have ha := G.analyticAt hγ hγ₁ hr
  refine ⟨G.positive hγ hγ₁ hr, ha.differentiableAt, ?_⟩
  by_cases heq : r = saddleU γ
  · subst r
    rw [G.saddle, saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)]
    have hs := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
    rw [saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)] at hs
    rw [show saddleS γ + 1 - (saddleS γ + 1) = 0 by ring,
      show saddleS γ - 1 - γ * (saddleS γ + 1) = 0 by linarith [hs]]
    ring
  · rw [(G.derivative r hr heq).deriv]
    have hden : G.σ r + 1 - r ≠ 0 := by
      rcases lt_or_gt_of_ne heq with hlo | hhi
      · linarith [(G.lower r ⟨hr, hlo⟩).2.2]
      · linarith [(G.upper r hhi).2.2]
    field_simp

/-- Every source parameter admits a genuine positive analytic Bellman graph.
This is an existence theorem derived from shooting, not a graph certificate
assumed as part of a string's admissibility. -/
theorem exists_analytic_feedbackGraph {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) :
    ∃ σ : ℝ → ℝ, (∀ r ≥ 1, AnalyticAt ℝ σ r) ∧
      ∀ r ≥ 1, FeedbackGraphAt γ σ r := by
  rcases eq_or_lt_of_le hγ₁ with rfl | hlt
  · obtain ⟨σ, ε, hε, ha, hb⟩ := exists_analytic_endpoint_graph
    refine ⟨σ, fun r hr ↦ (ha r (by linarith)).1, fun r hr ↦ ?_⟩
    have hd := ha r (by linarith)
    refine ⟨hd.2.1, hd.1.differentiableAt, ?_⟩
    rw [hd.2.2.2.deriv]
    have hr₀ : r ≠ 0 := by linarith
    have hden : σ r + 1 - r ≠ 0 := ne_of_gt hd.2.2.1
    field_simp
  · obtain ⟨G⟩ := exists_subcriticalGraph hγ hlt
    exact ⟨G.σ, fun r hr ↦ G.analyticAt hγ hlt (by linarith),
      fun r hr ↦ subcritical_feedbackGraphAt G hγ hlt (by linarith)⟩

/-- Any actual endpoint graph in the strict shooting corridor gives an
actual solution of the scalar gap equation. -/
theorem endpoint_gap_of_graph {σ : ℝ → ℝ}
    (hb : ∀ r ≥ 1, r + 1 < σ r ∧ σ r < r + 3)
    (hd : ∀ r ≥ 1, HasDerivAt σ
      (2 * σ r * (σ r - 1 - r) / (r * (σ r + 1 - r))) r) :
    ∀ r ≥ 1, (σ r - r) ∈ Icc (1 : ℝ) 3 ∧
      HasDerivAt (fun r ↦ σ r - r) (endpointGraphRate r (σ r - r)) r := by
  intro r hr
  have hh := hb r hr
  refine ⟨⟨by linarith [hh.1], by linarith [hh.2]⟩, ?_⟩
  have hr₀ : r ≠ 0 := by linarith
  have hden : σ r - r + 1 ≠ 0 := by linarith [hh.1]
  have hrate : 2 * σ r * (σ r - 1 - r) / (r * (σ r + 1 - r)) - 1 =
      endpointGraphRate r (σ r - r) := by
    rw [endpointGraphRate_eq hr₀ hden]
    have hid : σ r + 1 - r = σ r - r + 1 := by ring
    rw [hid]
    field_simp
    ring
  rw [← hrate]
  convert! (hd r hr).sub (hasDerivAt_id r) using 1

/-- The analytic endpoint extension agrees with every genuine shooting gap
on the physical domain. It can therefore be used for the very same candidate
mass constructed from that orbit. -/
theorem endpoint_graph_eq_of_gap {σ e : ℝ → ℝ}
    (hb : ∀ r ≥ 1, r + 1 < σ r ∧ σ r < r + 3)
    (hd : ∀ r ≥ 1, HasDerivAt σ
      (2 * σ r * (σ r - 1 - r) / (r * (σ r + 1 - r))) r)
    (he : ∀ r ≥ 1, e r ∈ Icc (1 : ℝ) 3 ∧
      HasDerivAt e (endpointGraphRate r (e r)) r) :
    ∀ r ≥ 1, σ r = r + e r := by
  have heq := endpoint_graph_gap_unique (endpoint_gap_of_graph hb hd) he
  intro r hr
  have h := heq hr
  dsimp at h
  linarith

end
end krylov.ContinuumControl
