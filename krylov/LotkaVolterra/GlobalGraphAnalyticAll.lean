import krylov.LotkaVolterra.AnalyticGraphField
import krylov.LotkaVolterra.GlobalGraphAnalytic

/-!
Article: main_krylov, apC:prop:LV, the analytic global stable graph.
Use: combine analytic regular-singular matching at the saddle with actual
rational ODE analyticity on each of the two global branches.
Source: the separately proved analytic saddle construction and analytic Picard
regularity for the concrete rational graph field.
-/

namespace krylov.LotkaVolterra.SubcriticalGraph
noncomputable section
open Set Filter
open scoped Topology

/-- The actual globally constructed stable graph is analytic at every
positive U, including the saddle. -/
theorem analyticAt {γ : ℝ} (G : SubcriticalGraph γ) (hγ : 0 < γ) (hγ₁ : γ < 1)
    {U : ℝ} (hU : 0 < U) : AnalyticAt ℝ G.σ U := by
  by_cases hUF : U = saddleU γ
  · simpa only [hUF] using G.analyticAt_saddle hγ hγ₁
  have hden : G.σ U + 1 - U ≠ 0 := by
    rcases lt_or_gt_of_ne hUF with hlo | hhi
    · have hh := (G.lower U ⟨hU, hlo⟩).2.2
      linarith
    · have hh := (G.upper U hhi).2.2
      linarith
  apply analyticAt_graph_solution hU.ne' hden
  filter_upwards [Ioi_mem_nhds hU, eventually_ne_nhds hUF] with V hV hVF
  exact G.derivative V hV hVF

end
end krylov.LotkaVolterra.SubcriticalGraph
