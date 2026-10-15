import «2610.05164v2».LocalObstruction.ObservationFunctions

/-!
Article: 2610.05164v2, Lemma 26.
The common parameter neighborhood in Lemma 26(i).
Result: `«2610.05164v2».LocalObstruction.observation_analytic_neighborhood` supplies the stated
article conclusion.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Filters
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

 /--
Constructs witnesses with the exact properties `∃ δ : ℝ, 0<δ ∧ (∀ a ∈ Metric.ball (0:ι → ℝ) δ,
∀ x,0<perturb m v a x) ∧ AnalyticOnNhd ℝ (fun p : (ι → ℝ) × ℝ => observationH (perturb m v p.1)
p.2) (Metric.ball (0:ι → ℝ) δ ×ˢ Ioi 0) ∧ ContDiffOn ℝ 1 (fun p : (ι → ℝ) × ℝ => observationS
(perturb m v p.1) p.2) (Metric.ball (0:ι → ℝ) δ ×ˢ Ioi 0)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 26.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem observation_analytic_neighborhood {ι : Type*} [Fintype ι]
    {m : ℝ → ℝ} {v : ι → ℝ → ℝ} (hm : Integrable m) (hc : Continuous m) (hn : ∀ x,0<m x)
    (hv : ∀ i,Integrable (v i)) (hvc : ∀ i,Continuous (v i)) (hcomp : ∀ i,HasCompactSupport (v i)) :
    ∃ δ : ℝ, 0<δ ∧ (∀ a ∈ Metric.ball (0:ι → ℝ) δ, ∀ x,0<perturb m v a x) ∧
      AnalyticOnNhd ℝ (fun p : (ι → ℝ) × ℝ => observationH (perturb m v p.1) p.2)
        (Metric.ball (0:ι → ℝ) δ ×ˢ Ioi 0) ∧
      ContDiffOn ℝ 1 (fun p : (ι → ℝ) × ℝ => observationS (perturb m v p.1) p.2)
        (Metric.ball (0:ι → ℝ) δ ×ˢ Ioi 0) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (finite_perturbation_positive hc hn hvc hcomp)
  have hH : AnalyticOnNhd ℝ (fun p : (ι → ℝ) × ℝ => observationH (perturb m v p.1) p.2)
      (Metric.ball (0:ι → ℝ) δ ×ˢ Ioi 0) := by
    intro p hp
    have hT : 0<perturbTransmission hm hv p := by
      rw [perturbTransmission_actual hm hv p (fun x => (hsub hp.1 x).le) hp.2.le]
      exact zero_lt_one.trans_le (transmission_ge_one (perturb_integrable hm hv p.1)
        (fun x => (hsub hp.1 x).le) hp.2.le)
    have hlog := (analyticAt_log hT).comp (f := perturbTransmission hm hv)
      (perturbTransmission_signed_analytic hm hv p)
    apply hlog.congr
    have hball := continuous_fst.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp.1)
    have hscale := (continuous_snd.tendsto p).eventually (Ioi_mem_nhds (show 0<p.2 from hp.2))
    filter_upwards [hball,hscale] with q hq hqs
    dsimp only [Function.comp_def]
    rw [perturbTransmission_actual hm hv q (fun x => (hsub hq x).le) hqs.le]
    rfl
  refine ⟨δ,hδ,hsub,hH,?_⟩
  intro p hp
  exact (parameter_derivative_c1 (hH p hp).contDiffAt).contDiffWithinAt

end
end «2610.05164v2».LocalObstruction
