import krylov.LotkaVolterra.GlobalFullSaddleGraphs
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: `main_krylov`, `apC:prop:LV`, the full continuous separating graph.

The two globally constructed branches are joined at the equilibrium. Their
sharp wedges imply continuity there without an assumed stable-manifold
theorem. The graph is strictly increasing and crosses `U=1` exactly once.
Analytic regularity through the equilibrium is handled separately.
-/

/-!
Article: krylov, Proposition D.11 [apC:prop:LV].

The global graph is constructed, analytic across the saddle, and exactly the positive stable
set. Actual finite first exits identify both sides of the crossing.
Exit classification applies to interior starts 0<s<s_F, as now stated. The graph definition
includes both lower and upper branch wedges.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

structure SubcriticalGraph (γ : ℝ) where
  σ : ℝ → ℝ
  saddle : σ (saddleU γ) = saddleS γ
  lower : ∀ U ∈ Ioo (0 : ℝ) (saddleU γ),
    1 + γ * U < σ U ∧ σ U < saddleS γ ∧ U - 1 < σ U
  upper : ∀ U > saddleU γ,
    saddleS γ < σ U ∧ σ U < 1 + γ * U ∧ σ U < U - 1
  derivative : ∀ U > 0, U ≠ saddleU γ →
    HasDerivAt σ (2 * σ U * (σ U - 1 - γ * U) / (U * (σ U + 1 - U))) U

theorem exists_subcriticalGraph {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    Nonempty (SubcriticalGraph γ) := by
  obtain ⟨lo, hlo⟩ := exists_global_lower_graph hγ hγ₁
  obtain ⟨hi, hhi⟩ := exists_global_upper_graph hγ hγ₁
  let σ : ℝ → ℝ := fun U ↦ if U < saddleU γ then lo U else
    if U = saddleU γ then saddleS γ else hi U
  have hloe {U : ℝ} (hU : U < saddleU γ) : σ U = lo U := by simp [σ, hU]
  have hhie {U : ℝ} (hU : saddleU γ < U) : σ U = hi U := by
    simp [σ, not_lt.mpr hU.le, ne_of_gt hU]
  refine ⟨⟨σ, by simp [σ], fun U hU ↦ ?_, fun U hU ↦ ?_, fun U hU hne ↦ ?_⟩⟩
  · rw [hloe hU.2]
    exact ⟨(hlo U hU).1, (hlo U hU).2.1, (hlo U hU).2.2.1⟩
  · rw [hhie hU]
    exact ⟨(hhi U hU).1, (hhi U hU).2.1, (hhi U hU).2.2.1⟩
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · have heq : σ =ᶠ[𝓝 U] lo := by
        filter_upwards [Iio_mem_nhds hlt] with V hV
        exact hloe hV
      have hh := (hlo U ⟨hU, hlt⟩).2.2.2.congr_of_eventuallyEq heq
      simpa only [hloe hlt] using hh
    · have heq : σ =ᶠ[𝓝 U] hi := by
        filter_upwards [Ioi_mem_nhds hgt] with V hV
        exact hhie hV
      have hh := (hhi U hgt).2.2.2.congr_of_eventuallyEq heq
      simpa only [hhie hgt] using hh

namespace SubcriticalGraph

variable {γ : ℝ} (G : SubcriticalGraph γ)

theorem positive {U : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) (hU : 0 < U) : 0 < G.σ U := by
  rcases lt_trichotomy U (saddleU γ) with hlt | heq | hgt
  · have hh := (G.lower U ⟨hU, hlt⟩).1
    have hmul := mul_pos hγ hU
    linarith
  · rw [heq, G.saddle]
    exact saddleS_pos hγ hγ₁
  · exact (saddleS_pos hγ hγ₁).trans (G.upper U hgt).1

/-- A direct wedge estimate controls the graph at the joining point. -/
theorem saddle_lipschitz_bound {U : ℝ} (hγ₁ : γ < 1) (hU : 0 < U) :
    |G.σ U - saddleS γ| ≤ γ * |U - saddleU γ| := by
  have hA := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
  rcases lt_trichotomy U (saddleU γ) with hlt | heq | hgt
  · have hh := G.lower U ⟨hU, hlt⟩
    rw [abs_of_neg (by linarith [hh.2.1]), abs_of_neg (sub_neg.mpr hlt)]
    rw [hA]
    linarith [hh.1]
  · simp [heq, G.saddle]
  · have hh := G.upper U hgt
    rw [abs_of_pos (by linarith [hh.1]), abs_of_pos (sub_pos.mpr hgt)]
    rw [hA]
    linarith [hh.2.1]

theorem continuousAt_saddle (hγ₁ : γ < 1) : ContinuousAt G.σ (saddleU γ) := by
  have hB := saddleU_pos hγ₁
  have hbound : ∀ᶠ U in 𝓝 (saddleU γ), ‖G.σ U - saddleS γ‖ ≤ γ * ‖U - saddleU γ‖ := by
    filter_upwards [Ioi_mem_nhds hB] with U hU
    exact G.saddle_lipschitz_bound hγ₁ hU
  have hlim : Tendsto (fun U : ℝ ↦ U - saddleU γ) (𝓝 (saddleU γ)) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun U : ℝ ↦ U)
      (𝓝 (saddleU γ)) (𝓝 (saddleU γ))).sub_const (saddleU γ))
  have hd := squeeze_zero_norm' hbound (by simpa using hlim.norm.const_mul γ)
  have hs : Tendsto G.σ (𝓝 (saddleU γ)) (𝓝 (saddleS γ)) := by
    simpa only [sub_add_cancel, zero_add] using hd.add_const (saddleS γ)
  change Tendsto G.σ (𝓝 (saddleU γ)) (𝓝 (G.σ (saddleU γ)))
  rw [G.saddle]
  exact hs

theorem continuousOn (hγ₁ : γ < 1) : ContinuousOn G.σ (Ioi 0) := by
  intro U hU
  by_cases heq : U = saddleU γ
  · subst U
    exact (G.continuousAt_saddle hγ₁).continuousWithinAt
  · exact (G.derivative U hU heq).continuousAt.continuousWithinAt

theorem deriv_pos {U : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hU : 0 < U) (hne : U ≠ saddleU γ) : 0 < deriv G.σ U := by
  rw [(G.derivative U hU hne).deriv]
  have hs := G.positive hγ hγ₁ hU
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh := G.lower U ⟨hU, hlt⟩
    exact div_pos (mul_pos (by positivity) (by linarith [hh.1]))
      (mul_pos hU (by linarith [hh.2.2]))
  · have hh := G.upper U hgt
    exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by positivity) (by linarith [hh.2.1]))
      (mul_neg_of_pos_of_neg hU (by linarith [hh.2.2]))

theorem strictMonoOn (hγ : 0 < γ) (hγ₁ : γ < 1) : StrictMonoOn G.σ (Ioi 0) := by
  have hlo : StrictMonoOn G.σ (Ioo (0 : ℝ) (saddleU γ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      ((G.continuousOn hγ₁).mono fun _ ht ↦ ht.1)
    intro U hU
    rw [interior_Ioo] at hU
    exact G.deriv_pos hγ hγ₁ hU.1 (ne_of_lt hU.2)
  have hhi : StrictMonoOn G.σ (Ioi (saddleU γ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi _)
      ((G.continuousOn hγ₁).mono fun _ ht ↦ (saddleU_pos hγ₁).trans ht)
    intro U hU
    rw [interior_Ioi] at hU
    exact G.deriv_pos hγ hγ₁ ((saddleU_pos hγ₁).trans hU) (ne_of_gt hU)
  intro U hU V hV hUV
  rcases lt_trichotomy V (saddleU γ) with hVB | heqV | hBV
  · exact hlo ⟨hU, hUV.trans hVB⟩ ⟨hV, hVB⟩ hUV
  · subst V
    rw [G.saddle]
    exact (G.lower U ⟨hU, hUV⟩).2.1
  · rcases lt_trichotomy U (saddleU γ) with hUB | heqU | hBU
    · exact (G.lower U ⟨hU, hUB⟩).2.1.trans (G.upper V hBV).1
    · subst U
      rw [G.saddle]
      exact (G.upper V hBV).1
    · exact hhi hBU hBV hUV

/-- The initial-value crossing is a genuine point of the constructed graph.
The stronger lower bound `1+γ` follows from its global wedge. -/
theorem crossing (hγ : 0 < γ) (hγ₁ : γ < 1) :
    1 + γ < G.σ 1 ∧ G.σ 1 < saddleS γ ∧
      ∀ U > 0, G.σ U = G.σ 1 ↔ U = 1 := by
  have hB : 1 < saddleU γ := by
    unfold saddleU
    apply (lt_div_iff₀ (by linarith : 0 < 1 - γ)).mpr
    linarith
  have hh := G.lower 1 ⟨by norm_num, hB⟩
  refine ⟨by simpa using hh.1, hh.2.1, fun U hU ↦ ?_⟩
  exact ⟨fun heq ↦ (G.strictMonoOn hγ hγ₁).injOn hU (by norm_num) heq, fun heq ↦ congrArg G.σ heq⟩

end SubcriticalGraph
end
end krylov.LotkaVolterra
