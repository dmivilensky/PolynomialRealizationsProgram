import krylov.LotkaVolterra.EndpointClassification
import krylov.LotkaVolterra.ExitSide

/-!
Article: `main_krylov`, `apC:prop:g1`, finite graph-to-orbit time change.
Every actual normalized graph segment with nonnegative gap is traversed by
a genuine endpoint Lotka--Volterra trajectory in finite orbit time. A
bounded clipped scalar clock supplies existence and reaches the terminal
state because its speed is at least one. No inverse or global completeness
of the original quadratic system is assumed.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

/-- Traverse a finite actual endpoint graph segment by its physical orbit
clock. This includes the endpoint values and exact terminal state. -/
theorem endpoint_finite_graph_traversal {V : ℝ} (hV : 1 < V) {q : ℝ → ℝ}
    (hq : ∀ U ∈ Icc (1 : ℝ) V, 0 ≤ q U ∧
      HasDerivAt q (endpointRatioRate U (q U)) U) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = (1 + q 1, 1) ∧ ∃ T > 0,
      IsSolutionOn 1 α (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, α t ∈ positiveQuadrant ∧ 1 ≤ (α t).2) ∧
      α T = (V * (1 + q V), V) := by
  let f : ℝ → ℝ := fun U ↦ U * (U * q U + 1)
  let D : ℝ → ℝ := fun U ↦ U ^ 2 * endpointRatioRate U (q U) + 2 * U * q U + 1
  have hqC : ContinuousOn q (Icc (1 : ℝ) V) :=
    HasDerivAt.continuousOn fun U hU ↦ (hq U hU).2
  have hf (U : ℝ) (hU : U ∈ Icc (1 : ℝ) V) : HasDerivAt f (D U) U := by
    convert (hasDerivAt_id U).mul
      (((hasDerivAt_id U).mul (hq U hU).2).add_const 1) using 1
    · rfl
    · dsimp [D]
      ring
  have hden (U : ℝ) (hU : U ∈ Icc (1 : ℝ) V) : U * q U + 1 ≠ 0 := by
    nlinarith [(hq U hU).1, hU.1]
  have hrateC : ContinuousOn (fun U ↦ endpointRatioRate U (q U)) (Icc (1 : ℝ) V) := by
    unfold endpointRatioRate
    exact (((continuousOn_id.mul hqC).sub continuousOn_const).div
      ((continuousOn_id.mul hqC).add continuousOn_const) hden).mul
        ((continuousOn_const.add hqC).div continuousOn_id (fun U hU ↦ by linarith [hU.1]))
  have hDC : ContinuousOn D (Icc (1 : ℝ) V) := by dsimp [D]; fun_prop
  have hfC : ContinuousOn f (Icc (1 : ℝ) V) := HasDerivAt.continuousOn hf
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hDC.norm
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image hfC.norm
  have hfLip : LipschitzOnWith (Real.toNNReal K) f (Icc (1 : ℝ) V) := by
    apply (convex_Icc (1 : ℝ) V).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun U hU ↦ (hf U hU).hasDerivWithinAt)
    intro U hU
    have hh : ‖D U‖ ≤ (Real.toNNReal K : ℝ) :=
      (hK ⟨U, hU, rfl⟩).trans (Real.le_coe_toNNReal _)
    exact_mod_cast hh
  let c : ℝ → ℝ := fun U ↦ max 1 (min U V)
  have hcLip : LipschitzWith 1 c := (LipschitzWith.id.min_const V).const_max 1
  have hc (U : ℝ) : c U ∈ Icc (1 : ℝ) V :=
    ⟨le_max_left _ _, max_le hV.le (min_le_right _ _)⟩
  have hceq (U : ℝ) (hU : U ∈ Icc (1 : ℝ) V) : c U = U := by
    simp [c, min_eq_left hU.2, max_eq_right hU.1]
  let F : ℝ → ℝ := f ∘ c
  have hFLip : LipschitzWith (Real.toNNReal K) F := by
    apply LipschitzWith.of_dist_le_mul
    intro U W
    calc
      dist (F U) (F W) ≤ (Real.toNNReal K : ℝ) * dist (c U) (c W) :=
        hfLip.dist_le_mul _ (hc U) _ (hc W)
      _ ≤ (Real.toNNReal K : ℝ) * dist U W := by
        gcongr
        simpa using hcLip.dist_le_mul U W
  have hFbound (U : ℝ) : ‖F U‖ ≤ (Real.toNNReal L : ℝ) :=
    (hL ⟨c U, hc U, rfl⟩).trans (Real.le_coe_toNNReal _)
  have hFpos (U : ℝ) : 1 ≤ F U := by
    have hh := (hq (c U) (hc U)).1
    have hcc := (hc U).1
    dsimp [F, f]
    nlinarith [mul_nonneg (show 0 ≤ c U by linarith) hh]
  obtain ⟨U, hU₀, hdU⟩ := exists_global_solution_of_bounded_lipschitz
    (L := Real.toNNReal L) (K := Real.toNNReal K)
    (fun _ ↦ hFLip) (fun _ ↦ continuous_const) (fun _ U ↦ hFbound U) (1 : ℝ)
  have hUC : Continuous U := continuous_iff_continuousAt.mpr fun t ↦ (hdU t).continuousAt
  have hUm : StrictMono U := strictMono_of_deriv_pos
    (fun t ↦ by rw [(hdU t).deriv]; linarith [hFpos (U t)])
  have hUg (t : ℝ) (ht : 0 ≤ t) : 1 + t ≤ U t := by
    have hh := mul_sub_le_image_sub_of_le_deriv (fun t ↦ (hdU t).differentiableAt)
      (C := (1 : ℝ)) (fun t ↦ by rw [(hdU t).deriv]; exact hFpos (U t)) ht
    rw [hU₀] at hh
    linarith
  obtain ⟨T, hTmem, hUT⟩ := intermediate_value_Icc (sub_nonneg.mpr hV.le) hUC.continuousOn
    (show V ∈ Icc (U 0) (U (V - 1)) by rw [hU₀]; exact ⟨hV.le, by linarith [hUg (V - 1) (by linarith)]⟩)
  have hT : 0 < T := by
    by_contra! hn
    have hTzero : T = 0 := le_antisymm hn hTmem.1
    rw [hTzero, hU₀] at hUT
    linarith
  have hUr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : U t ∈ Icc (1 : ℝ) V := by
    have hlo := hUm.monotone ht.1
    have hhi := hUm.monotone ht.2
    rw [hU₀] at hlo
    rw [hUT] at hhi
    exact ⟨hlo, hhi⟩
  have hUder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt U (U t * (U t * q (U t) + 1)) t := by
    simpa only [F, Function.comp_apply, hceq _ (hUr t ht), f] using hdU t
  let α : ℝ → ℝ × ℝ := fun t ↦ (U t * (1 + q (U t)), U t)
  refine ⟨α, by simp [α, hU₀], T, hT, ?_, ?_, by simp [α, hUT]⟩
  · intro t ht
    have hh := (hUder t ht).mul ((hq (U t) (hUr t ht)).2.comp t (hUder t ht) |>.const_add 1)
    have hUt : 0 < U t := by linarith [(hUr t ht).1]
    have hd : U t * q (U t) + 1 ≠ 0 := hden _ (hUr t ht)
    have hSder : HasDerivAt (fun t ↦ U t * (1 + q (U t)))
        (2 * (U t * (1 + q (U t))) * (U t * q (U t) - 1)) t := by
      convert hh using 1
      · rfl
      · simp only [Function.comp_apply]
        unfold endpointRatioRate
        field_simp [ne_of_gt hUt, hd]
        ring
    convert hSder.prodMk (hUder t ht) using 1
    apply Prod.ext <;> dsimp [α, vectorField, sRate, uRate] <;> ring
  · intro t ht
    have hh := (hq (U t) (hUr t ht)).1
    have hUpos : 0 < U t := by linarith [(hUr t ht).1]
    exact ⟨⟨mul_pos hUpos (by linarith), hUpos⟩, (hUr t ht).1⟩

end
end krylov.LotkaVolterra
