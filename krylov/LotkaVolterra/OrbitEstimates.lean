import krylov.LotkaVolterra.PositiveOrbits
import krylov.LotkaVolterra.Regions
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: `main_krylov`, `apC:prop:LV`, `apC:prop:g1`, and the endpoint
estimates following `apC:lem:fund`.

Regional monotonicity of actual solutions, stable-eigenvector wedge geometry,
and the exact gap/ratio equations at the endpoint parameter. Regional
monotonicity explicitly records the region hypothesis; it is not a claim
that the global separating orbit has already been constructed.

Source: the article's phase-plane inequalities and the standard derivative
criterion for monotonicity (`Mathlib.Analysis.Calculus.Deriv.MeanValue`).
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

theorem solution_s_hasDerivAt {γ t : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : HasDerivAt α (vectorField γ (α t)) t) :
    HasDerivAt (fun u ↦ (α u).1) (sRate γ (α t).1 (α t).2) t := by
  exact (hasFDerivAt_fst (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t hα

theorem solution_u_hasDerivAt {γ t : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : HasDerivAt α (vectorField γ (α t)) t) :
    HasDerivAt (fun u ↦ (α u).2) (uRate (α t).1 (α t).2) t := by
  exact (hasFDerivAt_snd (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t hα

/-- The state coordinate strictly increases on every interval of an actual
solution lying in the lower region. -/
theorem solution_lowerRegion_u_strictMono {γ l r : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn γ α (Ioo l r))
    (hreg : ∀ t ∈ Ioo l r, α t ∈ lowerRegion γ) :
    StrictMonoOn (fun t ↦ (α t).2) (Ioo l r) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo l r)
    (HasDerivAt.continuousOn (fun t ht ↦ solution_u_hasDerivAt (hα t ht)))
  intro t ht
  rw [interior_Ioo] at ht
  rw [(solution_u_hasDerivAt (hα t ht)).deriv]
  exact lowerRegion_uRate_pos (hreg t ht)

/-- The upper-region state coordinate strictly decreases away from the
saddle, as required to use it as a graph parameter. -/
theorem solution_upperRegion_u_strictAnti {γ l r : ℝ} {α : ℝ → ℝ × ℝ}
    (hγ : 0 < γ) (hγ₁ : γ < 1) (hα : IsSolutionOn γ α (Ioo l r))
    (hreg : ∀ t ∈ Ioo l r, α t ∈ upperRegion γ)
    (hne : ∀ t ∈ Ioo l r, α t ≠ saddlePoint γ) :
    StrictAntiOn (fun t ↦ (α t).2) (Ioo l r) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo l r)
    (HasDerivAt.continuousOn (fun t ht ↦ solution_u_hasDerivAt (hα t ht)))
  intro t ht
  rw [interior_Ioo] at ht
  rw [(solution_u_hasDerivAt (hα t ht)).deriv]
  exact upperRegion_uRate_neg hγ hγ₁ (hreg t ht) (hne t ht)

theorem solution_endpointRegion_strictMono {l r : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn 1 α (Ioo l r))
    (hreg : ∀ t ∈ Ioo l r, α t ∈ endpointRegion) :
    StrictMonoOn (fun t ↦ (α t).1) (Ioo l r) ∧
    StrictMonoOn (fun t ↦ (α t).2) (Ioo l r) := by
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Ioo l r)
      (HasDerivAt.continuousOn (fun t ht ↦ solution_s_hasDerivAt (hα t ht)))
    intro t ht
    rw [interior_Ioo] at ht
    rw [(solution_s_hasDerivAt (hα t ht)).deriv]
    exact (endpointRegion_rates_pos (hreg t ht)).1
  · apply strictMonoOn_of_deriv_pos (convex_Ioo l r)
      (HasDerivAt.continuousOn (fun t ht ↦ solution_u_hasDerivAt (hα t ht)))
    intro t ht
    rw [interior_Ioo] at ht
    rw [(solution_u_hasDerivAt (hα t ht)).deriv]
    exact (endpointRegion_rates_pos (hreg t ht)).2

/-- The stable eigenvector points strictly into the upper wedge at the
saddle; this holds on its entire positive ray. -/
theorem stable_ray_mem_upperRegion {γ a : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (ha : 0 ≤ a) :
    saddlePoint γ + a • saddleEigenvector γ (stableEigenvalue γ) ∈ upperRegion γ := by
  have hs := saddleS_pos hγ hγ₁
  have hη := stableEigenvalue_neg hγ hγ₁
  have he := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
  change saddleS γ ≤ saddleS γ + a * (2 * γ * saddleS γ) ∧
    (saddleS γ + a * (2 * γ * saddleS γ) - 1) / γ ≤
      saddleU γ + a * (2 * saddleS γ - stableEigenvalue γ)
  constructor
  · have h : 0 ≤ a * (2 * γ * saddleS γ) := by positivity
    linarith
  · apply (div_le_iff₀ hγ).mpr
    have h : 0 ≤ a * (γ * (-stableEigenvalue γ)) :=
      mul_nonneg ha (mul_nonneg hγ.le (neg_nonneg.mpr hη.le))
    nlinarith

/-- The opposite stable ray lies in the lower wedge whenever it still has
positive coordinates. -/
theorem negative_stable_ray_mem_lowerRegion {γ a : ℝ} (hγ : 0 < γ)
    (hγ₁ : γ < 1) (ha : 0 < a)
    (hpos : saddlePoint γ - a • saddleEigenvector γ (stableEigenvalue γ) ∈
      positiveQuadrant) :
    saddlePoint γ - a • saddleEigenvector γ (stableEigenvalue γ) ∈ lowerRegion γ := by
  have hs := saddleS_pos hγ hγ₁
  have hη := stableEigenvalue_neg hγ hγ₁
  have hU := saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)
  refine ⟨hpos.1, ?_, hpos.2, ?_⟩
  · change saddleS γ - a * (2 * γ * saddleS γ) < saddleS γ
    have h : 0 < a * (2 * γ * saddleS γ) := by positivity
    linarith
  · change saddleU γ - a * (2 * saddleS γ - stableEigenvalue γ) <
      saddleS γ - a * (2 * γ * saddleS γ) + 1
    have h : 0 < a * (2 * (1 - γ) * saddleS γ - stableEigenvalue γ) := by
      apply mul_pos ha
      have hn : 0 ≤ 2 * (1 - γ) * saddleS γ := by positivity
      linarith
    nlinarith

/-- Actual derivative of the endpoint gap variable, with no graph or
separating-orbit assumption. -/
theorem endpoint_gap_hasDerivAt {t : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : HasDerivAt α (vectorField 1 (α t)) t) :
    HasDerivAt (fun u ↦ (α u).1 - (α u).2)
      ((α t).2 * (((α t).1 - (α t).2) - 3) +
        2 * ((α t).1 - (α t).2) * (((α t).1 - (α t).2) - 1)) t := by
  rw [← endpoint_gap_rate]
  exact (solution_s_hasDerivAt hα).sub (solution_u_hasDerivAt hα)

/-- Once `e ≥ 3`, the endpoint gap grows at least at speed twelve. -/
theorem endpoint_gap_rate_ge_twelve {s U : ℝ} (hU : 0 ≤ U) (he : 3 ≤ s - U) :
    12 ≤ sRate 1 s U - uRate s U := by
  rw [endpoint_gap_rate]
  have h₁ : 0 ≤ U * ((s - U) - 3) := mul_nonneg hU (by linarith)
  have h₂ : 0 ≤ ((s - U) - 3) ^ 2 := sq_nonneg _
  nlinarith

/-- Endpoint ratio equation in the original orbit time. Dividing this by
`U' = U(e+1)` gives the differential inequality used in the article. -/
theorem endpoint_ratio_hasDerivAt {t : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : HasDerivAt α (vectorField 1 (α t)) t) (hU : (α t).2 ≠ 0) :
    HasDerivAt (fun u ↦ ((α u).1 - (α u).2) / (α u).2)
      ((((α t).1 - (α t).2) - 3) *
        (1 + ((α t).1 - (α t).2) / (α t).2)) t := by
  convert (endpoint_gap_hasDerivAt hα).div (solution_u_hasDerivAt hα) hU using 1
  unfold uRate
  field_simp
  ring

/-- The universal endpoint feedback ratio is between zero and one half as
soon as the separating gap bounds `1 < e < 3` have been established. -/
theorem endpoint_feedback_ratio_bounds {e : ℝ} (he₁ : 1 < e) (he₃ : e < 3) :
    0 < (e - 1) / (e + 1) ∧ (e - 1) / (e + 1) < 1 / 2 := by
  have hd : 0 < e + 1 := by linarith
  constructor
  · exact div_pos (by linarith) hd
  · apply (div_lt_iff₀ hd).mpr
    linarith

end
end krylov.LotkaVolterra
