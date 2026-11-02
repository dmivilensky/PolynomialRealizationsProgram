import krylov.LotkaVolterra.GlobalEndpointShooting
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: `main_krylov`, `apC:prop:g1`, and its strict endpoint gap estimates.

The compact shooting solution is upgraded to strict physical inequalities.
The resulting graph is constructed, not assumed: its gap lies in `(1,3)`
for every `U ≥ 1`, and its tangent is exactly the endpoint LV vector field
divided by the positive `U` component. Real analyticity is not claimed here;
it requires an additional analytic ODE regularity theorem.

Source: the one-sided derivative test at a barrier and the scalar shooting
construction in `GlobalEndpointShooting`.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

/-- A differentiable function lying above its present value immediately
to the right cannot have a negative derivative. -/
theorem derivative_nonneg_of_right_lower_bound {e : ℝ → ℝ} {U v : ℝ}
    (hd : HasDerivAt e v U) (hbound : ∀ V > U, e U ≤ e V) : 0 ≤ v := by
  apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  filter_upwards [self_mem_nhdsWithin] with V hV
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr (hbound V hV)) (sub_pos.mpr hV).le

/-- The corresponding right-sided upper-barrier test. -/
theorem derivative_nonpos_of_right_upper_bound {e : ℝ → ℝ} {U v : ℝ}
    (hd : HasDerivAt e v U) (hbound : ∀ V > U, e V ≤ e U) : v ≤ 0 := by
  apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  filter_upwards [self_mem_nhdsWithin] with V hV
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hbound V hV)) (sub_pos.mpr hV).le

/-- Any actual global graph staying in the closed shooting strip stays
strictly inside it: both boundaries point outward in increasing `U`. -/
theorem endpoint_graph_gap_strict {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧
      HasDerivAt e (endpointGraphRate U (e U)) U)
    {U : ℝ} (hU : 1 ≤ U) : e U ∈ Ioo (1 : ℝ) 3 := by
  have h := he U hU
  constructor
  · by_contra! hle
    have heq : e U = 1 := le_antisymm hle h.1.1
    have hd := derivative_nonneg_of_right_lower_bound h.2
      (fun V hV ↦ by rw [heq]; exact (he V (hU.trans hV.le)).1.1)
    rw [heq] at hd
    norm_num [endpointGraphRate] at hd
  · by_contra! hle
    have heq : e U = 3 := le_antisymm h.1.2 hle
    have hd := derivative_nonpos_of_right_upper_bound h.2
      (fun V hV ↦ by rw [heq]; exact (he V (hU.trans hV.le)).1.2)
    rw [heq] at hd
    norm_num [endpointGraphRate] at hd
    exact (not_le_of_gt (div_pos (by norm_num) (by linarith : 0 < U))) hd

/-- Genuine endpoint graph existence, with the stronger strict gap bound
used later in the continuum optimizer proof. -/
theorem exists_strict_endpoint_graph :
    ∃ σ : ℝ → ℝ, ∀ U ≥ 1,
      U + 1 < σ U ∧ σ U < U + 3 ∧ σ U ≤ 4 * U ∧
      HasDerivAt σ (2 * σ U * (σ U - 1 - U) / (U * (σ U + 1 - U))) U := by
  obtain ⟨e, he⟩ := exists_global_endpoint_graph_gap
  refine ⟨fun U ↦ U + e U, fun U hU ↦ ?_⟩
  have hs := endpoint_graph_gap_strict he hU
  refine ⟨by linarith [hs.1], by linarith [hs.2], by linarith [hs.2], ?_⟩
  have hU₀ : U ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hU)
  have he₀ : e U + 1 ≠ 0 := by linarith [hs.1]
  have hrate : 2 * (U + e U) * (U + e U - 1 - U) /
      (U * (U + e U + 1 - U)) = 1 + endpointGraphRate U (e U) := by
    rw [endpointGraphRate_eq hU₀ he₀]
    have hid : U + e U + 1 - U = e U + 1 := by ring
    rw [hid]
    field_simp
    ring
  rw [hrate]
  exact (hasDerivAt_id U).add (he U hU).2

end
end krylov.LotkaVolterra
