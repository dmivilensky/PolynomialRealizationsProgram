import jacobi.Trichotomy.YoungTail
import Mathlib.Topology.Bornology.BoundedOperation

/-!
Article: jacobi, Proposition C.4.
Source: translation preserves escape from compact subsets of the real line.
Use: young_translated_tail expresses every translated equality profile's decay in the source's original coordinate |x|.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Filter jacobi.Young
open scoped Topology

/-- A fixed translation changes the absolute spatial coordinate by an asymptotically negligible relative amount at both ends.
Use: young_translated_tail expresses every translated equality profile's decay in the source's original coordinate |x|.
Article: jacobi, Proposition C.4.
Proof: reciprocal |x| tends to zero outside compact sets, hence 1-c/x tends to one. Take its absolute value and cancel x only eventually away from zero. -/
theorem shifted_abs_ratio (c : ℝ) :
    Tendsto (fun x : ℝ => |x-c|/|x|) (cocompact ℝ) (𝓝 1) := by
  -- Both positive and negative spatial ends are retained by the actual cocompact filter.
  have hx : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop :=
    tendsto_norm_cocompact_atTop (E := ℝ)
  have hi : Tendsto (fun x : ℝ => x⁻¹) (cocompact ℝ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_inv,Real.norm_eq_abs,Function.comp_def] using tendsto_inv_atTop_zero.comp hx
  have h := ((tendsto_const_nhds (x := (1:ℝ))).sub (hi.const_mul c)).abs
  simp only [mul_zero,sub_zero,abs_one] at h
  apply h.congr'
  filter_upwards [hx.eventually (eventually_gt_atTop (0:ℝ))] with x hx0
  have hn : x≠0 := abs_pos.mp hx0
  rw [show 1-c*x⁻¹=(x-c)/x by field_simp,abs_div]

/-- Every positive translated Young equality profile has exactly the source's two-ended logarithmic tail exponent minus four.
Use: the complete Young minimizer classification, which permits arbitrary translates, has the actual comparison tail asserted in Proposition C.4.
Article: jacobi, Proposition C.4.
Proof: translate the centered tail along the actual cocompact filter and multiply by |x-c|/|x|, whose proved limit is one. The exact quotient cancellation is used only eventually away from the translated center. -/
theorem young_translated_tail {b : ℝ} (hb : 0<b) (c : ℝ) :
    Tendsto (fun x : ℝ => log (b*sech (x-c)^4)/|x|) (cocompact ℝ) (𝓝 (-4)) := by
  -- Translation preserves escape from every compact set, so the centered theorem applies at both actual spatial ends.
  have hs : Tendsto (fun x : ℝ => x-c) (cocompact ℝ) (cocompact ℝ) := by
    simpa only [Metric.cobounded_eq_cocompact] using tendsto_sub_const_cobounded c
  have h := ((young_tail hb).comp hs).mul (shifted_abs_ratio c)
  simp only [mul_one] at h
  have hx : Tendsto (fun x : ℝ => |x-c|) (cocompact ℝ) atTop :=
    by simpa only [Function.comp_def,Real.norm_eq_abs] using (tendsto_norm_cocompact_atTop (E := ℝ)).comp hs
  apply h.congr'
  filter_upwards [hx.eventually (eventually_gt_atTop (0:ℝ))] with x hx0
  dsimp only [Function.comp_def]
  field_simp [hx0.ne']

end
end jacobi.Trichotomy
