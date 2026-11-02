import jacobi.Trichotomy.CriticalLogProfile
import jacobi.Trichotomy.SupercriticalTail

/-!
Article: jacobi, Proposition C.4.
The genuine original critical density has the exact doubly exponential
logarithmic rate two at both ends of the real line. The actual inverse
intrinsic coordinate transfers the true physical endpoint asymptotic,
and the independently proved density evenness gives both spatial ends.
Use: critical_density_tail_atBot transfers this actual source endpoint asymptotic to ordinary spatial minus infinity using the genuine inverse coordinate.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual critical squared original profile has exactly the printed iterated-logarithmic density tail in its original intrinsic coordinate.
Use: critical_density_tail_atBot transfers this actual source endpoint asymptotic to ordinary spatial minus infinity using the genuine inverse coordinate.
Article: jacobi, Proposition C.4.
Proof: the genuine reciprocal-density logarithm has ratio two to log(1/t), so the common logarithmic-ratio theorem gives its second logarithm coefficient one. Divide by the negative of the actual coordinate ratio, whose limit is one half, and use the true coordinate's eventual negative sign. -/
theorem critical_density_coordinate_tail (ha : -1 < -(1/2:ℝ)) :
    Tendsto (fun t : ℝ => log (log (1/(physicalProfile (-(1/2)) ha t)^2))/
      |packingCoordinate (-(1/2)) ha t|) (𝓝[>] (0:ℝ)) (𝓝 2) := by
  -- The extra logarithm is justified by the positive genuine relative limit against the same divergent original scale.
  have hlog := jacobi.Analysis.logarithmic_ratio_limit (by norm_num : (0:ℝ)<2)
    critical_linear_log_scale_atTop (critical_log_density_limit ha)
  have h := hlog.div (critical_coordinate_limit ha).neg (by norm_num)
  norm_num only [neg_neg,one_div_div,mul_one,div_one] at h
  apply h.congr'
  filter_upwards [(critical_coordinate_atBot ha).eventually (eventually_lt_atBot (0:ℝ)),
    critical_scale_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t hx ht
  dsimp only [Pi.div_apply,Pi.neg_apply]
  rw [abs_of_neg hx]
  field_simp [hx.ne,ht.ne']

/-- The actual full-support critical packed density has the source's exact doubly exponential rate at ordinary spatial minus infinity.
Use: critical_density_tail combines this actual left-tail limit with proved evenness to obtain the same rate at both spatial ends.
Article: jacobi, Proposition C.4.
Proof: the genuine critical inverse tends to the positive physical endpoint and exactly inverts the original coordinate. Substitute its true squared-profile density identity into the proved coordinate tail. -/
theorem critical_density_tail_atBot (ha : -1 < -(1/2:ℝ)) :
    Tendsto (fun x : ℝ => log (log (1/packedDensity (-(1/2)) ha x))/|x|) atBot (𝓝 2) := by
  have hfull := critical_packingImage ha
  have h := (critical_density_coordinate_tail ha).comp (packingInverse_atBot (-(1/2)) ha hfull)
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro x
  have hx : x∈packingImage (-(1/2)) ha := by rw [hfull]; trivial
  dsimp only [Function.comp_def]
  rw [packingCoordinate_inverse (-(1/2)) ha hx,← packedDensity_on_image (-(1/2)) ha hx]

/-- The original critical packed density has exactly the printed doubly exponential logarithmic rate at both spatial ends.
Use: completes the critical support-and-tail branch of Proposition C.4 for the genuinely constructed original density.
Article: jacobi, Proposition C.4.
Proof: reflect the proved actual left-tail limit using the original density evenness, then compose the positive-end limit with absolute value tending to infinity outside compact real sets. -/
theorem critical_density_tail (ha : -1 < -(1/2:ℝ)) :
    Tendsto (fun x : ℝ => log (log (1/packedDensity (-(1/2)) ha x))/|x|)
      (cocompact ℝ) (𝓝 2) := by
  have hpos := (critical_density_tail_atBot ha).comp tendsto_neg_atTop_atBot
  simp only [Function.comp_def,packedDensity_even,abs_neg] at hpos
  have h := hpos.comp (tendsto_norm_cocompact_atTop (E := ℝ))
  simpa only [Function.comp_def,Real.norm_eq_abs,abs_abs,packedDensity_abs] using h

end
end jacobi.Trichotomy
