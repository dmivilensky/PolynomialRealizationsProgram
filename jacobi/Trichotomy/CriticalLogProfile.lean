import jacobi.Trichotomy.CriticalCoordinate
import jacobi.Analysis.LogarithmicRatios

/-!
Article: jacobi, Proposition C.4.
The original logarithmic endpoint asymptotic determines its ordinary
power exponent and the exact leading logarithm of the reciprocal
squared profile. These are the genuine density logarithms used in the
printed doubly exponential packing tail.
Use: critical_profile_log_limit and critical_log_density_limit compare the actual profile logarithms with the same source scale log(1/t).
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The genuine positive critical logarithmic scale diverges on the original endpoint filter.
Use: critical_profile_log_limit and critical_log_density_limit compare the actual profile logarithms with the same source scale log(1/t).
Article: jacobi, Proposition C.4.
Proof: negate the genuine logarithm-at-zero limit and use log(1/t)=-log(t). -/
theorem critical_linear_log_scale_atTop :
    Tendsto (fun t : ℝ => log (1/t)) (𝓝[>] (0:ℝ)) atTop := by
  simpa only [Function.comp_def,one_div,Real.log_inv] using
    tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero

/-- The actual critical profile has logarithmic endpoint exponent one despite its extra logarithmic factor.
Use: critical_log_density_limit derives the original squared-density reciprocal logarithm with its exact coefficient two.
Article: jacobi, Proposition C.4.
Proof: take the logarithm of the genuine normalized profile ratio, whose finite limit is log(two). The extra log(log(1/t))/log(t) vanishes by the community log(x)=o(x) theorem. Expand only on the actual positive physical endpoint filter. -/
theorem critical_profile_log_limit (ha : -1 < -(1/2:ℝ)) :
    Tendsto (fun t : ℝ => log (physicalProfile (-(1/2)) ha t)/log t)
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  -- Both the normalized original profile and the logarithmic scale are genuinely positive near zero.
  have hr := ((Real.continuousAt_log (by norm_num : (2:ℝ)≠0)).tendsto.comp
    (physicalProfile_critical_limit ha)).div_atBot tendsto_log_nhdsGT_zero
  have hs := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp critical_linear_log_scale_atTop
  have h := (hr.add_const 1).add hs.neg
  norm_num only [zero_add,neg_zero,add_zero] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
  have hp := physicalProfile_pos (-(1/2)) ha ht
  have hL : 0<log (1/t) := by rw [one_div,Real.log_inv]; exact neg_pos.mpr (Real.log_neg ht.1 ht.2)
  have hlog := (Real.log_neg ht.1 ht.2).ne
  dsimp only [Function.comp_def,id_eq]
  rw [Real.log_div hp.ne' (mul_pos ht.1 hL).ne',Real.log_mul ht.1.ne' hL.ne']
  simp only [one_div,Real.log_inv]
  field_simp [hlog]
  ring

/-- The actual critical reciprocal squared profile has the exact leading logarithm two in the original physical endpoint coordinate.
Use: critical_density_coordinate_tail takes one more logarithm against the actual divergent scale, giving the source doubly exponential tail.
Article: jacobi, Proposition C.4.
Proof: the genuine critical profile logarithmic exponent is one. The exact real logarithm identities give the same ratio multiplied by two. -/
theorem critical_log_density_limit (ha : -1 < -(1/2:ℝ)) :
    Tendsto (fun t : ℝ => log (1/(physicalProfile (-(1/2)) ha t)^2)/log (1/t))
      (𝓝[>] (0:ℝ)) (𝓝 2) := by
  -- The exact logarithm identities preserve the original density coefficient two at every positive physical point.
  have h := (critical_profile_log_limit ha).const_mul 2
  norm_num only [mul_one] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  simp only [one_div,Real.log_inv,Real.log_pow]
  ring

end
end jacobi.Trichotomy
