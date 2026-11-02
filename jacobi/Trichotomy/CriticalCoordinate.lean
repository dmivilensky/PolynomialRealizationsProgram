import jacobi.Trichotomy.PhysicalEndpointLimits
import jacobi.Trichotomy.PackingCoordinate
import jacobi.Trichotomy.InfinitePacking
import jacobi.Analysis.IteratedLogPrimitive

/-!
Article: jacobi, Proposition C.4.
The actual critical coordinate has its exact iterated-logarithmic
coefficient -1/2 and an infinite left endpoint. Hence the genuine
critical packed density is positive on the whole real line.
Use: critical_coordinate_atBot and the doubly exponential density tail concern the actual source coordinate, with its prescribed factor two retained.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The genuine critical intrinsic coordinate has exactly its printed iterated-logarithmic coefficient.
Use: critical_coordinate_atBot and the doubly exponential density tail concern the actual source coordinate, with its prescribed factor two retained.
Article: jacobi, Proposition C.4.
Proof: invert the proved actual critical profile quotient to get (t*log(1/t))*x'(t) tending to 1/2. Apply the iterated-logarithmic primitive theorem to the genuine derivative. -/
theorem critical_coordinate_limit (ha : -1 < -(1/2:ℝ)) :
    Tendsto (fun t : ℝ => packingCoordinate (-(1/2)) ha t/log (log (1/t)))
      (𝓝[>] (0:ℝ)) (𝓝 (-(1/2:ℝ))) := by
  -- The original profile limit fixes the genuine reciprocal coefficient before integrating the derivative.
  have hd : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),
      HasDerivAt (packingCoordinate (-(1/2)) ha) (1/physicalProfile (-(1/2)) ha t) t := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    exact packingCoordinate_hasDerivAt (-(1/2)) ha ht
  apply jacobi.Analysis.iterated_logarithmic_endpoint_limit hd
  have h := (physicalProfile_critical_limit ha).inv₀ (by norm_num)
  norm_num at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun t => by simp [div_eq_mul_inv,mul_comm])

/-- The genuine critical logarithmic scale tends to positive infinity on the original positive endpoint filter.
Use: critical_coordinate_atBot deduces the actual infinite support endpoint from its proved negative leading ratio.
Article: jacobi, Proposition C.4.
Proof: log(t) tends to minus infinity; negate it and apply the ordinary logarithm-at-infinity limit. -/
theorem critical_scale_atTop :
    Tendsto (fun t : ℝ => log (log (1/t))) (𝓝[>] (0:ℝ)) atTop := by
  simpa only [Function.comp_def,one_div,Real.log_inv] using
    tendsto_log_atTop.comp (tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero)

/-- The actual critical packing coordinate has an infinite left endpoint.
Use: critical_packingImage obtains full source support without an additional improper-integrability premise.
Article: jacobi, Proposition C.4.
Proof: multiply the actual negative limiting ratio -1/2 by the true iterated logarithmic scale tending to positive infinity. -/
theorem critical_coordinate_atBot (ha : -1 < -(1/2:ℝ)) :
    Tendsto (packingCoordinate (-(1/2)) ha) (𝓝[>] (0:ℝ)) atBot := by
  have h := (critical_coordinate_limit ha).neg_mul_atTop (by norm_num) critical_scale_atTop
  apply h.congr'
  filter_upwards [critical_scale_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t ht
  exact div_mul_cancel₀ _ ht.ne'

/-- The actual critical packing image is the whole real line.
Use: the genuine critical density and its double-exponential tails have the full support asserted in the source.
Article: jacobi, Proposition C.4.
Proof: its proved infinite left coordinate endpoint and original reflection fill the whole true interval image. -/
theorem critical_packingImage (ha : -1 < -(1/2:ℝ)) :
    packingImage (-(1/2)) ha=univ :=
  packingImage_eq_univ_of_atBot (-(1/2)) ha (critical_coordinate_atBot ha)

end
end jacobi.Trichotomy
