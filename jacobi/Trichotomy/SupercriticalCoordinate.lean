import jacobi.Trichotomy.PhysicalEndpointLimits
import jacobi.Trichotomy.PackingCoordinate

/-!
Article: jacobi, Proposition C.4.
The genuine reciprocal-profile derivative integrates to precisely
nu*log(t), forcing the actual left coordinate endpoint to minus infinity.
This proof uses the same original coordinate for every alpha>-1/2.
Use: supercritical_coordinate_atBot gives full support, and the density logarithm divided by this same coordinate gives its true exponential rate.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual original supercritical intrinsic packing coordinate has exactly its printed logarithmic leading coefficient.
Use: supercritical_coordinate_atBot gives full support, and the density logarithm divided by this same coordinate gives its true exponential rate.
Article: jacobi, Proposition C.4.
Proof: the genuine coordinate derivative is 1/phi_alpha and the proved profile ratio tends to 1/nu. Thus t*x_alpha'(t) tends to nu. Apply the proved logarithmic-primitive theorem to the actual coordinate. -/
theorem supercritical_coordinate_limit {a : ℝ} (ha : -1<a) (hs : -(1/2:ℝ)<a) :
    Tendsto (fun t : ℝ => packingCoordinate a ha t/log t)
      (𝓝[>] (0:ℝ)) (𝓝 (a/2+1/4)) := by
  -- No independent coordinate asymptotic is assumed: its derivative is the original positive reciprocal profile.
  have hd : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),
      HasDerivAt (packingCoordinate a ha) (1/physicalProfile a ha t) t := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    exact packingCoordinate_hasDerivAt a ha ht
  have hnu : 0<a/2+1/4 := by linarith
  have hl := (physicalProfile_supercritical_limit ha hs).inv₀ (one_div_ne_zero hnu.ne')
  rw [one_div,inv_inv] at hl
  apply jacobi.Analysis.logarithmic_endpoint_limit hd
  apply hl.congr'
  exact Filter.Eventually.of_forall (fun t => by simp [div_eq_mul_inv,mul_comm])

/-- The genuine supercritical intrinsic packing coordinate has an infinite left endpoint.
Use: the true packing image is the whole real line, and the left-tail density limit is transferred through its actual continuous inverse.
Article: jacobi, Proposition C.4.
Proof: its actual ratio to log(t) tends to the positive number nu. Multiplying by log(t), which tends to minus infinity, gives the genuine divergent endpoint. -/
theorem supercritical_coordinate_atBot {a : ℝ} (ha : -1<a) (hs : -(1/2:ℝ)<a) :
    Tendsto (packingCoordinate a ha) (𝓝[>] (0:ℝ)) atBot := by
  have h := (supercritical_coordinate_limit ha hs).pos_mul_atBot
    (show 0<a/2+1/4 by linarith) tendsto_log_nhdsGT_zero
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
  exact div_mul_cancel₀ _ (Real.log_ne_zero_of_pos_of_ne_one ht.1 ht.2.ne)

end
end jacobi.Trichotomy
