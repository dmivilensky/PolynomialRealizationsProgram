import jacobi.Trichotomy.SupercriticalEndpoint
import jacobi.Trichotomy.SubcriticalEndpoint
import jacobi.Trichotomy.CriticalEndpoint
import jacobi.Trichotomy.PhysicalProfile

/-!
Article: jacobi, Proposition C.4.
The three already proved original physical half-interval asymptotics
hold for the real representative used in the intrinsic packing integral.
The clamping map transfers only a genuine positive neighborhood of zero,
where it is exactly the original coordinate.
Use: the genuine three profile asymptotics can be differentiated and integrated in the ordinary real packing coordinate without a change of endpoint filter.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- An actual half-interval endpoint limit is the same right-hand real-coordinate limit.
Use: the genuine three profile asymptotics can be differentiated and integrated in the ordinary real packing coordinate without a change of endpoint filter.
Article: jacobi, Proposition C.4.
Proof: compose with the continuous physical half-interval projection, which maps sufficiently small positive reals to the same positive physical point. -/
theorem real_endpoint_of_half {f : ℝ → ℝ} {L : ℝ}
    (h : Tendsto (fun t : HalfInterval => f (t:ℝ)) (𝓝[>] halfZero) (𝓝 L)) :
    Tendsto f (𝓝[>] (0:ℝ)) (𝓝 L) := by
  -- Only the interval 0<t<1/2 is used, so the projection never changes the original endpoint coordinate.
  have hc : Tendsto halfParameterClamp (𝓝[>] (0:ℝ)) (𝓝[>] halfZero) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [halfParameterClamp,ContinuousMap.coe_mk,Set.projIcc_left,halfZero] using
        (halfParameterClamp.continuous.tendsto (0:ℝ)).mono_left
          (show 𝓝[>] (0:ℝ)≤𝓝 (0:ℝ) from nhdsWithin_le_nhds)
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with t ht
      change (0:ℝ)<(Set.projIcc 0 (1/2) (by norm_num) t:ℝ)
      rw [Set.projIcc_of_mem (by norm_num) ⟨ht.1.le,ht.2.le⟩]
      exact ht.1
  apply (h.comp hc).congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with t ht
  dsimp only [Function.comp_def,halfParameterClamp,ContinuousMap.coe_mk]
  rw [Set.projIcc_of_mem (by norm_num) ⟨ht.1.le,ht.2.le⟩]

/-- The genuine real-coordinate profile has the printed supercritical linear endpoint constant.
Use: supercritical_coordinate_limit integrates the actual reciprocal-profile derivative, fixing both the true infinite support and exponential tail rate.
Article: jacobi, Proposition C.4.
Proof: restrict the canonical real profile to the actual half interval, where it is the original profile, and transfer its already proved endpoint limit. -/
theorem physicalProfile_supercritical_limit {a : ℝ} (ha : -1<a) (hs : -(1/2:ℝ)<a) :
    Tendsto (fun t : ℝ => physicalProfile a ha t/t) (𝓝[>] (0:ℝ)) (𝓝 (1/(a/2+1/4))) := by
  apply real_endpoint_of_half
  have h := supercritical_profile_limit ha hs
  convert h using 1
  ext t
  rw [physicalProfile_eq a ha ⟨t.property.1,t.property.2.trans (by norm_num)⟩]
  rfl

/-- The genuine real-coordinate profile has the printed positive subcritical power coefficient.
Use: the compact-end intrinsic primitive and final compact density power law use exactly this original endpointConstant.
Article: jacobi, Proposition C.4.
Proof: the real physical profile agrees with the original on the full physical half interval, whose original spectral endpoint asymptotic is already proved. -/
theorem physicalProfile_subcritical_limit {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    Tendsto (fun t : ℝ => physicalProfile a ha t/t^(2*gamma a))
      (𝓝[>] (0:ℝ)) (𝓝 (endpointConstant a ha)) := by
  apply real_endpoint_of_half
  have h := endpoint_profile_limit a ha hs
  convert h using 1
  ext t
  rw [physicalProfile_eq a ha ⟨t.property.1,t.property.2.trans (by norm_num)⟩]
  rfl

/-- The genuine real-coordinate critical profile has its original logarithmic coefficient two.
Use: the critical packing-coordinate asymptotic and doubly exponential density tail start from this exact source normalization.
Article: jacobi, Proposition C.4.
Proof: transfer the independently proved original critical half-interval limit through the same genuine physical real representative. -/
theorem physicalProfile_critical_limit (ha : -1 < -(1/2:ℝ)) :
    Tendsto (fun t : ℝ => physicalProfile (-(1/2)) ha t/(t*log (1/t)))
      (𝓝[>] (0:ℝ)) (𝓝 2) := by
  apply real_endpoint_of_half
  have h := critical_profile_limit ha
  convert h using 1
  ext t
  rw [physicalProfile_eq (-(1/2)) ha ⟨t.property.1,t.property.2.trans (by norm_num)⟩]
  rfl

end
end jacobi.Trichotomy
