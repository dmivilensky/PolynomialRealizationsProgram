import jacobi.Trichotomy.SubcriticalCoordinate

/-!
Article: jacobi, Proposition C.4.
The actual subcritical endpoint gap has leading coefficient
1/(c_alpha*(1-2*gamma)), with the original spectral c_alpha. Genuine
integrability and the exact derivative discharge all premises of the
community l'Hopital theorem on the original positive endpoint filter.
Use: subcritical_gap_limit applies the zero-over-zero derivative theorem to precisely the source gap integral.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology

/-- The genuine vanishing endpoint gap has the actual positive reciprocal-profile derivative at every subcritical physical interior point before the midpoint.
Use: subcritical_gap_limit applies the zero-over-zero derivative theorem to precisely the source gap integral.
Article: jacobi, Proposition C.4.
Proof: the full actual endpoint reciprocal integral is finite. Restrict it to the genuine smaller segment and apply the fundamental theorem of calculus at its positive upper endpoint. -/
theorem subcritical_gap_hasDerivAt {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ))
    {t : ℝ} (ht : t∈Ioo (0:ℝ) (1/2)) :
    HasDerivAt (packingGap a ha) (1/physicalProfile a ha t) t := by
  -- The integrable endpoint segment and positive interior continuity are independently proved for the original source profile.
  have hsub : uIcc (0:ℝ) t⊆uIcc (0:ℝ) (1/2) := by
    rw [uIcc_of_le ht.1.le,uIcc_of_le (by norm_num : (0:ℝ)≤1/2)]
    exact Icc_subset_Icc le_rfl ht.2.le
  have hm : AEStronglyMeasurable (fun t : ℝ => 1/physicalProfile a ha t) volume :=
    (measurable_const.div (physicalProfile_continuous a ha).measurable).aestronglyMeasurable
  exact intervalIntegral.integral_hasDerivAt_right
    ((subcritical_reciprocal_integrable ha hs).mono_set hsub) hm.stronglyMeasurableAtFilter
    ((physicalProfile_reciprocal_continuousOn a ha).continuousAt
      (isOpen_Ioo.mem_nhds ⟨ht.1,ht.2.trans (by norm_num)⟩))

/-- The actual original compact-end packing gap has exactly the source's printed leading power coefficient.
Use: the compact density tail obtains both its exact power and its original coefficient from the independently proved profile and this genuine gap asymptotic.
Article: jacobi, Proposition C.4.
Proof: the genuine gap and the positive power both vanish. Their actual derivative ratio is (t^(2*gamma)/phi_alpha(t))/(1-2*gamma), with its limit fixed by the positive original profile coefficient. All derivatives, nonzero denominators and zero limits are proved, so the community l'Hopital theorem applies. -/
theorem subcritical_gap_limit {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    Tendsto (fun t : ℝ => packingGap a ha t/t^(1-2*gamma a))
      (𝓝[>] (0:ℝ)) (𝓝 (1/(endpointConstant a ha*(1-2*gamma a)))) := by
  -- This limit integrates the proved original profile asymptotic using genuine derivatives and an actually vanishing primitive.
  have hp : 0<1-2*gamma a := by dsimp only [gamma]; linarith
  have hc := endpointConstant_pos a ha hs
  have hdf : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),HasDerivAt (packingGap a ha)
      (1/physicalProfile a ha t) t := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with t ht
    exact subcritical_gap_hasDerivAt ha hs ht
  have hdg : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),HasDerivAt (fun s : ℝ => s^(1-2*gamma a))
      ((1-2*gamma a)*t^(-2*gamma a)) t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    convert Real.hasDerivAt_rpow_const (x := t) (p := 1-2*gamma a) (Or.inl ht.ne') using 1
    congr 1
    ring
  have hgn : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),(1-2*gamma a)*t^(-2*gamma a)≠0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero hp.ne' (Real.rpow_pos_of_pos ht _).ne'
  have hgz : Tendsto (fun t : ℝ => t^(1-2*gamma a)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using
      (Real.continuousAt_rpow_const (0:ℝ) (1-2*gamma a) (Or.inr hp.le)).tendsto.mono_left nhdsWithin_le_nhds
  have hi := ((physicalProfile_subcritical_limit ha hs).inv₀ hc.ne').div_const (1-2*gamma a)
  have hdlim : Tendsto (fun t : ℝ => (1/physicalProfile a ha t)/((1-2*gamma a)*t^(-2*gamma a)))
      (𝓝[>] (0:ℝ)) (𝓝 (1/(endpointConstant a ha*(1-2*gamma a)))) := by
    have hv : (endpointConstant a ha)⁻¹/(1-2*gamma a)=1/(endpointConstant a ha*(1-2*gamma a)) := by
      rw [← one_div,div_div]
    rw [hv] at hi
    apply hi.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [show -2*gamma a= -(2*gamma a) by ring,Real.rpow_neg ht.le]
    simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
  exact HasDerivAt.lhopital_zero_nhdsGT hdf hdg hgn (subcritical_gap_zero ha hs) hgz hdlim

end
end jacobi.Trichotomy
