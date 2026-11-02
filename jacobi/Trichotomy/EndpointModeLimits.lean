import jacobi.Trichotomy.EndpointWaves
import jacobi.Reference.EnergyGreenEndpoint

/-!
Article: jacobi, Proposition C.4.
Above the critical order, each selected wave square divided by t
vanishes at zero. The transformed and reference waves have their
independently proved original selected-branch normalization.
Use: selected_wave_square_limit and the final supercritical theorem compose the original real reference asymptotics with the actual physical coordinate.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The physical half-interval right endpoint filter maps to the genuine positive real endpoint filter.
Use: selected_wave_square_limit and the final supercritical theorem compose the original real reference asymptotics with the actual physical coordinate.
Article: jacobi, Proposition C.4.
Proof: the subtype inclusion is continuous and every point in the punctured right half-interval neighborhood is strictly positive. -/
theorem half_endpoint_tendsto :
    Tendsto (fun t : HalfInterval => (t:ℝ)) (𝓝[>] halfZero) (𝓝[>] (0:ℝ)) :=
  tendsto_nhdsWithin_iff.mpr
    ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,self_mem_nhdsWithin⟩

/-- A selected wave with its actual unit power normalization has square o(t) in the supercritical range.
Use: endpoint_difference_mode_limit proves the zero limit for each genuine summand in the profile-minus-Green comparison before summing.
Article: jacobi, Proposition C.4.
Proof: factor the square quotient into the squared normalized wave and t^(2*gamma-1). The first tends to one and the second to zero; all power identities hold on the genuine positive endpoint filter. -/
theorem selected_wave_square_limit {a : ℝ} (hg : 1/2<gamma a) {f : HalfInterval → ℝ}
    (hf : Tendsto (fun t => f t/(t:ℝ)^(gamma a)) (𝓝[>] halfZero) (𝓝 1)) :
    Tendsto (fun t => (f t)^2/(t:ℝ)) (𝓝[>] halfZero) (𝓝 0) := by
  -- The leftover positive power is essential; the all-mode bound alone does not give this fixed-mode limit.
  have hp : 0<2*gamma a-1 := by linarith
  have ht : Tendsto (fun t : HalfInterval => (t:ℝ)^(2*gamma a-1))
      (𝓝[>] halfZero) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const (0:ℝ) (2*gamma a-1) (Or.inr hp.le)).tendsto.comp
      (tendsto_nhds_of_tendsto_nhdsWithin half_endpoint_tendsto)
    simpa only [Function.comp_def,Real.zero_rpow hp.ne'] using h
  have h := (hf.pow 2).mul ht
  simp only [one_pow,one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t htp
  have htpos : 0<(t:ℝ) := htp
  have hpower : ((t:ℝ)^(gamma a))^2=(t:ℝ)*(t:ℝ)^(2*gamma a-1) := by
    calc
      _ = (t:ℝ)^(2*gamma a) := by
        rw [← Real.rpow_two ((t:ℝ)^(gamma a)),← Real.rpow_mul htpos.le]
        congr 1
        ring
      _ = (t:ℝ)^(1+(2*gamma a-1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add htpos,Real.rpow_one]
  rw [div_pow,hpower]
  field_simp [(Real.rpow_pos_of_pos htpos (2*gamma a-1)).ne',htpos.ne']

/-- Each actual original profile-minus-reference-Green spectral term, divided by t, tends to zero above the critical order.
Use: supercritical_profile_difference_limit combines these genuine mode limits with one proved summable all-index majorant.
Article: jacobi, Proposition C.4.
Proof: apply the selected-wave square lemma to the genuine transformed wave and to the independently normalized reference wave, then multiply by their fixed original spectral coefficients. -/
theorem endpoint_difference_mode_limit {a : ℝ} (ha : -1<a) (hg : 1/2<gamma a) (k : ℕ) :
    Tendsto (fun t : HalfInterval =>
      (jacobi.Bessel.edgeValue a ha k*spectralProfile a ha k (halfInclusion t)-
        2*energyGreenTerm a 0 k t t)/(t:ℝ)) (𝓝[>] halfZero) (𝓝 0) := by
  -- Both wave limits refer to the original enumerated mode k, and no uniformity in k is assumed here.
  have hu := selected_wave_square_limit hg (normalizedEndpointWave_limit a ha k)
  have hv := selected_wave_square_limit hg ((realSolution_endpoint_limit a (eigenvalue a k)).comp half_endpoint_tendsto)
  have h := (hu.const_mul (jacobi.Bessel.edgeValue a ha k*normingRatio a ha k/norming a k)).sub
    (hv.const_mul (2/(norming a k*eigenvalue a k)))
  simp only [mul_zero,sub_zero] at h
  convert h using 1
  ext t
  rw [spectralProfile_half]
  simp only [energyGreenTerm,sub_zero,realSolution_at_reference]
  ring

end
end jacobi.Trichotomy
