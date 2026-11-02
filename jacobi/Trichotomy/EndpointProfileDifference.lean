import jacobi.Trichotomy.EndpointErrorAlgebra
import jacobi.Trichotomy.EndpointCoefficients
import jacobi.GelfandLevitan.ProfileSeries

/-!
Article: jacobi, Proposition C.4.
Use: supercritical_profile_difference_limit applies dominated convergence to the unchanged original spectral series all the way down to the endpoint.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- One summable original-index majorant bounds the actual profile-minus-reference-Green summands after division by every positive physical t.
Use: supercritical_profile_difference_limit applies dominated convergence to the unchanged original spectral series all the way down to the endpoint.
Article: jacobi, Proposition C.4.
Proof: insert the proved original coefficient bounds, norm lower bound and common transformed/reference wave envelope into the elementary squared-error inequality. Its two normalized envelope bounds hold because gamma>1/2. -/
theorem endpoint_profile_difference_bound {a : ℝ} (ha : -1<a) (hg : 1/2<gamma a)
    (h0 : 0<eigenvalue a 0) :
    ∃ A B : ℝ,0<A ∧ 0<B ∧ ∀ k : ℕ,∀ t : HalfInterval,0<(t:ℝ) →
      |(jacobi.Bessel.edgeValue a ha k*spectralProfile a ha k (halfInclusion t)-
        2*energyGreenTerm a 0 k t t)/(t:ℝ)|≤A/(k+1:ℝ)^3+B/(k+1:ℝ)^2 := by
  -- Every premise below is a proved property of the same actual original data, not an additional spectral certificate.
  obtain ⟨_L,B,D,_hL,hB,hD,hcoeff⟩ := endpoint_coefficient_bounds ha h0
  obtain ⟨C,hC,hwave⟩ := endpoint_wave_comparison a ha
  obtain ⟨c,_Q,hc,_hQ,hnorm⟩ := norming_bounds ha
  refine ⟨D*C^2/c,2*B*C^2/c,by positivity,by positivity,fun k t ht => ?_⟩
  have hm : 0≤waveEnvelope a k t := le_min (Real.rpow_nonneg t.property.1 _)
    (Real.rpow_nonneg (by positivity) _)
  have hT : 0≤2/eigenvalue a k := div_nonneg (by norm_num)
    (by simpa only [sub_zero] using (energy_gap_pos ha h0 k).le)
  have h := endpoint_error_algebra (L := jacobi.Bessel.edgeValue a ha k)
    (rho := normingRatio a ha k) (T := 2/eigenvalue a k)
    (u := realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) t)
    (v := eigenfunction a k t) (by positivity : 0<(k+1:ℝ)) ht
    (Real.rpow_pos_of_pos (by positivity : 0<(k+1:ℝ)) _) hc hC hD hB hm hT
    (hnorm k).1 (hcoeff k).2.2 (hcoeff k).2.1
    (hwave k t).1 (hwave k t).2.1 (hwave k t).2.2
    (waveEnvelope_normalized_bounds hg k t.property.1).1
    (waveEnvelope_normalized_bounds hg k t.property.1).2
  rw [spectralProfile_half]
  simp only [energyGreenTerm,sub_zero]
  convert h using 1
  field_simp

/-- The actual full profile-minus-reference-Green quotient equals the sum of the original normalized spectral differences.
Use: supercritical_profile_difference_limit passes the dominated series limit to the source's literal phi_alpha and Green kernel.
Article: jacobi, Proposition C.4.
Proof: point-evaluate the norm-summable profile series and use the independently absolutely summable full Green series. Their actual sums commute with subtraction, multiplication by two and division by the fixed physical coordinate. -/
theorem endpoint_profile_difference_series {a : ℝ} (ha : -1<a)
    (h0 : 0<eigenvalue a 0) (t : HalfInterval) :
    (persymmetricProfile a ha (halfInclusion t)-2*energyGreenKernel a 0 t t)/(t:ℝ)=
      ∑' k,(jacobi.Bessel.edgeValue a ha k*spectralProfile a ha k (halfInclusion t)-
        2*energyGreenTerm a 0 k t t)/(t:ℝ) := by
  -- Both series converge in their original enumeration, including every finite low-frequency term.
  have hs : Summable (fun k => jacobi.Bessel.edgeValue a ha k*spectralProfile a ha k (halfInclusion t)) :=
    (ContinuousMap.evalCLM ℝ (halfInclusion t)).summable (profileSeries_summable a ha)
  have ht : (t:ℝ)∈Icc (0:ℝ) 1 := ⟨t.property.1,t.property.2.trans (by norm_num)⟩
  have hg := (energyGreen_absolute_summable ha h0 ht ht).of_abs
  rw [tsum_div_const,hs.tsum_sub (hg.mul_left 2),tsum_mul_left,persymmetricProfile_apply]
  rfl

end
end jacobi.Trichotomy
