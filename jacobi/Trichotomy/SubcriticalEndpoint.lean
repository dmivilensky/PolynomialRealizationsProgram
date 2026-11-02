import jacobi.Trichotomy.EndpointWaves
import jacobi.Trichotomy.EndpointWeights
import jacobi.GelfandLevitan.ProfileSeries

/-!
Article: jacobi, Proposition C.4.
The actual persymmetric profile has its full printed positive endpoint
asymptotic in the compact-support regime. The proof passes to the limit
in the unchanged original spectral series, using its proved summable
weights and the all-mode normalized selected-branch estimate.
Use: endpoint_profile_limit applies dominated convergence to the source's actual profile, with its original normalization retained exactly.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The actual endpoint-normalized persymmetric profile is the same original weighted squared normalized-wave series.
Use: endpoint_profile_limit applies dominated convergence to the source's actual profile, with its original normalization retained exactly.
Article: jacobi, Proposition C.4.
Proof: point-evaluation of the genuine original profile series commutes
with its scalar division. The actual half-interval inclusion fixes the
original folded coordinate, and t^(2gamma)=(t^gamma)^2. -/
theorem endpoint_profile_series (a:ℝ) (ha:-1<a) (t:HalfInterval) :
    persymmetricProfile a ha (halfInclusion t)/(t:ℝ)^(2*gamma a)=
      ∑'k,endpointWeight a ha k*(normalizedEndpointWave a ha k t)^2 := by
  -- The identity also respects the totalized zero endpoint; no artificial endpoint value is introduced.
  rw [persymmetricProfile_apply,← tsum_div_const]
  apply tsum_congr
  intro k
  have hp : (t:ℝ)^(2*gamma a)=((t:ℝ)^(gamma a))^2 := by
    rw [show 2*gamma a=gamma a*2 by ring,Real.rpow_mul t.property.1,Real.rpow_two]
  change jacobi.Bessel.edgeValue a ha k*((normingRatio a ha k/norming a k)*
    (realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) (physicalFold (halfInclusion t)))^2)/
      (t:ℝ)^(2*gamma a)=_
  rw [physicalFold_halfInclusion,hp,normalizedEndpointWave,endpointWeight,div_pow]
  ring

/-- The genuine original persymmetric profile has exactly the printed finite positive leading endpoint constant below alpha=-1/2.
Use: Proposition C.4's compact packing interval and endpoint density power law start from this actual proved profile asymptotic.
Article: jacobi, Proposition C.4.
Source: dominated convergence for an actually summable series.
Proof: each genuine normalized selected wave tends to one and all have
one common bound. The positive original endpoint weights are summable
in this exact regime. Their constant multiple dominates every squared
normalized-wave term, so the actual profile ratio tends to their true sum. -/
theorem endpoint_profile_limit (a:ℝ) (ha:-1<a) (hsub:a < -(1/2:ℝ)) :
    Tendsto (fun t:HalfInterval => persymmetricProfile a ha (halfInclusion t)/(t:ℝ)^(2*gamma a))
      (𝓝[>] halfZero) (𝓝 (endpointConstant a ha)) := by
  -- Every series term and every limit here belongs to the original GL/Bessel construction.
  obtain ⟨C,hC,hbound⟩ := normalizedEndpointWave_bound a ha
  have hs := endpointWeight_summable a ha hsub
  have h := tendsto_tsum_of_dominated_convergence (hs.mul_right (C^2))
    (fun k => ((normalizedEndpointWave_limit a ha k).pow 2).const_mul (endpointWeight a ha k)) (by
      apply Eventually.of_forall
      intro t k
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos (endpointWeight_pos a ha k),norm_pow,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hbound k t) 2) (endpointWeight_pos a ha k).le)
  simpa only [one_pow,mul_one,endpoint_profile_series,endpointConstant] using h

/-- The genuine endpoint coefficient has exactly the source's alternative adjacent-Bessel summand formula.
Use: endpointConstant_bessel identifies both printed expressions for c_alpha in Proposition C.4.
Article: jacobi, Proposition C.4.
Proof: insert the already proved fully normalized Bessel norming weight,
use the same true identity sigma_k=j_k^2, and subtract two from the
positive-base exponent alpha+1. -/
theorem endpointWeight_bessel (a:ℝ) (ha:-1<a) (k:ℕ) :
    endpointWeight a ha k=2*besselNormingScale a*
      (jacobi.Bessel.positiveZero a ha k)^(a-1)/
        |jacobi.Bessel.cylindrical (a+1) (jacobi.Bessel.positiveZero a ha k)| := by
  -- The exact adjacent-order normalization was proved independently for the same original spectral data.
  rw [endpointWeight,norming_weight_formula ha,jacobi.Bessel.edgeValue,
    ← (jacobi.Bessel.positiveZero_properties ha k).2]
  have hj := (jacobi.Bessel.positiveZero_properties ha k).1
  rw [show a-1=(a+1)-2 by ring,Real.rpow_sub hj,Real.rpow_two]
  ring

/-- The two original endpoint coefficient sums satisfy the printed scalar identity.
Use: together with endpointConstant_bessel_hasSum, gives the genuine convergent constant-identification clause of Proposition C.4 in the compact-support regime.
Article: jacobi, Proposition C.4.
Proof: substitute the proved true original summand identity in its
genuine full sum and factor out the unchanged source normalization. -/
theorem endpointConstant_bessel (a:ℝ) (ha:-1<a) :
    endpointConstant a ha=2*besselNormingScale a*
      ∑'k,(jacobi.Bessel.positiveZero a ha k)^(a-1)/
        |jacobi.Bessel.cylindrical (a+1) (jacobi.Bessel.positiveZero a ha k)| := by
  rw [endpointConstant]
  simp only [endpointWeight_bessel,mul_div_assoc,tsum_mul_left]

/-- The source's adjacent-Bessel endpoint series genuinely converges to its printed normalized positive constant in the complete subcritical regime.
Use: supplies explicit convergence, as well as the algebraic sum identity, for both original expressions of c_alpha in Proposition C.4.
Article: jacobi, Proposition C.4.
Proof: divide the already proved summable original endpoint-weight
series by the genuine nonzero normalization 2*mathfrak_w_alpha. Its
exact independently proved Gamma normalization excludes zero. The
actual adjacent-Bessel summand identity then identifies every term. -/
theorem endpointConstant_bessel_hasSum (a:ℝ) (ha:-1<a) (hsub:a < -(1/2:ℝ)) :
    HasSum (fun k:ℕ=>(jacobi.Bessel.positiveZero a ha k)^(a-1)/
      |jacobi.Bessel.cylindrical (a+1) (jacobi.Bessel.positiveZero a ha k)|)
      (endpointConstant a ha/(2*besselNormingScale a)) := by
  -- Convergence is inherited from the same genuine positive original weights, not inferred from a totalized sum equality.
  have hw : besselNormingScale a≠0 := by
    intro hz
    have h := besselNormingScale_normalization ha
    rw [hz,mul_zero] at h
    exact zero_ne_one h
  have hs := (endpointWeight_summable a ha hsub).hasSum.div_const (2*besselNormingScale a)
  apply hs.congr_fun
  intro k
  rw [endpointWeight_bessel]
  field_simp [hw]

end
end jacobi.Trichotomy
