import jacobi.GelfandLevitan.ProfileBounds

/-!
Article: jacobi, Theorem 2.1.
The actual Lambda-weighted reflected profiles form a norm-summable
series of continuous functions on the original unit interval. Its sum
is the source phi_alpha, is nonnegative and symmetric, and the genuine
squared-profile integral defines c_star. Identifying these functions
with the target Green diagonal requires the separate spectral theorem P.
Use: defines the true source phi_alpha and justifies its pointwise series, continuity and uniform convergence without a spectral-realization premise.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] spectralProfile

/-- The original persymmetric profile series converges in the actual uniform norm of continuous functions on the whole physical unit interval.
Use: defines the true source phi_alpha and justifies its pointwise series, continuity and uniform convergence without a spectral-realization premise.
Article: jacobi, Theorem 2.1.
Proof: the original positive Bessel Lambda sequence is already proved
summable. The actual continuous profiles have one proved common norm
bound, so their genuine scalar multiples have a summable norm majorant. -/
theorem profileSeries_summable (a : ℝ) (ha : -1<a) :
    Summable (fun k:ℕ => jacobi.Bessel.edgeValue a ha k • spectralProfile a ha k) := by
  obtain ⟨D,_,hPhi⟩ := spectralProfile_uniform_bound a ha
  have hM := (jacobi.Bessel.edgeValue_summable ha).mul_right D
  apply hM.of_norm_bounded (f := fun k:ℕ => jacobi.Bessel.edgeValue a ha k • spectralProfile a ha k)
  intro k
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ((jacobi.Bessel.edgeValue_properties ha).1 k)]
  exact mul_le_mul_of_nonneg_left (hPhi k) ((jacobi.Bessel.edgeValue_properties ha).1 k).le

/-- The original persymmetric profile as the actual norm sum of its continuous reflected spectral profiles.
Use: the square integral below is the article's actual c_star, and the subsequent target spectral realization identifies phi_alpha with twice the true Green diagonal.
Article: jacobi, Theorem 2.1.
-/
def persymmetricProfile (a : ℝ) (ha : -1<a) : C(Interval,ℝ) :=
  ∑' k,jacobi.Bessel.edgeValue a ha k • spectralProfile a ha k

/-- The actual continuous persymmetric profile has exactly the original pointwise Lambda-weighted source series at every physical point.
Use: its positivity, reflection and uniform convergence concern precisely the printed phi_alpha, rather than an independently specified continuous approximation.
Article: jacobi, Theorem 2.1.
Proof: the proved genuine norm summability permits the community continuous point-evaluation functional to commute with the original sum. -/
theorem persymmetricProfile_apply (a : ℝ) (ha : -1<a) (t : Interval) :
    persymmetricProfile a ha t=∑' k,jacobi.Bessel.edgeValue a ha k*spectralProfile a ha k t := by
  have hh := (ContinuousMap.evalCLM ℝ t).map_tsum (profileSeries_summable a ha)
  exact hh

/-- The original natural partial sums converge uniformly to the actual persymmetric profile on the entire physical unit interval.
Use: the source continuum profile is a genuine uniform spectral limit, supporting endpoint control and later interchange with actual integrals.
Article: jacobi, Proposition C.4.
Proof: the same genuine positive summable Lambda majorant dominates
the actual scalar summands at every physical point. Apply the community
uniform-series theorem and identify its true pointwise sum with the
already constructed continuous-function norm sum. -/
theorem persymmetricProfile_uniform_limit (a : ℝ) (ha : -1<a) :
    TendstoUniformly (fun N:ℕ => fun t:Interval =>
      ∑ k∈Finset.range N,jacobi.Bessel.edgeValue a ha k*spectralProfile a ha k t)
      (fun t:Interval => persymmetricProfile a ha t) atTop := by
  -- The majorant comes from the original all-index profile bound and the proved actual Bessel Rayleigh summability.
  obtain ⟨D,_,hPhi⟩ := spectralProfile_uniform_bound a ha
  have hM := (jacobi.Bessel.edgeValue_summable ha).mul_right D
  have hb (k : ℕ) (t : Interval) :
      ‖jacobi.Bessel.edgeValue a ha k*spectralProfile a ha k t‖≤ jacobi.Bessel.edgeValue a ha k*D := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos ((jacobi.Bessel.edgeValue_properties ha).1 k)]
    exact mul_le_mul_of_nonneg_left (((spectralProfile a ha k).norm_coe_le_norm t).trans (hPhi k))
      ((jacobi.Bessel.edgeValue_properties ha).1 k).le
  simpa only [persymmetricProfile_apply] using tendstoUniformly_tsum_nat hM hb

/-- The original constructed persymmetric profile is nonnegative throughout the genuine physical unit interval.
Use: the actual source squared-profile constant is the integral of a genuine continuous nonnegative spectral profile.
Article: jacobi, Proposition 2.2.
Proof: every original edge weight is positive and every actual squared profile is nonnegative; use the exact pointwise convergent source series. -/
theorem persymmetricProfile_nonneg (a : ℝ) (ha : -1<a) (t : Interval) :
    0≤persymmetricProfile a ha t := by
  rw [persymmetricProfile_apply]
  exact tsum_nonneg (fun k => mul_nonneg ((jacobi.Bessel.edgeValue_properties ha).1 k).le
    (spectralProfile_nonneg a ha k t))

/-- The original actual persymmetric profile is symmetric about the genuine physical midpoint.
Use: matches the reflected source profile normalization in the original c_star integral and subsequent target Green-diagonal identity.
Article: jacobi, Theorem 2.1.
Proof: every actual source spectral profile is unchanged by the original physical reflection, so the exact original Lambda-weighted sums agree term by term. -/
theorem persymmetricProfile_reflection (a : ℝ) (ha : -1<a) (t : Interval) :
    persymmetricProfile a ha (physicalReflection t)=persymmetricProfile a ha t := by
  rw [persymmetricProfile_apply,persymmetricProfile_apply]
  apply tsum_congr
  intro k
  rw [spectralProfile_reflection]

/-- The actual original uniformly convergent persymmetric profile vanishes at the physical left endpoint.
Use: gives the source endpoint value of phi_alpha and its later continuous target Green diagonal.
Article: jacobi, Theorem 2.1.
Proof: the exact source series has every actual spectral profile zero at that endpoint. -/
theorem persymmetricProfile_zero (a : ℝ) (ha : -1<a) :
    persymmetricProfile a ha (halfInclusion halfZero)=0 := by
  rw [persymmetricProfile_apply]
  simp only [spectralProfile_zero,mul_zero,tsum_zero]

/-- The actual original persymmetric profile also vanishes at the genuine reflected right endpoint.
Use: supplies both source endpoint values of the continuous profile before its later Green-diagonal identification.
Article: jacobi, Theorem 2.1.
Proof: apply the proved exact source reflection identity and the original zero left endpoint value. -/
theorem persymmetricProfile_reflected_zero (a : ℝ) (ha : -1<a) :
    persymmetricProfile a ha (physicalReflection (halfInclusion halfZero))=0 := by
  rw [persymmetricProfile_reflection,persymmetricProfile_zero]

/-- The actual source persymmetric constant defined from the constructed original uniform spectral profile.
Use: the target spectral theorem later identifies this same original constant with four times the squared Green-diagonal integral, and the special orders with their earlier verified constants.
Article: jacobi, Theorem 2.1.
-/
def persymmetricConstant (a : ℝ) (ha : -1<a) : ℝ :=
  ∫ t:Interval,(persymmetricProfile a ha t)^2

/-- The original squared persymmetric profile is genuinely integrable in the actual Lebesgue measure.
Use: c_star is the true finite source squared-profile integral, not a totalized value of a possibly nonintegrable expression.
Article: jacobi, Theorem 4.1.
Proof: the original profile is a true continuous function on the compact finite-measure physical interval, hence is L2; the community real L2-square theorem gives the actual integral. -/
theorem persymmetricConstant_integrable (a : ℝ) (ha : -1<a) :
    Integrable (fun t:Interval => (persymmetricProfile a ha t)^2) :=
  (ContinuousMap.memLp (p := 2) (μ := volume) ℝ (persymmetricProfile a ha)).integrable_sq

/-- The actual original persymmetric constant is nonnegative in its genuine source normalization.
Use: its later exact Green-kernel and special-order identifications concern this already constructed finite original quantity.
Article: jacobi, Theorem 2.1.
Proof: integrate the actual pointwise nonnegative source profile square in the original Lebesgue measure. -/
theorem persymmetricConstant_nonneg (a : ℝ) (ha : -1<a) :
    0≤persymmetricConstant a ha := integral_nonneg (fun _ => sq_nonneg _)

end
end jacobi.GelfandLevitan
