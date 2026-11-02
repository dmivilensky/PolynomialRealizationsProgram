import jacobi.GelfandLevitan.HalfInteger
import jacobi.Reference.HalfSine

/-!
Article: jacobi, Section 3.2 (sharp comparison at U).
The actual original reflected spectral profiles are exactly
2*sin^2(pi*(k+1)*t) on the whole closed interval. Their eigenvalues
are the original pi^2*(k+1)^2, with no rescaled target spectrum.
The profile sum and its squared integral remain the original constructed
persymmetric quantities.
Use: the alpha=1/2 profile series has the article's literal coefficients 4/(pi^2*(k+1)^2).
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference

/-- The actual target eigenvalues at order 1/2 are precisely the original integer sine spectrum.
Use: the alpha=1/2 profile series has the article's literal coefficients 4/(pi^2*(k+1)^2).
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the genuine target spectrum coincides with the original reference spectrum; gamma=1 and c_0=0 in its exact formula. -/
theorem half_sine_spectrum (ha : -1<(1/2:ℝ)) (k : ℕ) :
    jacobi.Bessel.sigma (1/2) ha k=Real.pi^2*(k+1:ℝ)^2 := by
  rw [half_integer_spectra ha (Or.inl rfl)]
  norm_num [eigenvalue,gamma,jacobi.Jacobi.endpointCorrection]

/-- The actual constructed whole-interval profiles at order 1/2 are the original normalized sine squares.
Use: the alpha=1/2 persymmetric profile and constant reduce to their literal sine series in the source normalization.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the actual GL reduction gives the genuine normalized reference
square. Substitute its proved original sine value and actual integral
norm; the true nonzero frequency cancels exactly. -/
theorem half_sine_spectralProfile (ha : -1<(1/2:ℝ)) (k : ℕ) (t : Interval) :
    spectralProfile (1/2) ha k t=2*(Real.sin (Real.pi*(k+1:ℝ)*(t:ℝ)))^2 := by
  rw [half_integer_spectralProfile ha (Or.inl rfl),half_sine_eigenfunction k t.property,
    half_sine_norming]
  field_simp [Real.pi_ne_zero,show (k+1:ℝ)≠0 by positivity]

/-- The actual original persymmetric profile at order 1/2 has exactly the article's original sine series.
Use: its subsequent polynomial and energy evaluations concern the constructed original phi, including both physical endpoints.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: substitute the genuine special-order spectrum and actual
whole-interval sine profiles in the already proved pointwise source series. -/
theorem half_sine_persymmetricSeries (ha : -1<(1/2:ℝ)) (t : Interval) :
    persymmetricProfile (1/2) ha t=
      ∑' k:ℕ,4*(Real.sin (Real.pi*(k+1:ℝ)*(t:ℝ)))^2/(Real.pi^2*(k+1:ℝ)^2) := by
  rw [persymmetricProfile_apply]
  apply tsum_congr
  intro k
  rw [half_sine_spectralProfile,jacobi.Bessel.edgeValue,half_sine_spectrum]
  ring

end
end jacobi.GelfandLevitan
