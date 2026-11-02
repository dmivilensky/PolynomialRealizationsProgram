import jacobi.GelfandLevitan.HalfInteger
import jacobi.Reference.SineIdentification
import chebyshev2.SineContinuum.MercerClosed

/-!
Article: jacobi, Proposition C.4.
The actual constructed persymmetric profile is exactly twice the
previously verified sine--Jacobi Green diagonal. Its original squared
integral is exactly c_sin from chebyshev1 and chebyshev2.
This reuses the earlier genuine Legendre Mercer expansion, including
both physical endpoints, and retains all original source definitions.
Use: sine_persymmetricProfile identifies the constructed original profile series with the earlier verified sine Green diagonal.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual whole-interval spectral profile at order -1/2 is the original sine--Legendre eigenfunction square.
Use: sine_persymmetricProfile identifies the constructed original profile series with the earlier verified sine Green diagonal.
Article: jacobi, Proposition C.4.
Proof: the proved actual special-order GL reduction gives the genuine normalized reference square, already identified with the earlier sine--Legendre basis. -/
theorem sine_spectralProfile (ha : -1< -(1/2:ℝ)) (k : ℕ) (t : Interval) :
    spectralProfile (-(1/2)) ha k t=(chebyshev2.SineContinuum.upsilon k t)^2 := by
  rw [half_integer_spectralProfile ha (Or.inr rfl)]
  exact sine_eigenfunction_square k t.property

/-- The original Bessel edge weight at order -1/2 is exactly twice the existing sine Green eigenvalue.
Use: sine_persymmetricProfile compares the actual original spectral coefficients in the same normalization.
Article: jacobi, Proposition C.4.
Proof: the actual target and reference spectra coincide; the reference spectrum is precisely the previous sine--Legendre spectrum. -/
theorem sine_edgeValue (ha : -1< -(1/2:ℝ)) (k : ℕ) :
    jacobi.Bessel.edgeValue (-(1/2)) ha k=2/chebyshev2.SineContinuum.mu k := by
  rw [jacobi.Bessel.edgeValue,half_integer_spectra ha (Or.inr rfl),sine_eigenvalue]

/-- The actual persymmetric profile at order -1/2 is exactly the previously verified sine--Jacobi density on the full closed interval.
Use: sine_persymmetricConstant identifies the original constructed c_star with the already verified c_sin; this also gives its closed elliptic profile through the earlier article.
Article: jacobi, Proposition C.4.
Proof: the actual source weights and profiles give twice the genuine
sine--Legendre Mercer series. Its earlier proved closed-interval sum
is the original sine Green diagonal; twice that diagonal is the original sine density. -/
theorem sine_persymmetricProfile (ha : -1< -(1/2:ℝ)) (t : Interval) :
    persymmetricProfile (-(1/2)) ha t=chebyshev2.SineJacobi.phi t := by
  -- The sum is the original constructed source series, including both endpoint values.
  rw [persymmetricProfile_apply]
  calc
    _ = ∑' k:ℕ,2*((chebyshev2.SineContinuum.upsilon k t)^2/
        chebyshev2.SineContinuum.mu k) := by
      apply tsum_congr
      intro k
      rw [sine_spectralProfile,sine_edgeValue]
      ring
    _ = 2*chebyshev2.SineContinuum.green t t := by
      rw [tsum_mul_left,(chebyshev2.SineContinuum.green_mercer_diagonal_closed t.property).tsum_eq]
    _ = _ := chebyshev2.SineContinuum.green_diagonal t

/-- The actual original persymmetric constant at order -1/2 is exactly c_sin from the two earlier articles.
Use: completes the c_sin identification in the alpha=-1/2 special case of Proposition C.2, retaining the earlier closed elliptic and decimal theorems without repeating their proofs.
Article: jacobi, Proposition C.4.
Proof: the proved actual whole-interval profiles coincide pointwise.
The genuine subtype Lebesgue integral equals the original closed
interval integral, since its two endpoints have zero measure. -/
theorem sine_persymmetricConstant (ha : -1< -(1/2:ℝ)) :
    persymmetricConstant (-(1/2)) ha=chebyshev1.SineJacobi.sineEnergy := by
  -- Both constants retain their actual defining squared-density integrals.
  unfold persymmetricConstant
  simp_rw [sine_persymmetricProfile]
  rw [integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc
    (fun t:ℝ => (chebyshev2.SineJacobi.phi t)^2)]
  change (∫ t:ℝ in Icc (0:ℝ) 1,(chebyshev1.SineJacobi.sineDensity t)^2)=_
  rw [integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)).symm

end
end jacobi.GelfandLevitan
