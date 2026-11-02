import jacobi.GelfandLevitan.TargetGreenAction
import jacobi.GelfandLevitan.ShrinkingIntegral
import jacobi.Bessel.EdgeData

/-!
Article: jacobi, Proposition 2.2.
Every actual full spectral profile has integral one, and the original
persymmetric profile has exactly the printed Bessel mass. The genuine
complete transformed Hilbert basis fixes the normalization before the
uniform profile series is integrated by a bounded linear functional.
Use: persymmetricProfile_integral evaluates the original packing mass by integrating its genuine uniformly summable source series.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- Every actual reflected spectral profile has exactly unit physical integral.
Use: persymmetricProfile_integral evaluates the original packing mass by integrating its genuine uniformly summable source series.
Article: jacobi, Proposition 2.2.
Proof: the actual original full target Hilbert basis is orthonormal and
has the genuine full continuous wave as representative. Its squared
integral is its Hilbert norm square, and its pointwise square is Phi_k. -/
theorem spectralProfile_integral (a:ℝ) (ha:-1<a) (k:ℕ) :
    (∫t:Interval,spectralProfile a ha k t)=1 := by
  -- The full-interval basis supplies the exact normalization, including the reflected half.
  have hnorm : inner ℝ (fullTargetBasis a ha k) (fullTargetBasis a ha k)=1 := by
    simpa only [ite_true] using (orthonormal_iff_ite.mp (fullTargetBasis a ha).orthonormal k k)
  rw [L2.inner_def] at hnorm
  convert hnorm using 1
  apply integral_congr_ae
  filter_upwards [fullTargetBasis_wave_ae a ha k] with t ht
  rw [← fullWaveMap_sq,ht]
  change (fullWaveMap a ha k t)^2=fullWaveMap a ha k t*fullWaveMap a ha k t
  ring

/-- The original persymmetric profile has exactly the source's prescribed Bessel mass.
Use: the intrinsic change of variables in Proposition C.4 gives integral m_alpha=M from this actual unchanged profile integral.
Article: jacobi, Proposition 2.2.
Proof: the genuine bounded physical integration map commutes with the
proved uniform source series. Every actual Phi_k has integral one;
the already proved original first Rayleigh sum gives the printed value. -/
theorem persymmetricProfile_integral (a:ℝ) (ha:-1<a) :
    (∫t:Interval,persymmetricProfile a ha t)=1/(2*(a+1)) := by
  -- No merely formal exchange of integration and an unproved spectral series is used.
  have h := unitRowIntegral.hasSum (profileSeries_summable a ha).hasSum
  have he (k:ℕ) : unitRowIntegral (jacobi.Bessel.edgeValue a ha k • spectralProfile a ha k)=
      jacobi.Bessel.edgeValue a ha k := by
    rw [map_smul,unitRowIntegral_apply,spectralProfile_integral,smul_eq_mul,mul_one]
  simp only [he] at h
  rw [← unitRowIntegral_apply]
  exact h.tsum_eq.symm.trans (jacobi.Bessel.first_rayleigh_sum ha)

end
end jacobi.GelfandLevitan
