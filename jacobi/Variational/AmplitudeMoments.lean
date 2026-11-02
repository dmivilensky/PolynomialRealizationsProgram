import jacobi.Variational.TopActivity
import jacobi.Continuum.MultipleIntegrals

/-!
Actual amplitude scaling of every spectral moment and of the full
extended Fredholm observation. The cyclic integral gives all moments
without requiring a new eigenvalue enumeration; the nonnegative series
then also handles poles. The edge data use the same exact scalar law.
Use: AllThreeTerm rescales the three homogeneous calibrations for the
one-quarter Nesterov edge, retaining their original variational meaning.
Article: jacobi, Theorem 5.3.
Article role: amplitude scaling and the one-eighth homogeneous lower bound at the quarter spectrum.
-/
namespace jacobi.Variational
noncomputable section
open Real Set MeasureTheory chebyshev2.Continuum jacobi.Continuum
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

/-- All genuine positive integer spectral moments have their exact
amplitude homogeneity, proved from the actual convergent cyclic integrals.
Article: jacobi, Theorem 5.3.
-/
theorem Density.scale_moment (m : Density) (c : ℝ) (hc : 0≤c) (n : ℕ) :
    (∑' j,(m.scale c hc).spectrum j^(n+1))=c^(n+1)*∑' j,m.spectrum j^(n+1) := by
  simp only [L1Source.spectrum]
  rw [moment_multiple_integral (m.scale c hc).integrable (m.scale c hc).measurable
    (m.scale c hc).nonneg n,moment_multiple_integral m.integrable m.measurable m.nonneg n]
  have he : cycleIntegrand (m.scale c hc).value n=
      fun z => c^(n+1)*cycleIntegrand m.value n z := by
    funext z
    simp only [cycleIntegrand_product,Density.scale,Finset.prod_mul_distrib,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    ring
  rw [he,integral_const_mul]

/-- The full actual Fredholm observation obeys the exact amplitude and
spectral-parameter law, including infinite values at or beyond poles.
Article: jacobi, Theorem 5.3.
-/
theorem Density.scale_fredholm (m : Density) (c : ℝ) (hc : 0≤c) {s : ℝ} (hs : 0≤s) :
    (m.scale c hc).fredholm s=m.fredholm (c*s) := by
  rw [(m.scale c hc).fredholm_series hs,m.fredholm_series (mul_nonneg hc hs)]
  apply tsum_congr
  intro n
  rw [Density.scale_moment m c hc (n+1),ENNReal.ofReal_mul (pow_nonneg hc _)]
  rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0≤s^(n+2)/((n:ℝ)+2))]
  have he : (s^(n+2)/((n:ℝ)+2))*c^(n+2)=(c*s)^(n+2)/((n:ℝ)+2) := by
    rw [mul_pow]
    ring
  rw [he]

/-- Positive scalar multiplication of the actual edge data, retaining
its original order, positivity and summability.
Article: jacobi, Theorem 5.3.
-/
def EdgeSpectrum.scale (Λ : EdgeSpectrum) (c : ℝ) (hc : 0<c) : EdgeSpectrum where
  value j := c*Λ.value j
  positive j := mul_pos hc (Λ.positive j)
  antitone _ _ hij := mul_le_mul_of_nonneg_left (Λ.antitone hij) hc.le
  summable := Λ.summable.mul_left c

/-- The prescribed edge mass scales by the same actual amplitude.
Article: jacobi, Theorem 5.3.
-/
theorem EdgeSpectrum.scale_mass (Λ : EdgeSpectrum) (c : ℝ) (hc : 0<c) :
    (Λ.scale c hc).mass=c*Λ.mass := tsum_mul_left

/-- The second prescribed spectral threshold scales quadratically.
Article: jacobi, Theorem 5.3.
-/
theorem EdgeSpectrum.scale_second (Λ : EdgeSpectrum) (c : ℝ) (hc : 0<c) :
    (Λ.scale c hc).second=c^2*Λ.second := by
  change (∑' j,(c*Λ.value j)^2)=_
  simp only [mul_pow]
  exact tsum_mul_left

/-- The full edge Fredholm threshold has exactly the same amplitude
law as the actual density observation, also for infinite thresholds.
Article: jacobi, Theorem 5.3.
-/
theorem EdgeSpectrum.scale_fredholm (Λ : EdgeSpectrum) (c : ℝ) (hc : 0<c) (s : ℝ) :
    (Λ.scale c hc).fredholm s=Λ.fredholm (c*s) := by
  unfold EdgeSpectrum.fredholm fredholmSpectrum
  apply tsum_congr
  intro j
  change fredholmTerm s (c*Λ.value j)=fredholmTerm (c*s) (Λ.value j)
  have he : s*(c*Λ.value j)=(c*s)*Λ.value j := by ring
  simp only [fredholmTerm,fredholmLog,he]

end
end jacobi.Variational
