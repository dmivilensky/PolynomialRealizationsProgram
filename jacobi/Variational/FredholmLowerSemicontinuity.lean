import jacobi.Variational.FredholmRelaxation
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
Article: jacobi, Appendix D.1 (lower semicontinuity).
The actual extended Fredholm observation is lower semicontinuous under L1
convergence of nonnegative densities, including at and beyond its spectral
pole. Fatou is applied twice to the proved nonnegative scalar power series
and the actual eigenvalue series. Thus no logarithmic pole separation is
assumed for this approximation step.
Source: Fatou for counting measure and trace-class L1 spectral stability.
Use: passes spectral and Fredholm power series through approximation without assuming finite sums.
-/
namespace jacobi.Variational
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Fatou's inequality for a double sequence of nonnegative extended summands.
Use: passes spectral and Fredholm power series through approximation without assuming finite sums.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: use Fatou for counting measure on the natural numbers. -/
theorem ennreal_series_fatou (F : ℕ → ℕ → ℝ≥0∞) :
    (∑' j, liminf (fun n => F n j) atTop) ≤ liminf (fun n => ∑' j, F n j) atTop := by
  have h := lintegral_liminf_le (μ := Measure.count) (u := atTop) (fun n => measurable_of_countable (F n))
  simpa only [lintegral_count] using h

/-- The scalar regularized logarithm is lower semicontinuous along nonnegative real sequences, including its infinite branch.
Use: transfers the Fredholm constraint through arbitrary L1 approximations of densities.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: every power-series summand is continuous and nonnegative; Fatou for
the proved full scalar series preserves the limiting value at poles as well. -/
theorem fredholmTerm_le_liminf {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ht : Tendsto a atTop (𝓝 x)) :
    fredholmTerm s x ≤ liminf (fun n => fredholmTerm s (a n)) atTop := by
  -- Work with the nonnegative series rather than a real logarithm that is undefined at the pole.
  simp_rw [fredholmTerm_series hs hx,fredholmTerm_series hs (ha _)]
  have hpoint (j : ℕ) : liminf (fun n => ENNReal.ofReal ((s*a n)^(j+2)/((j : ℝ)+2))) atTop=
      ENNReal.ofReal ((s*x)^(j+2)/((j : ℝ)+2)) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((ht.const_mul s).pow (j+2)).div_const ((j : ℝ)+2))).liminf_eq
  have h := ennreal_series_fatou (fun n j => ENNReal.ofReal ((s*a n)^(j+2)/((j : ℝ)+2)))
  simp_rw [hpoint] at h
  exact h

/-- Every actual ordered eigenvalue converges under L1 convergence of densities.
Use: the same spectral stability theorem controls all Fredholm summands in the approximation step.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: each entry error is bounded by the actual spectral l1 distance, itself
bounded by the L1 density error, which tends to zero. -/
theorem spectrum_limit_of_l1 (m : ℕ → Density) (q : L1Source)
    (hl : Tendsto (fun n => ∫ x, |(m n).value x-q.value x|) atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun n => (m n).spectrum j) atTop (𝓝 (q.spectrum j)) := by
  -- Neither symmetry nor a uniform pole margin is required for the density spectral estimate.
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hl
  intro n
  rw [Real.norm_eq_abs]
  exact (entry_distance
    (chebyshev2.Continuum.kernelSpectralData (m n).integrable (m n).nonneg).eigenvalue_summable
    (chebyshev2.Continuum.kernelSpectralData q.integrable q.nonneg).eigenvalue_summable j).trans
      (kernel_distance (m n).integrable q.integrable (m n).nonneg q.nonneg)

/-- Entrywise limits of nonnegative spectra preserve the extended Fredholm lower bound, including poles.
Use: spectral l1 convergence in Transfer implies the limiting Fredholm constraint without a pole-margin premise.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: apply scalar lower semicontinuity to every entry and Fatou to the nonnegative eigenvalue series. -/
theorem fredholmSpectrum_le_liminf {s : ℝ} (hs : 0 ≤ s) (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (ha : ∀ n j, 0 ≤ a n j) (hb : ∀ j, 0 ≤ b j)
    (ht : ∀ j, Tendsto (fun n => a n j) atTop (𝓝 (b j))) :
    fredholmSpectrum s b ≤ liminf (fun n => fredholmSpectrum s (a n)) atTop := by
  exact (ENNReal.tsum_le_tsum fun j => fredholmTerm_le_liminf hs (hb j)
    (fun n => a n j) (fun n => ha n j) (ht j)).trans (ennreal_series_fatou _)

/-- The actual extended Fredholm observation is lower semicontinuous under L1 density convergence, also at poles.
Use: the regular approximation step for the unrestricted Fredholm rearrangement and existence proof.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: actual eigenvalues converge by L1 spectral stability. Apply the proved
scalar lower semicontinuity to each eigenvalue and Fatou once more to their nonnegative series. -/
theorem fredholm_le_liminf_of_l1 (m : ℕ → Density) (q : L1Source)
    (hl : Tendsto (fun n => ∫ x, |(m n).value x-q.value x|) atTop (𝓝 0))
    {s : ℝ} (hs : 0 ≤ s) : q.fredholm s ≤ liminf (fun n => (m n).fredholm s) atTop := by
  -- Both series are allowed to be infinite; there is no subtraction of extended infinite quantities.
  change (∑' j, fredholmTerm s (q.spectrum j)) ≤
    liminf (fun n => ∑' j, fredholmTerm s ((m n).spectrum j)) atTop
  exact fredholmSpectrum_le_liminf hs (fun n => (m n).spectrum) q.spectrum
    (fun n => (chebyshev2.Continuum.kernelSpectralData (m n).integrable (m n).nonneg).eigenvalue_nonneg)
    (chebyshev2.Continuum.kernelSpectralData q.integrable q.nonneg).eigenvalue_nonneg
    (spectrum_limit_of_l1 m q hl)

end
end jacobi.Variational
