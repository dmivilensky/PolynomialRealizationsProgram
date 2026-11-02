import jacobi.Variational.RootLimit

/-!
Article: jacobi, Theorem D.4.
Convergence of the actual kernel spectra to an arbitrary edge spectrum in l1
implies convergence of mass and both moment observations. The extended
Fredholm threshold is retained by spectral Fatou, also at poles. Combined
with the proved root limit, this yields all continuum relaxation lower
bounds for any root-normalized density sequence, without an assumed limit.
Source: l1 spectral stability, Fatou and root-normalized compactness.
Use: converts the uniform finite packing error into the exact target constraints of Transfer.
-/
namespace jacobi.Variational
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Actual spectra converging in l1 to an edge spectrum retain its mass and both moment observations.
Use: converts the uniform finite packing error into the exact target constraints of Transfer.
Article: jacobi, Theorem D.4.
Proof: l1 distance controls the trace and each entry; the square-moment error
is bounded by the sum of the two masses times the same distance. -/
theorem density_edge_limits (m : ℕ → Density) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (m n).spectrum Λ.value) atTop (𝓝 0)) :
    Tendsto (fun n => (m n).mass) atTop (𝓝 Λ.mass) ∧
      ∀ i, Tendsto (fun n => observe (m n) i) atTop (𝓝 (threshold Λ i)) := by
  -- All quantities refer to the same actual ordered kernel spectrum and its trace.
  have hma (n : ℕ) : |(m n).mass-Λ.mass| ≤ distance (m n).spectrum Λ.value := by
    have h := mass_distance
      (chebyshev2.Continuum.kernelSpectralData (m n).integrable (m n).nonneg).eigenvalue_summable Λ.summable
    change |(∑' j, (m n).spectrum j)-Λ.mass| ≤ _ at h
    rw [L1Source.spectrum,chebyshev2.Continuum.kernelEigenvalue_mass] at h
    exact h
  have hm : Tendsto (fun n => (m n).mass) atTop (𝓝 Λ.mass) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hma) hd
  refine ⟨hm,fun i => ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  cases i with
  | top =>
    apply squeeze_zero (fun _ => norm_nonneg _) _ hd
    intro n
    exact entry_distance
      (chebyshev2.Continuum.kernelSpectralData (m n).integrable (m n).nonneg).eigenvalue_summable Λ.summable 0
  | second =>
    have ht := (hm.add_const Λ.mass).mul hd
    rw [mul_zero] at ht
    apply squeeze_zero (fun _ => norm_nonneg _) _ ht
    intro n
    have h := square_distance
      (chebyshev2.Continuum.kernelSpectralData (m n).integrable (m n).nonneg).eigenvalue_summable Λ.summable
      (chebyshev2.Continuum.kernelSpectralData (m n).integrable (m n).nonneg).eigenvalue_nonneg
      (fun j => (Λ.positive j).le)
    change |observe (m n) .second-threshold Λ .second| ≤
      ((∑' j, (m n).spectrum j)+Λ.mass)*distance (m n).spectrum Λ.value at h
    rw [L1Source.spectrum,chebyshev2.Continuum.kernelEigenvalue_mass] at h
    exact h

/-- Spectral l1 convergence to an edge spectrum retains every nonnegative Fredholm target in the lower-limit sense.
Use: the Fredholm branch of Transfer needs no extra numerical or pole-margin hypothesis.
Article: jacobi, Theorem D.4.
Proof: every actual eigenvalue converges by the entrywise l1 bound; scalar
and spectral Fatou apply the full nonnegative Fredholm series. -/
theorem edge_fredholm_le_liminf (m : ℕ → Density) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (m n).spectrum Λ.value) atTop (𝓝 0))
    {s : ℝ} (hs : 0 ≤ s) : Λ.fredholm s ≤ liminf (fun n => (m n).fredholm s) atTop := by
  -- Pointwise eigenvalue convergence suffices even when the target has an infinite Fredholm value.
  apply fredholmSpectrum_le_liminf hs (fun n => (m n).spectrum) Λ.value
    (fun n => (chebyshev2.Continuum.kernelSpectralData (m n).integrable (m n).nonneg).eigenvalue_nonneg)
    (fun j => (Λ.positive j).le)
  intro j
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hd
  intro n
  rw [Real.norm_eq_abs]
  exact entry_distance
    (chebyshev2.Continuum.kernelSpectralData (m n).integrable (m n).nonneg).eigenvalue_summable Λ.summable j

/-- Every root-normalized density sequence with an actual limiting edge spectrum satisfies all continuum Transfer bounds.
Use: the analytic Transfer theorem is instantiated by the proved finite packing construction.
Article: jacobi, Theorem D.4.
Proof: the finite lower-energy limit has an actual root-normalized competitor
by the proved root-limit theorem. Spectral l1 convergence fixes its mass and
retains every target moment and Fredholm lower constraint. The actual
variational infima are bounded by this competitor's cost. -/
theorem density_transfer (m : ℕ → Density) (Λ : EdgeSpectrum)
    (hr : ∀ n, (m n).rootMass ≤ 1)
    (hd : Tendsto (fun n => distance (m n).spectrum Λ.value) atTop (𝓝 0)) :
    (∀ S : Set Observation, rootInfimum S Λ.mass (threshold Λ) ≤ liminf (fun n => (m n).cost) atTop) ∧
      ∀ s : ℝ, 0 ≤ s → rootFredholmInfimum s Λ.mass (Λ.fredholm s) ≤ liminf (fun n => (m n).cost) atTop := by
  -- No actual limiting density is included in the hypotheses; it is constructed at finite lower cost.
  by_cases hL : liminf (fun n => (m n).cost) atTop=∞
  · simp only [hL,le_top,implies_true,and_self]
  obtain ⟨hm,hobs⟩ := density_edge_limits m Λ hd
  obtain ⟨q,hqs,hqM,hqR,hqC,hqO,hqF⟩ := root_limit_at_liminf m hm hr hL
  have hqT (i : Observation) : threshold Λ i ≤ observe q i := by
    have ht := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hobs i)).liminf_eq
    simp only [Function.comp_def] at ht
    have h := hqO i
    rw [ht] at h
    have hn : 0 ≤ observe q i := by
      cases i with
      | second => exact tsum_nonneg (fun j => sq_nonneg _)
      | top => exact (chebyshev2.Continuum.kernelSpectralData q.integrable q.nonneg).eigenvalue_nonneg 0
    exact (ENNReal.ofReal_le_ofReal_iff hn).mp h
  refine ⟨fun S => ?_,fun s hs => ?_⟩
  · have hi : rootInfimum S Λ.mass (threshold Λ) ≤ q.cost :=
      sInf_le ⟨q,⟨hqM,hqR,fun i _ => hqT i⟩,rfl⟩
    exact hi.trans hqC
  · have hqd := (edge_fredholm_le_liminf m Λ hd hs).trans (hqF s hs)
    have hi : rootFredholmInfimum s Λ.mass (Λ.fredholm s) ≤ q.cost := sInf_le ⟨q,⟨hqM,hqR,hqd⟩,rfl⟩
    exact hi.trans hqC

end
end jacobi.Variational
