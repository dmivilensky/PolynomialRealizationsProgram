import bezout.Risk.Bounds
import bezout.History.Realization
import bezout.Lower.EndpointGain
import chebyshev1.Spectral.Sharpness

/-!
Article: bezout, Theorem 4.1, spectral and Hilbert--Schmidt gains.
Use: the exact physical kernel of an unrestricted causal history is
identified with the established realization gain and its sharp matrix
theory. Positive endpoint factorizations attain the full spectral maximum.
Proof: the actual history-to-realization bridge, finite Cauchy--Schwarz
and compactness of the closed spectral square.
-/

namespace bezout.History
noncomputable section
open scoped BigOperators
variable {N : ℕ}

/-- The maximum temporal physical-kernel norm over the entire spectral square. -/
def spectralGain (h : bezout.History N) (I : chebyshev1.SpectralInterval) : ℝ :=
  h.realization.gain I N

/-- The realization kernel norm is the norm of the actual physical insertion profile. -/
theorem realization_kernelNorm (h : bezout.History N) (x y : ℝ) :
    h.realization.kernelNorm N x y = Real.sqrt (Lower.physicalKernelSq h x y) := by
  simp only [chebyshev1.Realization.kernelNorm, Finset.sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [h.realization_kernel]
  rfl

/-- Every physical spectral pair is bounded by the full spectral gain. -/
theorem physical_kernelNorm_le_gain (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) {x y : ℝ}
    (hx : x ∈ Set.Icc I.mu I.L) (hy : y ∈ Set.Icc I.mu I.L) :
    Real.sqrt (Lower.physicalKernelSq h x y) ≤ h.spectralGain I := by
  rw [← h.realization_kernelNorm]
  exact h.realization.kernelNorm_le_gain I N hx hy

/-- A maximizing pair exists for the physical history kernel. -/
theorem spectralGain_attained (h : bezout.History N) (I : chebyshev1.SpectralInterval) :
    ∃ x ∈ Set.Icc I.mu I.L, ∃ y ∈ Set.Icc I.mu I.L,
      Real.sqrt (Lower.physicalKernelSq h x y) = h.spectralGain I := by
  obtain ⟨x, hx, y, hy, he⟩ := h.realization.gain_attained I N
  exact ⟨x, hx, y, hy, (h.realization_kernelNorm x y).symm.trans he⟩

/-- A product of uniform response and query bounds controls the whole kernel. -/
theorem spectralGain_le_product_energy (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (P Q : Fin N → ℝ)
    (hP : bezout.Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s) :
    h.spectralGain I ≤ bezout.Analysis.energyNorm (fun s => P s * Q s) := by
  obtain ⟨x, hx, y, hy, he⟩ := h.spectralGain_attained I
  rw [← he]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro s _
  have hb : |Lower.physicalKernel h s x y| ≤ P s * Q s := by
    rw [Lower.physicalKernel, abs_mul]
    exact mul_le_mul (hP.2 s x hx) (hq s y hy) (abs_nonneg _) (hP.1 s)
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (hP.1 s) (hQ s))).mpr hb
  simpa only [sq_abs] using hs

/-- Simultaneous endpoint attainment makes the product-energy bound exact. -/
theorem spectralGain_eq_product_energy (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (P Q : Fin N → ℝ)
    (hP : bezout.Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s)
    (hpμ : ∀ s, |(h.response s).eval I.mu| = P s)
    (hqμ : ∀ s, |(h.query s).eval I.mu| = Q s) :
    h.spectralGain I = bezout.Analysis.energyNorm (fun s => P s * Q s) := by
  apply le_antisymm (h.spectralGain_le_product_energy I P Q hP hQ hq)
  have he : Lower.physicalKernelSq h I.mu I.mu = ∑ s, (P s * Q s) ^ 2 := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← sq_abs, Lower.physicalKernel, abs_mul, hpμ, hqμ]
  have hb := h.physical_kernelNorm_le_gain I
    (x := I.mu) (y := I.mu) ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩
  simpa only [he, bezout.Analysis.energyNorm] using hb

/-- Every Chebyshev-exact causal history obeys the sharp parity-corrected spectral lower bound. -/
theorem linearGain_le_spectralGain (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N) :
    bezout.Lower.linearGain I N ≤ h.spectralGain I :=
  bezout.Lower.uniform_spectral_bound_ge_linearGain h I he hN _
    (fun _ hx _ hy => h.physical_kernelNorm_le_gain I hx hy)

/-- The spectral coefficient is a sharp dimension-uniform Hilbert--Schmidt
bound for the corresponding actual realization insertion operator. -/
theorem hs_gain_minimal (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ H : Matrix (Fin 2) (Fin 2) ℝ, H.IsHermitian →
      spectrum ℝ H ⊆ Set.Icc I.mu I.L → ∀ D : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
        chebyshev1.hsNorm (h.realization.linearResponse N H D) ≤
          C * Real.sqrt (∑ s ∈ Finset.range N, chebyshev1.hsNorm (D s) ^ 2)) :
    h.spectralGain I ≤ C := h.realization.hs_constant_minimal I N C hC hb

end
end bezout.History
