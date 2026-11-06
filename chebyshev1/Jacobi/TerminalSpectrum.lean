import chebyshev1.Jacobi.Admissibility
import chebyshev1.Jacobi.EndpointProfile
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! Terminal Chebyshev exactness supplies the Jacobi spectral and denominator hypotheses. -/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
variable (J : JacobiData)

theorem spectrum_subset_of_terminal {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c * T ℝ N) :
    spectrum ℝ (J.matrix 0 N) ⊆ Set.Icc (-1) 1 := by
  intro x hx
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, ← J.block_eq_charpoly hsq,
    ← leading, ht] at hx
  have hroot : IsRoot (T ℝ N) x := by
    simpa [IsRoot, hc] using hx
  rw [← mem_roots (T_ne_zero ℝ N), roots_T_real] at hroot
  simp only [Finset.mem_val, Finset.mem_image, Finset.mem_range] at hroot
  obtain ⟨k, _, rfl⟩ := hroot
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem admissible_of_terminal (I : SpectralInterval) {N : ℕ}
    (hsq : ∀ t, 0 ≤ J.aSq t) {c : ℝ} (hc : c ≠ 0)
    (ht : J.leading N = C c * T ℝ N) : J.Admissible I N :=
  J.admissible_of_spectrum I N hsq (J.spectrum_subset_of_terminal hsq hc ht)

/-- The universal Jacobi gain bound, with admissibility derived from terminal exactness. -/
theorem gain_lower_bound_of_terminal (I : SpectralInterval) {N : ℕ}
    (hsq : ∀ t, 0 ≤ J.aSq t) {c : ℝ} (hc : c ≠ 0)
    (ht : J.leading N = C c * T ℝ N) :
    2 * I.epsilon N / I.delta * Real.sqrt ((N : ℝ) ^ 3) ≤
      (J.realization I).gain I N :=
  J.gain_ge_sqrt_cube I (J.admissible_of_terminal I hsq hc ht) hc ht

end
end chebyshev1.JacobiData
