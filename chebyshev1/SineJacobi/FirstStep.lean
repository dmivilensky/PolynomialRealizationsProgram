import chebyshev1.Jacobi.EndpointProfile
import chebyshev1.Jacobi.TerminalSpectrum
import chebyshev1.SineJacobi.Resolvent
import chebyshev1.Spectral.Resolvent
import chebyshev1.SineJacobi.SpectralMeasure
import chebyshev1.Prefix.Kernel

/-! Exact first-step transmission and the first Green diagonal as a spectral sum. -/
namespace chebyshev1
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators Matrix

namespace JacobiData

/-- At the first query there has been no evolution in the input spectral mode. -/
theorem kernel_zero_input_independent (J : JacobiData) (I : SpectralInterval)
    {N : ℕ} (h : J.Admissible I N) (hN : 0 < N) (lam nu₁ nu₂ : ℝ) :
    (J.realization I).kernel N 0 lam nu₁ = (J.realization I).kernel N 0 lam nu₂ := by
  rw [J.kernel_eq I h 0 hN, J.kernel_eq I h 0 hN]
  simp only [leading, block, eval_one]

theorem kernel_zero_endpoint_profile (J : JacobiData) (I : SpectralInterval)
    {N : ℕ} (h : J.Admissible I N) (hN : 0 < N)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c * T ℝ N) (nu : ℝ) :
    (J.realization I).kernel N 0 I.mu nu =
      -(2 * I.epsilon N / I.delta) * J.endpointProfile N 0 := by
  rw [J.kernel_zero_input_independent I h hN I.mu nu I.mu]
  exact J.kernel_endpoint_profile I h hc ht 0 hN

/-- First-step transmission for terminally exact Jacobi data, with positivity
of the normalizing denominators supplied by the terminal polynomial. -/
theorem first_step_transmission_of_terminal (J : JacobiData) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (hsq : ∀ t, 0 ≤ J.aSq t)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c * T ℝ N) (nu : ℝ) :
    (J.realization I).kernel N 0 I.mu nu =
      -(2 * I.epsilon N / I.delta) * J.endpointProfile N 0 :=
  J.kernel_zero_endpoint_profile I (J.admissible_of_terminal I hsq hc ht) hN hc ht nu

end JacobiData

namespace SineJacobi

theorem kernel_zero_greenWeight (I : SpectralInterval) (N : ℕ) (hN : 0 < N) (nu : ℝ) :
    ((data N).realization I).kernel N 0 I.mu nu =
      -(2 * I.epsilon N / I.delta) * greenWeight N 0 := by
  rw [(data N).kernel_zero_input_independent I (admissible I N hN) hN I.mu nu I.mu]
  exact kernel_endpoint I N 0 hN

theorem first_green_spectral_sum (N : ℕ) (hN : 0 < N) :
    greenWeight N 0 = ∑ j : Fin N, sineWeight N j / (1 - node N j) := by
  have hx : ∀ j, (1 : ℝ) - (basis N).eigenvalues j ≠ 0 := by
    intro j
    obtain ⟨k, hk⟩ := basis_eigenvalue_is_node N hN j
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0)
      (y := nodeAngle N k) le_rfl (nodeAngle_mem N k).2.le (nodeAngle_mem N k).1
    have he : node N k < 1 := by simpa [node] using hc
    rw [← hk]
    linarith
  have hr := (basis N).resolvent_diagonal_sum 1 hx (⟨0, hN⟩ : Fin N)
  have hs : Matrix.scalar (Fin N) (1 : ℝ) = 1 := by simp [Matrix.scalar]
  rw [hs, resolvent_diagonal] at hr
  rw [show (⟨0, hN⟩ : Fin N).val = 0 by rfl] at hr
  rw [hr, ← (nodeIndex N hN).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [spectral_weight N hN j, eigenvalue_nodeIndex]

end SineJacobi
end
end chebyshev1
