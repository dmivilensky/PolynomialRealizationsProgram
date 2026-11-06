import chebyshev1.Jacobi.TerminalSpectrum
import chebyshev1.Spectral.Resolvent
import chebyshev1.Chebyshev.EndpointDerivatives

/-! The spectral upper bound for the squared Green diagonal. -/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The Green energy lies below the squared spectral resolvent norm. -/
theorem endpointEnergy_le_spectral (J : JacobiData) (N : ℕ)
    (hsq : ∀ t, 0 ≤ J.aSq t) (B : SpectralBasis (J.matrix 0 N))
    (hx : ∀ j, (1 : ℝ)-B.eigenvalues j ≠ 0) :
    J.endpointEnergy N ≤ ∑ j, (1/(1-B.eigenvalues j))^2 := by
  have henergy : J.endpointEnergy N =
      ∑ s : Fin N, (∑ j, B.weight s j*(1/(1-B.eigenvalues j)))^2 := by
    cases N with
    | zero => simp [endpointEnergy]
    | succ n =>
      unfold endpointEnergy
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro s _
      rw [J.endpointProfile_eq_resolvent n s hsq]
      have hr := B.resolvent_diagonal_sum 1 hx s
      simp only [map_one] at hr
      rw [hr]
      simp only [mul_one_div]
  rw [henergy]
  exact B.weighted_diagonal_energy_le _

/-- The Schur bound, with the Chebyshev spectrum evaluated exactly. -/
theorem endpointEnergy_upper_bound (J : JacobiData) {N : ℕ}
    (hsq : ∀ t, 0 ≤ J.aSq t) {c : ℝ} (hc : c ≠ 0)
    (ht : J.leading N = C c*T ℝ N) :
    J.endpointEnergy N ≤ (2*(N:ℝ)^4+(N:ℝ)^2)/3 := by
  let B := SpectralBasis.ofHermitian (J.matrix 0 N) (J.matrix_isHermitian 0 N)
  have hpoly : (J.matrix 0 N).charpoly = C c*T ℝ N := by
    rw [← J.block_eq_charpoly hsq]
    exact ht
  have hp : (J.matrix 0 N).charpoly.eval 1 ≠ 0 := by
    simpa [hpoly] using hc
  have hx : ∀ j, (1 : ℝ)-B.eigenvalues j ≠ 0 := by
    have hf := hp
    rw [B.charpoly_factor, eval_prod] at hf
    simpa using Finset.prod_ne_zero_iff.mp hf
  refine (J.endpointEnergy_le_spectral N hsq B hx).trans_eq ?_
  rw [B.reciprocal_gap_square_sum 1 hx]
  have hT : (T ℝ N).derivative.derivative.eval 1 =
      (N:ℝ)^2*((N:ℝ)^2-1)/3 := by
    have h := iterate_derivative_T_eval_one_eq_div (𝔽 := ℝ) N 2
    simpa [Finset.prod_range_succ, Function.iterate_succ_apply'] using h
  simp only [hpoly, derivative_mul, derivative_C, zero_mul, zero_add,
    eval_mul, eval_C, T_eval_one, derivative_T_eval_one, hT, mul_one]
  push_cast
  field_simp [hc]
  ring

end
end chebyshev1.JacobiData
