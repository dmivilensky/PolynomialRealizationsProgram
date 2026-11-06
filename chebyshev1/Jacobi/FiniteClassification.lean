import chebyshev1.Jacobi.FiniteConverse
import chebyshev1.Jacobi.TerminalClassification
import chebyshev1.Jacobi.TerminalSpectrum
import chebyshev2.Finite.Horizon

/-! The finite-horizon classification transports residuals, kernels and gain. -/
namespace chebyshev1.TwoTerm
noncomputable section
open Polynomial
open scoped BigOperators

theorem exists_terminal_jacobi_coordinates (S : TwoTerm) (I : SpectralInterval) {N : ℕ}
    (h : S.PositiveFixedPointUpTo N)
    (hexact : S.realization.residualPolynomial N = I.residual N) :
    ∃ J : JacobiData, (∀ s, 0 ≤ J.aSq s) ∧ J.aSq 0 = 0 ∧
      (∀ s, 0 < s → s < N → 0 < J.aSq s) ∧ J.Admissible I N ∧
      chebyshev2.Horizon.Agree N (J.method I) S ∧
      J.leading N = JacobiData.monicChebyshev N := by
  obtain ⟨J, hsq, hz, hp, ha, hc⟩ := S.exists_finite_jacobi_coordinates I h
  refine ⟨J, hsq, hz, hp, ha, hc, ?_⟩
  apply (J.terminal_residual_iff_monic I hsq ha).mp
  rw [← J.residualPolynomial_eq I ha N le_rfl]
  change (J.method I).realization.residualPolynomial N = I.residual N
  rw [chebyshev2.Horizon.residual_eq hc le_rfl, hexact]

/-- The universal gain bound is stated for every finite positive two-term method. -/
theorem finite_terminal_gain_lower (S : TwoTerm) (I : SpectralInterval) {N : ℕ}
    (h : S.PositiveFixedPointUpTo N)
    (hexact : S.realization.residualPolynomial N = I.residual N) :
    2*I.epsilon N/I.delta*Real.sqrt ((N : ℝ)^3) ≤ S.realization.gain I N := by
  obtain ⟨J, hsq, _, _, _, hc, ht⟩ := S.exists_terminal_jacobi_coordinates I h hexact
  rw [← chebyshev2.Horizon.gain_eq hc I]
  exact J.gain_lower_bound_of_terminal I hsq
    (inv_ne_zero (pow_ne_zero _ (by norm_num))) ht

/-- The reconstructed Green profile has the article's mass and the original method's kernel. -/
theorem finite_terminal_green_profile (S : TwoTerm) (I : SpectralInterval) {N : ℕ}
    (h : S.PositiveFixedPointUpTo N)
    (hexact : S.realization.residualPolynomial N = I.residual N) :
    ∃ J : JacobiData,
      (∑ s ∈ Finset.range N, J.endpointProfile N s) = (N : ℝ)^2 ∧
      (∀ s < N, ∀ x y, S.realization.kernel N s x y = (J.realization I).kernel N s x y) ∧
      S.realization.gain I N = (J.realization I).gain I N := by
  obtain ⟨J, _, _, _, ha, hc, ht⟩ := S.exists_terminal_jacobi_coordinates I h hexact
  refine ⟨J, J.endpointProfile_mass I ha
    (inv_ne_zero (pow_ne_zero _ (by norm_num))) ht, ?_, ?_⟩
  · intro s hs x y
    exact (chebyshev2.Horizon.kernel_eq hc hs x y).symm
  · exact (chebyshev2.Horizon.gain_eq hc I).symm

end
end chebyshev1.TwoTerm
