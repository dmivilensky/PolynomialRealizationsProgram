import chebyshev1.Background.StepsizeClassification
import chebyshev1.Realization.UniversalGain

/-! The complete endpoint profile of an exact stepsize schedule consists of
the reciprocal Chebyshev gaps, in precisely its chosen temporal order. -/
namespace chebyshev1.Stepsize
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Remove one factor of the stepsize residual without division. -/
theorem kernel_diagonal_mul_factor (gamma : ℕ → ℝ) (N s : ℕ) (hs : s < N) (lam : ℝ) :
    (realization gamma).kernel N s lam lam*(1-gamma s*lam) =
      -gamma s*(polynomial gamma N).eval lam := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases he : s=N
    · subst s
      rw [kernel_last,polynomial,eval_mul,eval_sub,eval_one,eval_mul,eval_C,eval_X]
      ring
    · rw [kernel_extend gamma N s (by omega),mul_assoc,ih (by omega),
        polynomial,eval_mul,eval_sub,eval_one,eval_mul,eval_C,eval_X]
      ring

theorem signedEndpointProfile_eq_reciprocal_gap (gamma : ℕ → ℝ) (I : SpectralInterval)
    (N : ℕ) (hexact : FinalExact gamma I N) (s j : Fin N)
    (hgamma : gamma s.val=1/chebyshevRoot I N j) :
    (realization gamma).signedEndpointProfile I N s.val =
      1/(1-JacobiData.chebyshevNode N j) := by
  have heps : I.epsilon N ≠ 0 := (one_div_pos.mpr (I.den_pos N)).ne'
  have hroot : chebyshevRoot I N j ≠ 0 := chebyshevRoot_ne_zero I N j
  have hgap : 1-JacobiData.chebyshevNode N j ≠ 0 := by
    intro hz
    have he : JacobiData.chebyshevNode N j=1 := by linarith
    have ht := JacobiData.monicChebyshev_node N j
    rw [he,JacobiData.monicChebyshev,eval_mul,eval_C,T_eval_one,mul_one] at ht
    exact (inv_ne_zero (pow_ne_zero _ (by norm_num : (2:ℝ)≠0))) ht
  have hp := kernel_diagonal_mul_factor gamma N s.val s.isLt I.mu
  rw [final_polynomial_eq gamma I N hexact,I.residual_eval_mu,hgamma] at hp
  have hd : chebyshevRoot I N j-I.mu =
      I.delta/2*(1-JacobiData.chebyshevNode N j) := by
    unfold chebyshevRoot SpectralInterval.lambda SpectralInterval.delta
    ring
  have hp' : (realization gamma).kernel N s.val I.mu I.mu*(chebyshevRoot I N j-I.mu) =
      -I.epsilon N := by
    calc
      _ = ((realization gamma).kernel N s.val I.mu I.mu*
          (1-1/chebyshevRoot I N j*I.mu))*chebyshevRoot I N j := by
        field_simp [hroot]
      _ = (-1/chebyshevRoot I N j*I.epsilon N)*chebyshevRoot I N j := by rw [hp]; ring
      _ = _ := by field_simp [hroot]
  rw [hd] at hp'
  apply (eq_div_iff hgap).mpr
  unfold Realization.signedEndpointProfile
  field_simp [heps]
  nlinarith [hp']

/-- The whole profile is a permutation of the eigenvalues of the terminal
Chebyshev Green matrix. No order or positivity premise is supplied. -/
theorem signedEndpointProfile_eq_permutation (gamma : ℕ → ℝ) (I : SpectralInterval)
    (N : ℕ) (hexact : FinalExact gamma I N) :
    ∃ σ : Equiv.Perm (Fin N), ∀ s : Fin N,
      (realization gamma).signedEndpointProfile I N s.val =
        1/(1-JacobiData.chebyshevNode N (σ s)) := by
  obtain ⟨σ,hσ⟩ := (finalExact_iff_permutation gamma I N).mp hexact
  exact ⟨σ,fun s => signedEndpointProfile_eq_reciprocal_gap gamma I N hexact s (σ s) (hσ s)⟩

end
end chebyshev1.Stepsize
