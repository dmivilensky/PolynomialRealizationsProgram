import krylov.LinearAlgebra.SpectralContinuation
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual real continuation factorization.
Use: prove that every genuine continuation zero is real by splitting the actual positive spectral product over the original real field.
Source: true positive reciprocal spectral factors and the standard finite linear-factor splitting criterion.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine positive spectral continuation splits completely over the real field.
Use: The genuine positive spectral continuation splits completely over the real field.
Article: main_krylov, prop:phi(a), actual real continuation factorization.
Proof: Factor each true reciprocal term into an actual real nonzero constant and its genuine monic real eigenvalue factor. -/
theorem spectralContinuation_splits (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    (spectralContinuation S hS).Splits := by
  -- Every actual reciprocal factor has its genuine positive eigenvalue as a real root.
  apply Polynomial.Splits.prod
  intro i _
  have he : (1-C ((hS.1.eigenvalues i)⁻¹)*X : ℝ[X])=
      C (-(hS.1.eigenvalues i)⁻¹)*(X-C (hS.1.eigenvalues i)) := by
    simp only [mul_sub,← C_mul,neg_mul,inv_mul_cancel₀ (hS.eigenvalues_pos i).ne',
      C_neg,C_1,sub_neg_eq_add]
    ring
  rw [he]
  exact (Polynomial.Splits.C _).mul (Polynomial.Splits.X_sub_C _)
end
end krylov.LinearAlgebra
