import jacobi.Support.Polynomials
import jacobi.Finite.AffinePolynomials

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The orthogonal polynomials of the actual corrected support spectral
measure equal the original natural family after the exact printed
affine substitution, throughout the original parameter range.
Use: the natural support Volterra and envelope estimates apply to the same corrected orthogonal family used in the target Gram matrix.
-/
namespace jacobi.Support
noncomputable section
open Polynomial jacobi.Finite

/-- The genuine corrected support polynomial is exactly the original natural polynomial after the article's affine spectral substitution.
Use: the natural support Volterra and envelope estimates apply to the same corrected orthogonal family used in the target Gram matrix.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: identify the actual corrected spectral polynomial with its genuine normalized recurrence polynomial, then apply the proved positive affine recurrence identity at the actual positive model scale. -/
theorem supportPolynomial_affine (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (i:Fin (n+1)) :
    supportPolynomial a b ha hb n i=(naturalPolynomial a b ha hb n i).comp
      (C (jacobi.Jacobi.modelScale a b (n+1))⁻¹*(X-C (jacobi.Jacobi.modelShift a b (n+1)))) := by
  rw [supportPolynomial_eq_normalized]
  exact normalizedLeading_affine _ (modelScale_pos ha hb (by omega)) _ _ (Nat.le_of_lt i.isLt)

/-- The actual corrected support polynomial has the exact printed affine evaluation at every real spectral point.
Use: Gram entries at genuine target nodes and the support edge limit use this unchanged actual spectral polynomial.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: evaluate the exact polynomial identity and simplify its literal affine inner polynomial. -/
theorem supportPolynomial_eval (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (i:Fin (n+1)) (x : ℝ) :
    (supportPolynomial a b ha hb n i).eval x=(naturalPolynomial a b ha hb n i).eval
      ((x- jacobi.Jacobi.modelShift a b (n+1))/ jacobi.Jacobi.modelScale a b (n+1)) := by
  rw [supportPolynomial_affine]
  simp only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,
    Polynomial.eval_X,div_eq_mul_inv,mul_comm]

end
end jacobi.Support
