import jacobi.Jacobi.EquationUniqueness

/-!
Article: jacobi, Lemma C.1.
The full polynomial derivative identity follows by differentiating the actual
Jacobi equation and applying its endpoint uniqueness with shifted parameters.
Source: the classical Jacobi derivative identity, proved for the literal series.
Use: proves the full actual derivative identity without taking special-function derivative identities as premises.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial

/-- Differentiation shifts both Jacobi parameters by one and lowers the degree by one.
Use: proves the full actual derivative identity without taking special-function derivative identities as premises.
Article: jacobi, Lemma C.1.
Proof: apply the polynomial product rule to the actual residual; evaluating
at every real point reduces the exact shifted residual identity to ring algebra. -/
theorem equationResidual_derivative (a b : ℝ) (n : ℕ) (p : Polynomial ℝ) :
    (equationResidual a b (n+1) p).derivative=equationResidual (a+1) (b+1) n p.derivative := by
  apply Polynomial.funext
  intro t
  simp only [equationResidual,derivative_add,derivative_sub,derivative_mul,
    derivative_C,derivative_X,zero_mul,one_mul,zero_add,
    eval_add,eval_sub,eval_mul,eval_C,eval_X,Nat.cast_add,Nat.cast_one]
  ring

/-- The actual shifted Jacobi polynomial has its full exact polynomial derivative identity.
Use: supplies the source's classical derivative formula at all arguments, including the exact endpoint mass calculation.
Article: jacobi, Lemma C.1.
Proof: the derivative satisfies the actual shifted equation by the preceding
identity. Compare it with the genuine shifted-parameter polynomial multiplied
by the already evaluated endpoint derivative, and use endpoint uniqueness. -/
theorem shiftedPolynomial_derivative {a b : ℝ} (ha : -1<a) (n : ℕ) :
    (shiftedPolynomial a b (n+1)).derivative=
      C (-((n:ℝ)+1)*(n+a+b+2)/(a+1))*shiftedPolynomial (a+1) (b+1) n := by
  -- The shifted solution is the original finite hypergeometric polynomial, not a newly stipulated solution.
  have ha1 : -1<a+1 := by linarith
  apply equation_unique ha1 n
  · rw [← equationResidual_derivative,shiftedPolynomial_residual ha (n+1),derivative_zero]
  · rw [equationResidual_const_mul,shiftedPolynomial_residual ha1 n,mul_zero]
  · rw [eval_mul,eval_C,shiftedPolynomial_zero,mul_one,shiftedPolynomial_derivative_zero ha]
    push_cast
    ring

end
end jacobi.Jacobi
