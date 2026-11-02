import jacobi.Jacobi.EquationUniqueness
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
Article: jacobi, Theorem 5.1.
The community Chebyshev differential equation and the already proved
Jacobi polynomial uniqueness identify the original half-integer Jacobi
family with U_n, including its actual endpoint normalization.
Source: DLMF 18.3.1 and the community Chebyshev differential equation.
Use: shiftedPolynomial_half_sine identifies the literal classical U_n polynomial with the already verified Jacobi family.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The original Chebyshev polynomial U_n in the shifted coordinate solves the actual half-integer Jacobi equation.
Use: shiftedPolynomial_half_sine identifies the literal classical U_n polynomial with the already verified Jacobi family.
Article: jacobi, Theorem 5.1.
Source: the community Chebyshev U differential equation.
Proof: compose the genuine Chebyshev equation with x=1-2*t.
The two actual polynomial chain rules give derivative factors -2
and four, which are exactly the original shifted Jacobi equation. -/
theorem chebyshev_U_shifted_residual (n:ℕ) :
    equationResidual (1/2) (1/2) n ((U ℝ (n:ℤ)).comp (1-C 2*X))=0 := by
  -- The original polynomial, not only its real zeros, satisfies the actual equation.
  apply Polynomial.funext
  intro t
  rw [equationResidual_eval]
  simp only [derivative_comp,derivative_mul,derivative_sub,derivative_one,derivative_C,
    derivative_X,zero_mul,mul_one,zero_sub,zero_add,derivative_neg,
    eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_one,eval_zero,eval_neg,eval_comp]
  have h:=congrArg (fun p:Polynomial ℝ=>p.eval (1-2*t))
    (one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (R:=ℝ) (n:ℤ))
  simp only [Function.iterate_succ,Function.iterate_zero,Function.comp_apply,id_eq,
    eval_mul,eval_sub,eval_one,eval_pow,eval_X,eval_add,eval_ofNat,eval_natCast,Int.cast_natCast] at h
  linear_combination h

/-- The original normalized half-integer Jacobi polynomial is exactly U_n/(n+1) in its literal shifted coordinate.
Use: the U counterexample fibre and its true optimal-energy limit are the already verified genuine Jacobi fibre, with no polynomial-identification assumption.
Article: jacobi, Proposition 6.1.
Proof: both actual polynomials solve the same shifted Jacobi
equation. Their values at zero are one because U_n(1)=n+1.
The independently proved genuine polynomial uniqueness identifies them. -/
theorem shiftedPolynomial_half_sine (n:ℕ) :
    shiftedPolynomial (1/2) (1/2) n=
      C (1/((n:ℝ)+1))*(U ℝ (n:ℤ)).comp (1-C 2*X) := by
  -- The endpoint value fixes the full original normalization before the finite fibres are compared.
  apply equation_unique (by norm_num : (-1:ℝ)<1/2) n
    _ _ (shiftedPolynomial_residual (by norm_num) n)
  · rw [equationResidual_const_mul,chebyshev_U_shifted_residual,mul_zero]
  · simp only [shiftedPolynomial_zero,eval_mul,eval_C,eval_comp,eval_sub,eval_one,eval_X,
      mul_zero,sub_zero,U_eval_one,Int.cast_natCast]
    field_simp

end
end jacobi.Jacobi
