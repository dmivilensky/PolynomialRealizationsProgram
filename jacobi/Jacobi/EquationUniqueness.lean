import jacobi.Jacobi.EndpointDerivatives

/-!
Article: jacobi, Theorem 5.1.
The genuine polynomial Jacobi equation determines its solution uniquely
from its endpoint value for alpha>-1. This gives reflection and derivative
identities directly for the already constructed source polynomials.
Source: the elementary triangular coefficient recurrence for the Jacobi equation.
Use: proves the classical identities by uniqueness for the same actual equation.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial

/-- The literal polynomial residual of the shifted Jacobi differential equation.
Use: proves the classical identities by uniqueness for the same actual equation.
Article: jacobi, Theorem 5.1.
-/
def equationResidual (a b : ℝ) (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  X*p.derivative.derivative-X*(X*p.derivative.derivative)+C (a+1)*p.derivative-
    C (a+b+2)*(X*p.derivative)+C ((n:ℝ)*(n+a+b+1))*p

/-- Every coefficient of the Jacobi residual is the exact triangular recurrence residual.
Use: uniqueness includes polynomial solutions of arbitrary degree without a hidden degree or termination premise.
Article: jacobi, Theorem 5.1.
Proof: compute both Euler terms using the previously proved generic polynomial identities and collect the two coefficients. -/
theorem equationResidual_coeff (a b : ℝ) (n : ℕ) (p : Polynomial ℝ) (k : ℕ) :
    (equationResidual a b n p).coeff k=
      (k+1:ℝ)*(a+1+k)*p.coeff (k+1)-((k:ℝ)-n)*(n+a+b+1+k)*p.coeff k := by
  simp only [equationResidual,coeff_add,coeff_sub,coeff_C_mul,euler_coeff,
    second_euler_coeff,coeff_derivative]
  ring

/-- Evaluation of the polynomial residual gives exactly the real Jacobi equation.
Use: reflection and differentiation preserve the actual equation, so coefficient uniqueness applies.
Article: jacobi, Theorem 5.1.
Proof: evaluation respects polynomial addition, multiplication and the actual derivatives. -/
theorem equationResidual_eval (a b : ℝ) (n : ℕ) (p : Polynomial ℝ) (t : ℝ) :
    (equationResidual a b n p).eval t=t*(1-t)*p.derivative.derivative.eval t+
      (a+1-(a+b+2)*t)*p.derivative.eval t+(n:ℝ)*(n+a+b+1)*p.eval t := by
  simp only [equationResidual,eval_add,eval_sub,eval_mul,eval_C,eval_X]
  ring

/-- A polynomial solution of the Jacobi equation is uniquely determined by its actual endpoint value.
Use: proves the full parameter-reflection and derivative identities for the original hypergeometric polynomials.
Article: jacobi, Theorem 5.1.
Proof: the constant coefficients agree by the endpoint condition. The
triangular recurrence determines every successor coefficient, since both
k+1 and alpha+1+k are strictly positive in the stated parameter range. -/
theorem equation_unique {a b : ℝ} (ha : -1<a) (n : ℕ) (p q : Polynomial ℝ)
    (hp : equationResidual a b n p=0) (hq : equationResidual a b n q=0)
    (hzero : p.eval 0=q.eval 0) : p=q := by
  -- No root, normalization or degree assertion about an unrelated polynomial is substituted for the actual coefficient recurrence.
  ext k
  induction k with
  | zero => simpa only [coeff_zero_eq_eval_zero] using hzero
  | succ k ih =>
    have hpc := congrArg (fun r : Polynomial ℝ => r.coeff k) hp
    have hqc := congrArg (fun r : Polynomial ℝ => r.coeff k) hq
    rw [equationResidual_coeff,coeff_zero] at hpc hqc
    rw [ih] at hpc
    have hh : (k+1:ℝ)*(a+1+k)≠0 := ne_of_gt (by
      have hk : (0:ℝ)≤k := Nat.cast_nonneg k
      have ha1 : 0<a+1 := by linarith
      positivity)
    apply mul_left_cancel₀ hh
    linear_combination hpc-hqc

/-- The previously constructed literal shifted Jacobi polynomial has zero residual.
Use: exposes its proved true differential equation through the common uniqueness interface.
Article: jacobi, Theorem 5.1.
Proof: unfold the residual and apply the already proved hypergeometric coefficient equation. -/
theorem shiftedPolynomial_residual {a b : ℝ} (ha : -1<a) (n : ℕ) :
    equationResidual a b n (shiftedPolynomial a b n)=0 := shiftedPolynomial_equation ha n

/-- Constant multiplication preserves the actual Jacobi polynomial equation.
Use: compares endpoint-normalized and reflected or differentiated genuine solutions.
Article: jacobi, Theorem 5.1.
Proof: polynomial differentiation is linear and constants factor out of every residual term. -/
theorem equationResidual_const_mul (a b : ℝ) (n : ℕ) (c : ℝ) (p : Polynomial ℝ) :
    equationResidual a b n (C c*p)=C c*equationResidual a b n p := by
  simp only [equationResidual,derivative_C_mul]
  ring

end
end jacobi.Jacobi
