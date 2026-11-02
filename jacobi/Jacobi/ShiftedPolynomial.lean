import jacobi.Jacobi.CoefficientEquation
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Article: jacobi, Theorem 5.1.
The same actual Jacobi family is expressed in the coordinate t=(1-x)/2.
Its real polynomial obeys the full Sturm--Liouville polynomial equation.
Source: the hypergeometric Jacobi equation, DLMF 18.8.1 and 18.5.7.
Use: the real Sturm equation and weighted orthogonality apply directly on the fixed interval [0,1].
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Complex Set
open scoped Nat
set_option backward.isDefEq.respectTransparency false

/-- The actual real normalized Jacobi polynomial in the shifted coordinate t=(1-x)/2.
Use: the real Sturm equation and weighted orthogonality apply directly on the fixed interval [0,1].
Article: jacobi, Theorem 5.1.
-/
def shiftedPolynomial (a b : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k∈Finset.range (n+1),C (coefficient (a:ℂ) (b:ℂ) n k).re*X^k

/-- Every coefficient of the shifted real polynomial is the real part of the original hypergeometric coefficient.
Use: the genuine coefficient recurrence proves the actual polynomial equation at every degree.
Article: jacobi, Proposition A.1.
Proof: coefficient extraction selects the single matching finite term;
outside the degree range the original coefficient vanishes by termination. -/
theorem shiftedPolynomial_coeff (a b : ℝ) (n k : ℕ) :
    (shiftedPolynomial a b n).coeff k=(coefficient (a:ℂ) (b:ℂ) n k).re := by
  -- Beyond the finite polynomial degree the original terminating coefficient vanishes as well.
  classical
  simp only [shiftedPolynomial,finsetSum_coeff,coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · have hn : n<k := by
      have hh : n+1≤k := by simpa only [Finset.mem_range,not_lt] using hk
      omega
    rw [coefficient_terminates _ _ hn,Complex.zero_re]

/-- The shifted polynomial evaluates to the original normalized Jacobi function at the exact affine coordinate.
Use: every Sturm statement about the real shifted polynomial is a statement about the actual source polynomial.
Article: jacobi, Theorem 5.1.
Proof: evaluate the genuine finite polynomial and compare it with the
proved terminating expansion at x=1-2*t. Taking real parts preserves the finite sum. -/
theorem shiftedPolynomial_eval (a b t : ℝ) (n : ℕ) :
    (shiftedPolynomial a b n).eval t=realNormalized a b n (1-2*t) := by
  -- Both sides use the original coefficients; the real coordinate is the only substitution.
  rw [realNormalized,normalized_eq_sum]
  simp only [shiftedPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  have he : (1-((1-2*t:ℝ):ℂ))/2=(t:ℂ) := by push_cast; ring
  rw [he]
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,mul_zero,sub_zero]

/-- The Euler derivative X*p' has coefficient k*p_k.
Use: computes the Jacobi differential operator coefficients without truncated-index boundary cases.
Article: jacobi, Theorem 5.1.
Proof: at zero the X factor kills the coefficient; at a successor use the actual polynomial derivative coefficient theorem. -/
theorem euler_coeff (p : Polynomial ℝ) (k : ℕ) :
    (X*p.derivative).coeff k=(k:ℝ)*p.coeff k := by
  cases k with
  | zero => simp
  | succ k => rw [coeff_X_mul,coeff_derivative]; push_cast; ring

/-- The second Euler term X^2*p'' has coefficient k*(k-1)*p_k, with real subtraction even at k=0.
Use: computes every coefficient of the genuine Jacobi differential equation uniformly.
Article: jacobi, Theorem 5.1.
Proof: differentiate X*p' and multiply by X. The product rule expresses
the result as X*p'+X^2*p''; apply the first Euler coefficient identity twice. -/
theorem second_euler_coeff (p : Polynomial ℝ) (k : ℕ) :
    (X*(X*p.derivative.derivative)).coeff k=(k:ℝ)*(k-1)*p.coeff k := by
  -- This product-rule identity includes the two boundary coefficient degrees automatically.
  have he : X*(X*p.derivative).derivative=X*p.derivative+X*(X*p.derivative.derivative) := by
    rw [derivative_mul,derivative_X,one_mul]
    ring
  have h := congrArg (fun q : Polynomial ℝ => q.coeff k) he
  rw [euler_coeff,euler_coeff,coeff_add,euler_coeff] at h
  linarith

/-- The actual shifted real Jacobi polynomial satisfies its exact polynomial differential equation.
Use: supplies the Sturm operator, weighted Green identity, orthogonality and complete finite zero location.
Article: jacobi, Theorem 5.1.
Proof: extract each actual polynomial coefficient. The two Euler
identities handle the X and X^2 derivative terms, and the proved real
hypergeometric coefficient recurrence cancels the entire residual. -/
theorem shiftedPolynomial_equation {a b : ℝ} (ha : -1<a) (n : ℕ) :
    let q := shiftedPolynomial a b n
    X*q.derivative.derivative-X*(X*q.derivative.derivative)+C (a+1)*q.derivative-
      C (a+b+2)*(X*q.derivative)+C ((n:ℝ)*(n+a+b+1))*q=0 := by
  -- The equation is proved for the original finite polynomial, rather than for an abstract ODE solution.
  dsimp only
  ext k
  simp only [coeff_add,coeff_sub,coeff_C_mul,coeff_zero,euler_coeff,second_euler_coeff,
    coeff_derivative,shiftedPolynomial_coeff]
  linear_combination real_coefficient_equation (b := b) ha n k

end
end jacobi.Jacobi
