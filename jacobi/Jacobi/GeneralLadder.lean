import jacobi.Jacobi.EquationUniqueness

/-!
Degree ladder identities for the actual endpoint-normalized Jacobi family
with independent parameters. They follow from the proved polynomial ODE
and its coefficient uniqueness, including the removable initial cases.
Use: GeneralRecurrence constructs the standard finite Jacobi matrix from
the genuine polynomials, without postulating Gauss weights or coefficients.
Source: the classical Jacobi raising and lowering identities.
Article: jacobi, Theorem 5.4, Equation (5.10).
Article role: the classical ladder identities and the actual standard recurrence.
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Divergence-compatible form of the general polynomial Jacobi equation.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem general_residual_eq (a b : ℝ) (n : ℕ) (p : ℝ[X]) :
    equationResidual a b n p=X*(1-X)*p.derivative.derivative+
      (C (a+1)-C (a+b+2)*X)*p.derivative+C ((n:ℝ)*(n+a+b+1))*p := by
  unfold equationResidual
  ring

/-- Raising in degree, with all coefficients kept polynomial in the
parameters. No division at a removable initial singularity is used.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
def generalRaise (a b : ℝ) (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C ((n:ℝ)+a+b+1)*(C ((n:ℝ)+a+1)-C (2*(n:ℝ)+a+b+2)*X)*p+
    C (2*(n:ℝ)+a+b+2)*X*(1-X)*p.derivative

/-- Lowering from degree n+1. Its endpoint factor is always positive
for b>-1, so the first row remains regular for every parameter sum.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
def generalLower (a b : ℝ) (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C ((n:ℝ)+1)*(C ((n:ℝ)+b+1)-C (2*((n:ℝ)+1)+a+b)*X)*p-
    C (2*((n:ℝ)+1)+a+b)*X*(1-X)*p.derivative

/-- Raising intertwines the two genuine Jacobi differential equations.
Differentiate the old residual once; the displayed polynomial combination
is exactly the next residual.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem general_raise_residual (a b : ℝ) (n : ℕ) (p : ℝ[X])
    (hp : equationResidual a b n p=0) :
    equationResidual a b (n+1) (generalRaise a b n p)=0 := by
  rw [general_residual_eq] at hp
  have hd := congrArg Polynomial.derivative hp
  rw [general_residual_eq]
  simp only [generalRaise,derivative_add,derivative_sub,derivative_mul,derivative_C,
    derivative_one,derivative_X,zero_add,add_zero,zero_mul,mul_zero,
    one_mul,mul_one,sub_zero,derivative_zero] at hd ⊢
  push_cast
  linear_combination (norm := (simp only [map_add,map_mul,map_one,map_ofNat]; ring))
    (C (2*(n:ℝ)+a+b+2)*X*(1-X))*hd+
      (C ((n:ℝ)+a+b+1)*(C ((n:ℝ)+a+1)-C (2*(n:ℝ)+a+b+2)*X)+
        C (2*(n:ℝ)+a+b+2)*(1-2*X))*hp

/-- Lowering intertwines the original next-degree equation with its
predecessor. The calculation includes degree one and all parameter sums.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem general_lower_residual (a b : ℝ) (n : ℕ) (p : ℝ[X])
    (hp : equationResidual a b (n+1) p=0) :
    equationResidual a b n (generalLower a b n p)=0 := by
  rw [general_residual_eq] at hp
  have hd := congrArg Polynomial.derivative hp
  rw [general_residual_eq]
  simp only [generalLower,derivative_add,derivative_sub,derivative_mul,derivative_C,
    derivative_one,derivative_X,zero_add,add_zero,zero_mul,mul_zero,
    one_mul,mul_one,sub_zero,derivative_zero] at hd ⊢
  push_cast at hp hd ⊢
  linear_combination (norm := (simp only [map_add,map_mul,map_one,map_ofNat]; ring))
    (-C (2*((n:ℝ)+1)+a+b)*X*(1-X))*hd+
      (C ((n:ℝ)+1)*(C ((n:ℝ)+b+1)-C (2*((n:ℝ)+1)+a+b)*X)-
        C (2*((n:ℝ)+1)+a+b)*(1-2*X))*hp

/-- The actual raising polynomial equals the actual next Jacobi
polynomial with its exact endpoint factor, by ODE uniqueness.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem general_raise_eq {a b : ℝ} (ha : -1<a) (n : ℕ) :
    C (((n:ℝ)+a+1)*((n:ℝ)+a+b+1))*shiftedPolynomial a b (n+1)=
      generalRaise a b n (shiftedPolynomial a b n) := by
  symm
  apply equation_unique ha (n+1)
  · exact general_raise_residual a b n _ (shiftedPolynomial_residual ha n)
  · rw [equationResidual_const_mul,shiftedPolynomial_residual ha,mul_zero]
  · simp [generalRaise,shiftedPolynomial_zero,mul_comm]

/-- The actual lowering polynomial equals the preceding Jacobi
polynomial with its nonvanishing endpoint factor.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 18.9: Jacobi differential and three-term recurrence identities.
-/
theorem general_lower_eq {a b : ℝ} (ha : -1<a) (n : ℕ) :
    C (((n:ℝ)+1)*((n:ℝ)+b+1))*shiftedPolynomial a b n=
      generalLower a b n (shiftedPolynomial a b (n+1)) := by
  symm
  apply equation_unique ha n
  · exact general_lower_residual a b n _ (shiftedPolynomial_residual ha (n+1))
  · rw [equationResidual_const_mul,shiftedPolynomial_residual ha,mul_zero]
  · simp [generalLower,shiftedPolynomial_zero]

end
end jacobi.Jacobi
