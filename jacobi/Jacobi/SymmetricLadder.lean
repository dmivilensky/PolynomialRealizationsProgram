import jacobi.Jacobi.EquationUniqueness

/-!
Article: jacobi, Proposition A.1.
The existing true Jacobi differential equation supplies exact raising
and lowering identities for the same normalized symmetric polynomials.
Use: SymmetricRecurrence identifies the original Nesterov recurrence with
its Gegenbauer residual without importing a special-function identity.
Source: classical Jacobi ladder identities, proved here by polynomial ODE uniqueness.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The symmetric original Jacobi equation has its standard divergence-compatible polynomial form.
Use: symmetric_raise_residual and symmetric_lower_residual perform the exact ladder algebra on the original equation.
Article: jacobi, Proposition A.1.
Proof: expand the same literal polynomial residual and collect its symmetric real coefficients. -/
theorem symmetric_residual_eq (a:ℝ) (n:ℕ) (p:Polynomial ℝ) :
    equationResidual a a n p=X*(1-X)*p.derivative.derivative+
      C (a+1)*(1-2*X)*p.derivative+C ((n:ℝ)*(n+2*a+1))*p := by
  unfold equationResidual
  simp only [map_add,map_mul,map_one,map_ofNat]
  ring

/-- The exact symmetric Jacobi raising polynomial, retaining the source normalization.
Use: symmetric_raise_eq identifies it with the actual next original Jacobi polynomial.
Article: jacobi, Proposition A.1.
-/
def symmetricRaise (a:ℝ) (n:ℕ) (p:Polynomial ℝ) : Polynomial ℝ :=
  C ((n:ℝ)+2*a+1)*(1-2*X)*p+2*X*(1-X)*p.derivative

/-- The exact symmetric Jacobi lowering polynomial at positive degree n+1.
Use: symmetric_lower_eq identifies it with the actual preceding original Jacobi polynomial.
Article: jacobi, Proposition A.1.
-/
def symmetricLower (n:ℕ) (p:Polynomial ℝ) : Polynomial ℝ :=
  C ((n:ℝ)+1)*(1-2*X)*p-2*X*(1-X)*p.derivative

/-- The genuine raising polynomial solves the next original Jacobi equation whenever its input solves the original equation.
Use: symmetric_raise_eq applies the existing all-degree coefficient uniqueness theorem to the actual source polynomials.
Article: jacobi, Proposition A.1.
Proof: differentiate the original polynomial equation. The next residual is exactly twice X*(1-X) times that derivative plus the old residual times (n+2*alpha+3)*(1-2*X). Both terms vanish. -/
theorem symmetric_raise_residual (a:ℝ) (n:ℕ) (p:Polynomial ℝ)
    (hp:equationResidual a a n p=0) :
    equationResidual a a (n+1) (symmetricRaise a n p)=0 := by
  -- This exact intertwining calculation differentiates the already proved original polynomial equation.
  rw [symmetric_residual_eq] at hp
  have hd:=congrArg Polynomial.derivative hp
  rw [symmetric_residual_eq]
  simp only [symmetricRaise,derivative_add,derivative_sub,derivative_mul,derivative_C,
    derivative_one,derivative_ofNat,derivative_X,zero_add,add_zero,zero_mul,mul_zero,
    one_mul,mul_one,sub_zero,derivative_zero] at hd ⊢
  push_cast
  linear_combination (norm := (simp only [map_add,map_mul,map_one,map_ofNat]; ring))
    (2*X*(1-X))*hd+C ((n:ℝ)+2*a+3)*(1-2*X)*hp

/-- The genuine lowering polynomial solves the preceding original Jacobi equation whenever its input solves the next equation.
Use: symmetric_lower_eq identifies the original normalized preceding polynomial with no degree or termination premise.
Article: jacobi, Proposition A.1.
Proof: the lower residual is minus twice X*(1-X) times the derivative of the input residual plus that residual times (n-1)*(1-2*X). The genuine input equation makes both terms zero. -/
theorem symmetric_lower_residual (a:ℝ) (n:ℕ) (p:Polynomial ℝ)
    (hp:equationResidual a a (n+1) p=0) :
    equationResidual a a n (symmetricLower n p)=0 := by
  -- The predecessor degree is encoded as n+1 before lowering, avoiding any truncated natural subtraction.
  rw [symmetric_residual_eq] at hp
  have hd:=congrArg Polynomial.derivative hp
  rw [symmetric_residual_eq]
  simp only [symmetricLower,derivative_add,derivative_sub,derivative_mul,derivative_C,
    derivative_one,derivative_ofNat,derivative_X,zero_add,add_zero,zero_mul,mul_zero,
    one_mul,mul_one,sub_zero,derivative_zero] at hd ⊢
  push_cast at hp hd ⊢
  linear_combination (norm := (simp only [map_add,map_sub,map_mul,map_one,map_ofNat]; ring))
    (-2*X*(1-X))*hd+C ((n:ℝ)-1)*(1-2*X)*hp

end
end jacobi.Jacobi
