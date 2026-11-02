import jacobi.Oscillation.PhaseZeros

/-!
Article: jacobi, Proposition B.1.
An explicit modified ordinary phase has an absolutely integrable fourth-order
ordinary derivative. At every genuine zero its sine correction vanishes.
This exact near-conservation identity gives the cubic remainder directly,
without assuming a Bessel second solution or large-argument amplitude expansion.
Source: the classical asymptotic-integration method for the inverse-square restoring equation.
Use: its fourth-order derivative and exact zero values give McMahon's cubic zero remainder.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The explicit corrected phase for the actual inverse-square ordinary Pruefer equation.
Use: its fourth-order derivative and exact zero values give McMahon's cubic zero remainder.
Article: jacobi, Proposition B.1.
-/
def phaseInvariant (c : ℝ) (theta : ℝ → ℝ) (x : ℝ) : ℝ :=
  theta x-x+c/(2*x)+c*sin (2*theta x)/(4*x^2)-c*cos (2*theta x)/(4*x^3)

/-- The literal fourth-order remainder in the corrected actual phase derivative.
Use: its integrable uniform bound controls the genuine cubic McMahon remainder at the original zeros.
Article: jacobi, Proposition B.1.
-/
def phaseInvariantSlope (c : ℝ) (theta : ℝ → ℝ) (x : ℝ) : ℝ :=
  c^2*cos (2*theta x)*sin (theta x)^2/(2*x^4)+
    c^2*sin (2*theta x)*sin (theta x)^2/(2*x^5)+3*c*cos (2*theta x)/(4*x^4)

/-- The explicit corrected phase has precisely its genuine fourth-order ordinary derivative for the actual inverse-square phase equation.
Use: proves the cubic McMahon error from first derivatives of the actual constructed phase, without an asymptotic phase certificate.
Article: jacobi, Proposition B.1.
Proof: differentiate the literal phase corrections and substitute the
original actual phase derivative. The double-angle cosine identity cancels
all second- and third-order terms, leaving exactly the displayed fourth-
and fifth-order remainder. -/
theorem phaseInvariant_hasDerivAt {theta : ℝ → ℝ} {c x : ℝ} (hx : 0<x)
    (ht : HasDerivAt theta (1+c/x^2*sin (theta x)^2) x) :
    HasDerivAt (phaseInvariant c theta) (phaseInvariantSlope c theta x) x := by
  -- This is an exact identity for the actual phase, including the oscillatory correction that vanishes at its original zero levels.
  have hi := hasDerivAt_id x
  have h1 := (hasDerivAt_const x c).div (hi.const_mul 2) (by positivity : 2*x≠0)
  have h2 := ((ht.const_mul 2).sin.const_mul c).div ((hi.pow 2).const_mul 4) (by positivity : 4*x^2≠0)
  have h3 := ((ht.const_mul 2).cos.const_mul c).div ((hi.pow 3).const_mul 4) (by positivity : 4*x^3≠0)
  convert (((ht.sub hi).add h1).add h2).sub h3 using 1
  · rfl
  · dsimp only [phaseInvariantSlope]
    norm_num only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,zero_mul,zero_sub]
    simp only [Real.cos_two_mul_eq_one_sub]
    field_simp [hx.ne']
    ring

end
end jacobi.Oscillation
