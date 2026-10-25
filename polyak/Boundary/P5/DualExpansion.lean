import polyak.Boundary.P5.DualReal

/-!
Article: exact coefficient expansion of the central dual numerator.
Use: continuous residual quadratic coefficients are extracted from the true sextic.
-/
noncomputable section
namespace polyak.Boundary.P5
open Polynomial

/-- Article: the six scalar parameters of the central dual numerator. -/
def dualGeneric (g u d a b e : ℝ) : ℝ[X] := by
  let c : ℝ[X] := Polynomial.X
  let G := Polynomial.C g
  let U := Polynomial.C u
  exact -(1-c^2-U^2)*(C d+C a*(2*(G+c))+C b*(4*(G^2+G*c+c^2)-3)+
      C e*(16*(G^4+G^3*c+G^2*c^2+G*c^3+c^4)-20*(G^2+G*c+c^2)+5))+
    2*U*(1-c^2)*(C a*2+C b*(4*(G+c))+
      C e*(16*(G^3+G^2*c+G*c^2+c^3)-12*(G+c)))

/-- Article: exact coefficient of degree 0. -/
def genericCoefficient0 (g u d a b e : ℝ) : ℝ := 2*a*g*u^2 - 2*a*g + 4*a*u + 4*b*g^2*u^2 - 4*b*g^2 + 8*b*g*u - 3*b*u^2 + 3*b + d*u^2 - d + 16*e*g^4*u^2 - 16*e*g^4 + 32*e*g^3*u - 20*e*g^2*u^2 + 20*e*g^2 - 24*e*g*u + 5*e*u^2 - 5*e

/-- Article: exact coefficient of degree 1. -/
def genericCoefficient1 (g u _d a b e : ℝ) : ℝ := 2*(a*u^2 - a + 2*b*g*u^2 - 2*b*g + 4*b*u + 8*e*g^3*u^2 - 8*e*g^3 + 16*e*g^2*u - 10*e*g*u^2 + 10*e*g - 12*e*u)

/-- Article: exact coefficient of degree 2. -/
def genericCoefficient2 (g u d a b e : ℝ) : ℝ := 2*a*g - 4*a*u + 4*b*g^2 - 8*b*g*u + 4*b*u^2 - 7*b + d + 16*e*g^4 - 32*e*g^3*u + 16*e*g^2*u^2 - 36*e*g^2 + 56*e*g*u - 20*e*u^2 + 25*e

/-- Article: exact coefficient of degree 3. -/
def genericCoefficient3 (g u _d a b e : ℝ) : ℝ := 2*(a + 2*b*g - 4*b*u + 8*e*g^3 - 16*e*g^2*u + 8*e*g*u^2 - 18*e*g + 28*e*u)

/-- Article: exact coefficient of degree 4. -/
def genericCoefficient4 (g u _d _a b e : ℝ) : ℝ := 4*(b + 4*e*g^2 - 8*e*g*u + 4*e*u^2 - 9*e)

/-- Article: exact coefficient of degree 5. -/
def genericCoefficient5 (g u _d _a _b e : ℝ) : ℝ := -16*e*(-g + 2*u)

/-- Article: exact coefficient of degree 6. -/
def genericCoefficient6 (_g _u _d _a _b e : ℝ) : ℝ := 16*e

/-- Article: the actual sextic written by its seven true real coefficients. -/
theorem dualGeneric_expansion (g u d a b e : ℝ) :
    dualGeneric g u d a b e=
      C (genericCoefficient0 g u d a b e)+
      C (genericCoefficient1 g u d a b e)*Polynomial.X^1+
      C (genericCoefficient2 g u d a b e)*Polynomial.X^2+
      C (genericCoefficient3 g u d a b e)*Polynomial.X^3+
      C (genericCoefficient4 g u d a b e)*Polynomial.X^4+
      C (genericCoefficient5 g u d a b e)*Polynomial.X^5+
      C (genericCoefficient6 g u d a b e)*Polynomial.X^6 := by
  simp only [dualGeneric,genericCoefficient0,genericCoefficient1,genericCoefficient2,genericCoefficient3,genericCoefficient4,genericCoefficient5,genericCoefficient6,map_add,map_sub,map_mul,map_pow,map_neg,map_ofNat]
  ring

/-- Article: no central dual numerator has degree above six. -/
theorem dualGeneric_natDegree (g u d a b e : ℝ) :
    (dualGeneric g u d a b e).natDegree≤6 := by
  rw [dualGeneric_expansion]
  compute_degree!

/-- Article: coefficient extraction from the independently expanded sextic. -/
theorem dualGeneric_coeff4 (g u d a b e : ℝ) :
    (dualGeneric g u d a b e).coeff 4=genericCoefficient4 g u d a b e := by
  rw [dualGeneric_expansion]
  simp

/-- Article: coefficient extraction from the independently expanded sextic. -/
theorem dualGeneric_coeff5 (g u d a b e : ℝ) :
    (dualGeneric g u d a b e).coeff 5=genericCoefficient5 g u d a b e := by
  rw [dualGeneric_expansion]
  simp

/-- Article: coefficient extraction from the independently expanded sextic. -/
theorem dualGeneric_coeff6 (g u d a b e : ℝ) :
    (dualGeneric g u d a b e).coeff 6=genericCoefficient6 g u d a b e := by
  rw [dualGeneric_expansion]
  simp

end polyak.Boundary.P5
