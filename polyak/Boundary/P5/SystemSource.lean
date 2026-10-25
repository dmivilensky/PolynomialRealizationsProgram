import polyak.Boundary.Optimality
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
Article: (p5system), (blowup), the actual central-family polynomial source.
Use: the four primal numerators and three dual equations are defined from the
original normalized Chebyshev functionals before their finite coefficient codes.
No proposed solution, interval annotation or numerical certificate enters them.
-/

noncomputable section
open scoped Polynomial
namespace polyak.Boundary.P5

/-- Article: h,A,B,y,P,D,w₂,w₃, in the original regularized coordinate order. -/
abbrev SourcePolynomial := MvPolynomial (Fin 8) ℚ

/-- Article: an exact coordinate variable in the polynomial source. -/
def sourceVar (i : Fin 8) : SourcePolynomial := MvPolynomial.X i

/-- Article: the regularizing parameter h=G−1. -/
def H : SourcePolynomial := sourceVar 0
/-- Article: the blown-up twist u=1/2+hA. -/
def U : SourcePolynomial := MvPolynomial.C (1/2)+H*sourceVar 1
/-- Article: the main atom x=−1/2+hB. -/
def X : SourcePolynomial := MvPolynomial.C (-1/2)+H*sourceVar 2
/-- Article: the auxiliary atom. -/
def Y : SourcePolynomial := sourceVar 3
/-- Article: p=hP, the auxiliary atom's probability weight. -/
def Probability : SourcePolynomial := H*sourceVar 4
/-- Article: d=hD, the normalized value constant. -/
def Charge : SourcePolynomial := H*sourceVar 5
/-- Article: w₂, the normalized upper-lag-two dual weight. -/
def W₂ : SourcePolynomial := sourceVar 6
/-- Article: w₃, the normalized upper-lag-three dual weight. -/
def W₃ : SourcePolynomial := sourceVar 7
/-- Article: w₅=1−w₂−w₃. -/
def W₅ : SourcePolynomial := 1-W₂-W₃
/-- Article: G=1+h. -/
def G : SourcePolynomial := 1+H

/-- Article: Chebyshev T evaluated in the exact source polynomial ring. -/
def sourceT (n : ℕ) (a : SourcePolynomial) : SourcePolynomial :=
  (Polynomial.Chebyshev.T ℚ (n : ℤ)).eval₂ MvPolynomial.C a

/-- Article: Chebyshev U evaluated in the exact source polynomial ring. -/
def sourceU (n : ℕ) (a : SourcePolynomial) : SourcePolynomial :=
  (Polynomial.Chebyshev.U ℚ (n : ℤ)).eval₂ MvPolynomial.C a

/-- Article: the raw signed lag numerator at one atom; σ=−1 is lower. -/
def sourceRaw (n : ℕ) (σ : ℚ) (c : SourcePolynomial) : SourcePolynomial :=
  (1-c^2-U^2)*(sourceT n G-sourceT n c)+
    MvPolynomial.C σ*(2*U*(1-c^2)*sourceU (n-1) c)

/-- Article: the primal normalized slack after multiplication by its Chebyshev denominator. -/
def primalNumerator (n : ℕ) (σ : ℚ) : SourcePolynomial :=
  (1-Probability)*sourceRaw n σ X+Probability*sourceRaw n σ Y-
    MvPolynomial.C σ*Charge*sourceU (n-1) G

/-- Article: G U₂(G)U₄(G), the positive common denominator of the dual polynomial. -/
def dualDenominator : SourcePolynomial := G*sourceU 2 G*sourceU 4 G

/-- Article: the central dual numerator as a true polynomial in the frequency.
The displayed divided differences are exactly (Tₘ(G)−Tₘ(c))/(G−c) and
(Uₘ₋₁(G)−Uₘ₋₁(c))/(G−c), so c=G is included. -/
def dualSource : Polynomial SourcePolynomial := by
  let c : Polynomial SourcePolynomial := Polynomial.X
  let g : Polynomial SourcePolynomial := Polynomial.C G
  let u : Polynomial SourcePolynomial := Polynomial.C U
  let d := Polynomial.C dualDenominator
  let a₂ := Polynomial.C (W₂*(sourceU 2 G*sourceU 4 G*MvPolynomial.C (1/2)))
  let a₃ := Polynomial.C (W₃*(G*sourceU 4 G))
  let a₅ := Polynomial.C (W₅*(G*sourceU 2 G))
  exact -(1-c^2-u^2)*(d+a₂*(2*(g+c))+a₃*(4*(g^2+g*c+c^2)-3)+
      a₅*(16*(g^4+g^3*c+g^2*c^2+g*c^3+c^4)-20*(g^2+g*c+c^2)+5))+
    2*u*(1-c^2)*(a₂*2+a₃*(4*(g+c))+
      a₅*(16*(g^3+g^2*c+g*c^2+c^3)-12*(g+c)))

/-- Article: the exact formal frequency derivative of the central dual source. -/
def dualDerivativeSource : Polynomial SourcePolynomial := by
  let c : Polynomial SourcePolynomial := Polynomial.X
  let g : Polynomial SourcePolynomial := Polynomial.C G
  let u : Polynomial SourcePolynomial := Polynomial.C U
  let d := Polynomial.C dualDenominator
  let a₂ := Polynomial.C (W₂*(sourceU 2 G*sourceU 4 G*MvPolynomial.C (1/2)))
  let a₃ := Polynomial.C (W₃*(G*sourceU 4 G))
  let a₅ := Polynomial.C (W₅*(G*sourceU 2 G))
  let a := d+a₂*(2*(g+c))+a₃*(4*(g^2+g*c+c^2)-3)+
    a₅*(16*(g^4+g^3*c+g^2*c^2+g*c^3+c^4)-20*(g^2+g*c+c^2)+5)
  let b := a₂*2+a₃*(4*(g+c))+a₅*(16*(g^3+g^2*c+g*c^2+c^3)-12*(g+c))
  let da := a₂*2+a₃*(4*(g+2*c))+
    a₅*(16*(g^3+2*g^2*c+3*g*c^2+4*c^3)-20*(g+2*c))
  let db := a₃*4+a₅*(16*(g^2+2*g*c+3*c^2)-12)
  exact 2*c*a-(1-c^2-u^2)*da+2*u*(-2*c*b+(1-c^2)*db)

/-- Article: the three actual dual equations Q(y)=Q′(x)=Q′(y)=0,
with their common positive parameter denominator removed. -/
def dualNumerator (i : Fin 3) : SourcePolynomial :=
  if i=0 then dualSource.eval Y else
    dualSource.derivative.eval (if i=1 then X else Y)

/-- Article: interpretation of the independently specified source polynomial at real data. -/
def sourceEval (z : Fin 8 → ℝ) : SourcePolynomial →+* ℝ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) z

end polyak.Boundary.P5
