import polyak.Boundary.Optimality
import polyak.Numerics.Concrete

/-!
Article: (p2poly), (p2param), Definition p2data and Lemma p2ends.
Use: the mathematical formulas are fixed independently of executable coefficients
and numerical enclosures. Polynomial formulas are valid over any commutative ring.
-/

namespace polyak.Boundary.P2
noncomputable section

section PolynomialSources
variable {R : Type*} [CommRing R]

/-- Article: q₋=ζ²−2ζ+2. -/
def qMinus (z : R) : R := z^2-2*z+2
/-- Article: q₊=ζ²+2ζ+2. -/
def qPlus (z : R) : R := z^2+2*z+2
/-- Article: r₋=ζ²−2. -/
def rMinus (z : R) : R := z^2-2
/-- Article: r₊=ζ²+2. -/
def rPlus (z : R) : R := z^2+2
/-- Article: e₋=ζ²−2ζ−2. -/
def eMinus (z : R) : R := z^2-2*z-2
/-- Article: e₊=ζ²+2ζ−2. -/
def ePlus (z : R) : R := z^2+2*z-2
/-- Article: K₆, the denominator of the dual weights. -/
def K6 (z : R) : R := z^6-4*z^5+4*z^4+8*z^2-16*z+8
/-- Article: F₈, the numerator of the mean cosine. -/
def F8 (z : R) : R :=
  15*z^8-92*z^7+224*z^6-440*z^5+760*z^4-880*z^3+896*z^2-736*z+240
/-- Article: M₁₀, the denominator of the primal moment and value constant. -/
def M10 (z : R) : R :=
  5*z^10-44*z^9+170*z^8-368*z^7+744*z^6-1376*z^5+1488*z^4-
    1472*z^3+1360*z^2-704*z+160
/-- Article: D₁₄, the numerator of the normalized value constant. -/
def D14 (z : R) : R :=
  5*z^14-34*z^13+42*z^12+648*z^11-3460*z^10+8296*z^9-14984*z^8+
    23616*z^7-29968*z^6+33184*z^5-27680*z^4+10368*z^3+1344*z^2-2176*z+640
/-- Article: N₁₀, the common numerator of the nonactive lag slacks. -/
def N10 (z : R) : R :=
  5*z^10-24*z^9+74*z^8-512*z^7+1448*z^6-2240*z^5+2896*z^4-
    2048*z^3+592*z^2-384*z+160
/-- Article: N₈ in the exact averaged minimizer gap. -/
def N8 (z : R) : R :=
  5*z^8-24*z^7+48*z^6-104*z^5+184*z^4-208*z^3+192*z^2-192*z+80
/-- Article: N₁₂, the defining polynomial of the P₂-to-P₅ endpoint. -/
def N12 (z : R) : R :=
  25*z^12-314*z^11+1764*z^10-6092*z^9+14988*z^8-28736*z^7+44832*z^6-
    57472*z^5+59952*z^4-48736*z^3+28224*z^2-10048*z+1600
/-- Article: the cubic defining the spiral-to-P₂ endpoint. -/
def endpointCubic (z : R) : R := z^3-z^2-2
/-- Article: Hₐ, the defining polynomial in the physical G coordinate. -/
def Ha (G : R) : R :=
  162529280000*G^12-238685519872*G^10+77668708352*G^8-6246545408*G^6-
    58821872*G^4+12933112*G^2+229441
/-- Article: the implicit P₂ curve. -/
def curvePolynomial (G u : R) : R :=
  256*G^4*(u^2-1)-512*G^3*u^3+768*G^3*u-32*G^2*u^4-
    480*G^2*u^2-16*G*u^3-u^4-16*u^2

end PolynomialSources

/-- Article: the exact rational parametrization G(ζ). -/
def G (z : ℝ) : ℝ := (z^4+4)/(8*z*rMinus z)
/-- Article: the exact rational parametrization u(ζ). -/
def u (z : ℝ) : ℝ := qMinus z^2/(z^4-4)
/-- Article: the upper-lag-two dual weight W. -/
def W (z : ℝ) : ℝ := qMinus z^2*qPlus z*(7*z^2-18*z+14)/(8*rPlus z*K6 z)
/-- Article: the linear coefficient of the monic atom polynomial. -/
def atomA (z : ℝ) : ℝ := qMinus z^3/(2*z*rMinus z*rPlus z)
/-- Article: the constant coefficient of the monic atom polynomial. -/
def atomB (z : ℝ) : ℝ :=
  -2*z*(3*z^4-10*z^3+16*z^2-20*z+12)/(rMinus z^2*rPlus z)
/-- Article: the prescribed mean cosine. -/
def meanCosine (z : ℝ) : ℝ := 4*z^2*F8 z/(rMinus z*M10 z)
/-- Article: d=C sinh t, independent of the sign of t. -/
def d (z : ℝ) : ℝ := qMinus z^3*D14 z/(rMinus z^3*rPlus z^2*M10 z)
/-- Article: the atom polynomial c²+ac+b. -/
def atomPolynomial (z c : ℝ) : ℝ := c^2+atomA z*c+atomB z
/-- Article: its smaller real root. Real-root existence is proved on J. -/
def x (z : ℝ) : ℝ := (-atomA z-Real.sqrt (atomA z^2-4*atomB z))/2
/-- Article: its larger real root. -/
def y (z : ℝ) : ℝ := (-atomA z+Real.sqrt (atomA z^2-4*atomB z))/2
/-- Article: the upper-atom probability weight. -/
def p (z : ℝ) : ℝ := (meanCosine z-x z)/(y z-x z)
/-- Article: the averaged minimizer slack after reducing c² modulo its atom polynomial. -/
def meanGap (z : ℝ) : ℝ := 1-u z^2+atomA z*meanCosine z+atomB z
/-- Article: the derivative du/dG in the rational parameter. -/
def slope (z : ℝ) : ℝ :=
  32*z^2*qMinus z*(z^4-2*z^3-4*z+4)/(rPlus z^3*eMinus z*ePlus z)

/-- Article: the exact factor multiplying ζ³−ζ²−2 in the atom polynomial at its mean. -/
def meanRootFactor (z : ℝ) : ℝ :=
  32*z^3*eMinus z*ePlus z*(z^3+2*z-4)*N10 z/(rMinus z^2*rPlus z*M10 z^2)

/-- Article: the positive factor multiplying N₁₂ in the upper lag-five slack. -/
def upperFiveFactor (z : ℝ) : ℝ :=
  (N10 z/M10 z)*(eMinus z*ePlus z*qMinus z^3)/(8*z^2*rPlus z^2*rMinus z^7)

/-- Article: reduced power moments modulo c²+ac+b, fixed before the certificate data. -/
def moment (z : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => meanCosine z
  | n+2 => -atomA z*moment z (n+1)-atomB z*moment z n

/-- Article: all finite sign certificates use the same exact interval J. -/
def parameterInterval : Set ℝ := Set.Icc (3391/2000) (1699/1000)

end
end polyak.Boundary.P2
