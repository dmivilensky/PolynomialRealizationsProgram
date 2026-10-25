import polyak.Boundary.P5.CriticalRoot

/-!
Article: Appendix B, Theorem p5h0, exact values in ℚ(y₀).
Use: source formulas for the critical central family; coefficient certificates
are separate objects and do not define these mathematical expressions.
-/
noncomputable section
open scoped Polynomial
namespace polyak.Boundary.P5
open Polynomial

/-- Article: the critical source polynomial for A. -/
def APolynomial : ℚ[X] := C ((693/1208) : ℚ)+C ((-75/302) : ℚ)*X+C ((27/604) : ℚ)*X^2+C ((-77/302) : ℚ)*X^3+C ((-34/151) : ℚ)*X^4

/-- Article: the critical source polynomial for B. -/
def BPolynomial : ℚ[X] := C ((-7471/2416) : ℚ)+C ((19977/1208) : ℚ)*X+C ((-29287/1208) : ℚ)*X^2+C ((16769/604) : ℚ)*X^3+C ((-2275/151) : ℚ)*X^4

/-- Article: the critical source polynomial for D. -/
def DPolynomial : ℚ[X] := C ((4381/2416) : ℚ)+C ((1773/1208) : ℚ)*X+C ((-1959/1208) : ℚ)*X^2+C ((2097/604) : ℚ)*X^3+C ((-243/151) : ℚ)*X^4

/-- Article: the critical source polynomial for P. -/
def PPolynomial : ℚ[X] := C ((-501309/8456) : ℚ)+C ((1529793/4228) : ℚ)*X+C ((-2294121/4228) : ℚ)*X^2+C ((1393863/2114) : ℚ)*X^3+C ((-396330/1057) : ℚ)*X^4

/-- Article: the critical source polynomial for w2. -/
def w2Polynomial : ℚ[X] := C ((10388100/43243231) : ℚ)+C ((22511544/43243231) : ℚ)*X+C ((5194992/43243231) : ℚ)*X^2+C ((15609088/43243231) : ℚ)*X^3+C ((36571392/43243231) : ℚ)*X^4

/-- Article: the critical source polynomial for w3. -/
def w3Polynomial : ℚ[X] := C ((25003776/43243231) : ℚ)+C ((3069756/43243231) : ℚ)*X+C ((708408/43243231) : ℚ)*X^2+C ((2128512/43243231) : ℚ)*X^3+C ((4987008/43243231) : ℚ)*X^4

/-- Article: the critical source polynomial for w5. -/
def w5Polynomial : ℚ[X] := C ((7851355/43243231) : ℚ)+C ((-25581300/43243231) : ℚ)*X+C ((-5903400/43243231) : ℚ)*X^2+C ((-17737600/43243231) : ℚ)*X^3+C ((-41558400/43243231) : ℚ)*X^4

/-- Article: the critical source polynomial for dualDet. -/
def dualDetPolynomial : ℚ[X] := C ((-276075/16) : ℚ)+C (31725 : ℚ)*X+C ((783675/8) : ℚ)*X^2+C ((102825/2) : ℚ)*X^3+C ((306225/2) : ℚ)*X^4

/-- Article: the critical source polynomial for primalDet. -/
def primalDetPolynomial : ℚ[X] := C (3078 : ℚ)+C (-38016 : ℚ)*X+C (-23436 : ℚ)*X^2+C (85104 : ℚ)*X^3+C (-32400 : ℚ)*X^4

/-- Article: the critical source polynomial for q0. -/
def q0Polynomial : ℚ[X] := C ((39714948/43243231) : ℚ)+C ((-57555904/43243231) : ℚ)*X+C ((38477232/43243231) : ℚ)*X^2+C ((-7311424/43243231) : ℚ)*X^3+C ((-74548736/43243231) : ℚ)*X^4

/-- Article: the critical source polynomial for q1. -/
def q1Polynomial : ℚ[X] := C ((-189296/43243231) : ℚ)+C ((32368672/43243231) : ℚ)*X+C ((-194699520/43243231) : ℚ)*X^2+C ((151965440/43243231) : ℚ)*X^3+C ((-313000960/43243231) : ℚ)*X^4

/-- Article: the critical source polynomial for q2. -/
def q2Polynomial : ℚ[X] := C ((25124336/43243231) : ℚ)+C ((-81860160/43243231) : ℚ)*X+C ((-18890880/43243231) : ℚ)*X^2+C ((-56760320/43243231) : ℚ)*X^3+C ((-132986880/43243231) : ℚ)*X^4

/-- Article: A evaluated in the actual isolated critical root. -/
def A₀ : ℝ := Polynomial.aeval y₀ APolynomial

/-- Article: B evaluated in the actual isolated critical root. -/
def B₀ : ℝ := Polynomial.aeval y₀ BPolynomial

/-- Article: D evaluated in the actual isolated critical root. -/
def D₀ : ℝ := Polynomial.aeval y₀ DPolynomial

/-- Article: P evaluated in the actual isolated critical root. -/
def P₀ : ℝ := Polynomial.aeval y₀ PPolynomial

/-- Article: w2 evaluated in the actual isolated critical root. -/
def w2₀ : ℝ := Polynomial.aeval y₀ w2Polynomial

/-- Article: w3 evaluated in the actual isolated critical root. -/
def w3₀ : ℝ := Polynomial.aeval y₀ w3Polynomial

/-- Article: w5 evaluated in the actual isolated critical root. -/
def w5₀ : ℝ := Polynomial.aeval y₀ w5Polynomial

/-- Article: dualDet evaluated in the actual isolated critical root. -/
def dualDet₀ : ℝ := Polynomial.aeval y₀ dualDetPolynomial

/-- Article: primalDet evaluated in the actual isolated critical root. -/
def primalDet₀ : ℝ := Polynomial.aeval y₀ primalDetPolynomial

/-- Article: q0 evaluated in the actual isolated critical root. -/
def q0₀ : ℝ := Polynomial.aeval y₀ q0Polynomial

/-- Article: q1 evaluated in the actual isolated critical root. -/
def q1₀ : ℝ := Polynomial.aeval y₀ q1Polynomial

/-- Article: q2 evaluated in the actual isolated critical root. -/
def q2₀ : ℝ := Polynomial.aeval y₀ q2Polynomial

end polyak.Boundary.P5
