import polyak.Boundary.P5.CriticalData
import polyak.Numerics.Modular

/-!
Article: exact coefficient certificates for P₅ at h=0.
Use: finite rational arrays are linked to the independent critical source
formulas before any sign or algebraic conclusion is drawn.
-/
noncomputable section
open scoped Polynomial
namespace polyak.Certificates.P5
open Polynomial Numerics Boundary.P5 LeanCert.Engine

/-- Article: exact executable coefficients for A at criticality. -/
def ACode : PolynomialCode APolynomial where
  code := ⟨#[(693/1208),(-75/302),(27/604),(-77/302),(-34/151)]⟩
  exact := by
    change C ((693/1208) : ℚ)+X*(C ((-75/302) : ℚ)+X*(C ((27/604) : ℚ)+X*(C ((-77/302) : ℚ)+X*(C ((-34/151) : ℚ)+X*(0))))) = APolynomial
    dsimp only [APolynomial]
    ring

/-- Article: exact executable coefficients for B at criticality. -/
def BCode : PolynomialCode BPolynomial where
  code := ⟨#[(-7471/2416),(19977/1208),(-29287/1208),(16769/604),(-2275/151)]⟩
  exact := by
    change C ((-7471/2416) : ℚ)+X*(C ((19977/1208) : ℚ)+X*(C ((-29287/1208) : ℚ)+X*(C ((16769/604) : ℚ)+X*(C ((-2275/151) : ℚ)+X*(0))))) = BPolynomial
    dsimp only [BPolynomial]
    ring

/-- Article: exact executable coefficients for D at criticality. -/
def DCode : PolynomialCode DPolynomial where
  code := ⟨#[(4381/2416),(1773/1208),(-1959/1208),(2097/604),(-243/151)]⟩
  exact := by
    change C ((4381/2416) : ℚ)+X*(C ((1773/1208) : ℚ)+X*(C ((-1959/1208) : ℚ)+X*(C ((2097/604) : ℚ)+X*(C ((-243/151) : ℚ)+X*(0))))) = DPolynomial
    dsimp only [DPolynomial]
    ring

/-- Article: exact executable coefficients for P at criticality. -/
def PCode : PolynomialCode PPolynomial where
  code := ⟨#[(-501309/8456),(1529793/4228),(-2294121/4228),(1393863/2114),(-396330/1057)]⟩
  exact := by
    change C ((-501309/8456) : ℚ)+X*(C ((1529793/4228) : ℚ)+X*(C ((-2294121/4228) : ℚ)+X*(C ((1393863/2114) : ℚ)+X*(C ((-396330/1057) : ℚ)+X*(0))))) = PPolynomial
    dsimp only [PPolynomial]
    ring

/-- Article: exact executable coefficients for w2 at criticality. -/
def w2Code : PolynomialCode w2Polynomial where
  code := ⟨#[(10388100/43243231),(22511544/43243231),(5194992/43243231),(15609088/43243231),(36571392/43243231)]⟩
  exact := by
    change C ((10388100/43243231) : ℚ)+X*(C ((22511544/43243231) : ℚ)+X*(C ((5194992/43243231) : ℚ)+X*(C ((15609088/43243231) : ℚ)+X*(C ((36571392/43243231) : ℚ)+X*(0))))) = w2Polynomial
    dsimp only [w2Polynomial]
    ring

/-- Article: exact executable coefficients for w3 at criticality. -/
def w3Code : PolynomialCode w3Polynomial where
  code := ⟨#[(25003776/43243231),(3069756/43243231),(708408/43243231),(2128512/43243231),(4987008/43243231)]⟩
  exact := by
    change C ((25003776/43243231) : ℚ)+X*(C ((3069756/43243231) : ℚ)+X*(C ((708408/43243231) : ℚ)+X*(C ((2128512/43243231) : ℚ)+X*(C ((4987008/43243231) : ℚ)+X*(0))))) = w3Polynomial
    dsimp only [w3Polynomial]
    ring

/-- Article: exact executable coefficients for w5 at criticality. -/
def w5Code : PolynomialCode w5Polynomial where
  code := ⟨#[(7851355/43243231),(-25581300/43243231),(-5903400/43243231),(-17737600/43243231),(-41558400/43243231)]⟩
  exact := by
    change C ((7851355/43243231) : ℚ)+X*(C ((-25581300/43243231) : ℚ)+X*(C ((-5903400/43243231) : ℚ)+X*(C ((-17737600/43243231) : ℚ)+X*(C ((-41558400/43243231) : ℚ)+X*(0))))) = w5Polynomial
    dsimp only [w5Polynomial]
    ring

/-- Article: exact executable coefficients for dualDet at criticality. -/
def dualDetCode : PolynomialCode dualDetPolynomial where
  code := ⟨#[(-276075/16),31725,(783675/8),(102825/2),(306225/2)]⟩
  exact := by
    change C ((-276075/16) : ℚ)+X*(C (31725 : ℚ)+X*(C ((783675/8) : ℚ)+X*(C ((102825/2) : ℚ)+X*(C ((306225/2) : ℚ)+X*(0))))) = dualDetPolynomial
    dsimp only [dualDetPolynomial]
    ring

/-- Article: exact executable coefficients for primalDet at criticality. -/
def primalDetCode : PolynomialCode primalDetPolynomial where
  code := ⟨#[3078,-38016,-23436,85104,-32400]⟩
  exact := by
    change C (3078 : ℚ)+X*(C (-38016 : ℚ)+X*(C (-23436 : ℚ)+X*(C (85104 : ℚ)+X*(C (-32400 : ℚ)+X*(0))))) = primalDetPolynomial
    dsimp only [primalDetPolynomial]
    ring

/-- Article: exact executable coefficients for q0 at criticality. -/
def q0Code : PolynomialCode q0Polynomial where
  code := ⟨#[(39714948/43243231),(-57555904/43243231),(38477232/43243231),(-7311424/43243231),(-74548736/43243231)]⟩
  exact := by
    change C ((39714948/43243231) : ℚ)+X*(C ((-57555904/43243231) : ℚ)+X*(C ((38477232/43243231) : ℚ)+X*(C ((-7311424/43243231) : ℚ)+X*(C ((-74548736/43243231) : ℚ)+X*(0))))) = q0Polynomial
    dsimp only [q0Polynomial]
    ring

/-- Article: exact executable coefficients for q1 at criticality. -/
def q1Code : PolynomialCode q1Polynomial where
  code := ⟨#[(-189296/43243231),(32368672/43243231),(-194699520/43243231),(151965440/43243231),(-313000960/43243231)]⟩
  exact := by
    change C ((-189296/43243231) : ℚ)+X*(C ((32368672/43243231) : ℚ)+X*(C ((-194699520/43243231) : ℚ)+X*(C ((151965440/43243231) : ℚ)+X*(C ((-313000960/43243231) : ℚ)+X*(0))))) = q1Polynomial
    dsimp only [q1Polynomial]
    ring

/-- Article: exact executable coefficients for q2 at criticality. -/
def q2Code : PolynomialCode q2Polynomial where
  code := ⟨#[(25124336/43243231),(-81860160/43243231),(-18890880/43243231),(-56760320/43243231),(-132986880/43243231)]⟩
  exact := by
    change C ((25124336/43243231) : ℚ)+X*(C ((-81860160/43243231) : ℚ)+X*(C ((-18890880/43243231) : ℚ)+X*(C ((-56760320/43243231) : ℚ)+X*(C ((-132986880/43243231) : ℚ)+X*(0))))) = q2Polynomial
    dsimp only [q2Polynomial]
    ring

end polyak.Certificates.P5
