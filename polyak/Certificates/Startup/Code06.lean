import polyak.Certificates.Startup.Code05

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: canonical numerator for one arithmetic source node. -/
def hAst051Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-10,0,-6,0,-1],[0,0,-8,0,-16,0,-16,0,-8],[4,8,16,-8,56,-8,16,8,4],[12,0,36,0,36,0,12]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst051Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst051Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 1)+(Source.radius z.1 z.2 1))) :=
  (hDiscrepancy1Code.add hRadius1Code)
private theorem hAst051DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst051Denominator=true := by kernel_decide
private theorem hAst051DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst051Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst051Denominator hAst051DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst051Cross : equalCheck
    (mul hAst051Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst051Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst051Numerator) hAst051Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst051Code : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 1)+(Source.radius z.1 z.2 1))) :=
  hAst051Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst051Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst051Denominator)
    hAst051DenNonzero hAst051Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst052Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-10,0,-6,0,-1],[0,0,-8,0,-16,0,-16,0,-8],[20,8,64,-8,104,-8,32,8,4],[12,0,36,0,36,0,12],[32,0,96,0,96,0,32],[0],[16,0,48,0,48,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst052Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst052Raw : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 1)+(Source.radius z.1 z.2 1))+((((1 : ℚ) : ℝ)+(z.2)^2))^2)) :=
  (hAst051Code.add hAst047Code)
private theorem hAst052DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst052Denominator=true := by kernel_decide
private theorem hAst052DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst052Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst052Denominator hAst052DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst052Cross : equalCheck
    (mul hAst052Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst052Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst052Numerator) hAst052Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst052Code : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 1)+(Source.radius z.1 z.2 1))+((((1 : ℚ) : ℝ)+(z.2)^2))^2)) :=
  hAst052Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst052Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst052Denominator)
    hAst052DenNonzero hAst052Cross

/-- Article: proposed exact numerator for hPairUpper1. -/
def hPairUpper1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-10,0,-6,0,-1],[0,0,-8,0,-16,0,-16,0,-8],[20,8,64,-8,104,-8,32,8,4],[12,0,36,0,36,0,12],[32,0,96,0,96,0,32],[0],[16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for hPairUpper1. -/
def hPairUpper1Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairUpper1Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 1)+(Source.radius z.1 z.2 1)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)) :=
  (hAst052Code.congr (by
    intro z hz
    ring))
private theorem hPairUpper1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.discrepancy z.1 z.2 1)+(Source.radius z.1 z.2 1)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)=Source.pairSlack z.1 z.2 (1) 1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairUpper1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairUpper1Denominator=true := by kernel_decide
private theorem hPairUpper1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairUpper1Denominator hPairUpper1DenCheck hz.1 hz.2).ne'
private theorem hPairUpper1Cross : equalCheck
    (mul hPairUpper1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper1Numerator) hPairUpper1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairUpper1. -/
def hPairUpper1Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (1) 1) :=
  (hPairUpper1Raw.congr hPairUpper1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper1Denominator)
    hPairUpper1DenNonzero hPairUpper1Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst053Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,0,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst053Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst053Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 2 (radialCosine z.1))*(z.1)^2)) :=
  (hT2Code.mul hAst031Code)
private theorem hAst053DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst053Denominator=true := by kernel_decide
private theorem hAst053DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst053Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst053Denominator hAst053DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst053Cross : equalCheck
    (mul hAst053Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst053Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst053Numerator) hAst053Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst053Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 2 (radialCosine z.1))*(z.1)^2)) :=
  hAst053Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst053Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst053Denominator)
    hAst053DenNonzero hAst053Cross

/-- Article: proposed exact numerator for hPowerReal2. -/
def hPowerReal2Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,0,0,-1]]
/-- Article: proposed positive denominator for hPowerReal2. -/
def hPowerReal2Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerReal2Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 2 (radialCosine z.1))*(z.1)^2)) :=
  (hAst053Code.congr (by
    intro z hz
    ring))
private theorem hPowerReal2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebT 2 (radialCosine z.1))*(z.1)^2)=Source.powerReal z.1 2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.powerReal]; ring
private theorem hPowerReal2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerReal2Denominator=true := by kernel_decide
private theorem hPowerReal2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerReal2Denominator hPowerReal2DenCheck hz.1 hz.2).ne'
private theorem hPowerReal2Cross : equalCheck
    (mul hPowerReal2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal2Numerator) hPowerReal2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerReal2. -/
def hPowerReal2Code : RationalCode Source.domain (fun z => Source.powerReal z.1 2) :=
  (hPowerReal2Raw.congr hPowerReal2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal2Denominator)
    hPowerReal2DenNonzero hPowerReal2Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst054Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst054Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst054Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 1 (radialCosine z.1))*z.1)) :=
  (hU1Code.mul (RationalCode.first Source.domain))
private theorem hAst054DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst054Denominator=true := by kernel_decide
private theorem hAst054DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst054Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst054Denominator hAst054DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst054Cross : equalCheck
    (mul hAst054Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst054Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst054Numerator) hAst054Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst054Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 1 (radialCosine z.1))*z.1)) :=
  hAst054Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst054Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst054Denominator)
    hAst054DenNonzero hAst054Cross

/-- Article: proposed exact numerator for hPowerImag2. -/
def hPowerImag2Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2]]
/-- Article: proposed positive denominator for hPowerImag2. -/
def hPowerImag2Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerImag2Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 1 (radialCosine z.1))*z.1)) :=
  (hAst054Code.congr (by
    intro z hz
    ring))
private theorem hPowerImag2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebU 1 (radialCosine z.1))*z.1)=Source.powerImag z.1 2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.powerImag,ite_eq_right (by decide)]; ring
private theorem hPowerImag2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerImag2Denominator=true := by kernel_decide
private theorem hPowerImag2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerImag2Denominator hPowerImag2DenCheck hz.1 hz.2).ne'
private theorem hPowerImag2Cross : equalCheck
    (mul hPowerImag2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag2Numerator) hPowerImag2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerImag2. -/
def hPowerImag2Code : RationalCode Source.domain (fun z => Source.powerImag z.1 2) :=
  (hPowerImag2Raw.congr hPowerImag2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag2Denominator)
    hPowerImag2DenNonzero hPowerImag2Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst055Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,0,0,1],[0],[0,0,1,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst055Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst055Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 2)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerReal2Code.mul hSRealCode)
private theorem hAst055DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst055Denominator=true := by kernel_decide
private theorem hAst055DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst055Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst055Denominator hAst055DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst055Cross : equalCheck
    (mul hAst055Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst055Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst055Numerator) hAst055Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst055Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 2)*(Source.multiplierReal z.1 z.2))) :=
  hAst055Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst055Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst055Denominator)
    hAst055DenNonzero hAst055Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst056Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,2,0,2,0,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst056Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst056Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))) :=
  (hAst002Code.mul hPowerImag2Code)
private theorem hAst056DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst056Denominator=true := by kernel_decide
private theorem hAst056DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst056Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst056Denominator hAst056DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst056Cross : equalCheck
    (mul hAst056Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst056Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst056Numerator) hAst056Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst056Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))) :=
  hAst056Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst056Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst056Denominator)
    hAst056DenNonzero hAst056Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst057Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,1,0,1],[0],[0,0,-1,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst057Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst057Raw : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))*(Source.multiplierImag z.1 z.2))) :=
  (hAst056Code.mul hSImagCode)
private theorem hAst057DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst057Denominator=true := by kernel_decide
private theorem hAst057DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst057Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst057Denominator hAst057DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst057Cross : equalCheck
    (mul hAst057Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst057Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst057Numerator) hAst057Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst057Code : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))*(Source.multiplierImag z.1 z.2))) :=
  hAst057Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst057Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst057Denominator)
    hAst057DenNonzero hAst057Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst058Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,3,0,2,0,3],[0],[0,0,-1,0,-2,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst058Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst058Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 2)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))*(Source.multiplierImag z.1 z.2)))) :=
  (hAst055Code.add hAst057Code)
private theorem hAst058DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst058Denominator=true := by kernel_decide
private theorem hAst058DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst058Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst058Denominator hAst058DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst058Cross : equalCheck
    (mul hAst058Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst058Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst058Numerator) hAst058Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst058Code : RationalCode Source.domain (fun z => (((Source.powerReal z.1 2)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))*(Source.multiplierImag z.1 z.2)))) :=
  hAst058Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst058Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst058Denominator)
    hAst058DenNonzero hAst058Cross

/-- Article: proposed exact numerator for hGradientReal2. -/
def hGradientReal2Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,3,0,2,0,3],[0],[0,0,-1,0,-2,0,-1]]
/-- Article: proposed positive denominator for hGradientReal2. -/
def hGradientReal2Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientReal2Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 2)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 2)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst058Code.congr (by
    intro z hz
    ring))
private theorem hGradientReal2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerReal z.1 2)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 2)*(Source.multiplierImag z.1 z.2)))=Source.gradientReal z.1 z.2 2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientReal]; ring
private theorem hGradientReal2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientReal2Denominator=true := by kernel_decide
private theorem hGradientReal2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientReal2Denominator hGradientReal2DenCheck hz.1 hz.2).ne'
private theorem hGradientReal2Cross : equalCheck
    (mul hGradientReal2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal2Numerator) hGradientReal2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientReal2. -/
def hGradientReal2Code : RationalCode Source.domain (fun z => Source.gradientReal z.1 z.2 2) :=
  (hGradientReal2Raw.congr hGradientReal2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal2Denominator)
    hGradientReal2DenNonzero hGradientReal2Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst059Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1],[0],[0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst059Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,2,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst059Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 2)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerImag2Code.mul hSRealCode)
private theorem hAst059DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst059Denominator=true := by kernel_decide
private theorem hAst059DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst059Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst059Denominator hAst059DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst059Cross : equalCheck
    (mul hAst059Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst059Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst059Numerator) hAst059Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst059Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 2)*(Source.multiplierReal z.1 z.2))) :=
  hAst059Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst059Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst059Denominator)
    hAst059DenNonzero hAst059Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst060Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,0,0,-1],[0],[1,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst060Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst060Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 2)*(Source.multiplierImag z.1 z.2))) :=
  (hPowerReal2Code.mul hSImagCode)
private theorem hAst060DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst060Denominator=true := by kernel_decide
private theorem hAst060DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst060Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst060Denominator hAst060DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst060Cross : equalCheck
    (mul hAst060Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst060Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst060Numerator) hAst060Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst060Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 2)*(Source.multiplierImag z.1 z.2))) :=
  hAst060Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst060Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst060Denominator)
    hAst060DenNonzero hAst060Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst061Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,2,0,-1],[0],[1,0,2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst061Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst061Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 2)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 2)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst059Code.add hAst060Code)
private theorem hAst061DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst061Denominator=true := by kernel_decide
private theorem hAst061DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst061Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst061Denominator hAst061DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst061Cross : equalCheck
    (mul hAst061Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst061Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst061Numerator) hAst061Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst061Code : RationalCode Source.domain (fun z => (((Source.powerImag z.1 2)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 2)*(Source.multiplierImag z.1 z.2)))) :=
  hAst061Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst061Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst061Denominator)
    hAst061DenNonzero hAst061Cross

/-- Article: proposed exact numerator for hGradientImag2. -/
def hGradientImag2Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,2,0,-1],[0],[1,0,2,0,1]]
/-- Article: proposed positive denominator for hGradientImag2. -/
def hGradientImag2Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientImag2Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 2)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 2)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst061Code.congr (by
    intro z hz
    ring))
private theorem hGradientImag2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerImag z.1 2)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 2)*(Source.multiplierImag z.1 z.2)))=Source.gradientImag z.1 z.2 2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientImag]; ring
private theorem hGradientImag2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientImag2Denominator=true := by kernel_decide
private theorem hGradientImag2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientImag2Denominator hGradientImag2DenCheck hz.1 hz.2).ne'
private theorem hGradientImag2Cross : equalCheck
    (mul hGradientImag2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag2Numerator) hGradientImag2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientImag2. -/
def hGradientImag2Code : RationalCode Source.domain (fun z => Source.gradientImag z.1 z.2 2) :=
  (hGradientImag2Raw.congr hGradientImag2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag2Denominator)
    hGradientImag2DenNonzero hGradientImag2Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst062Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,3,0,2,0,3],[0],[-2,0,-6,0,-6,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst062Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst062Raw : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  (hGradientReal2Code.add hAst009Code)
private theorem hAst062DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst062Denominator=true := by kernel_decide
private theorem hAst062DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst062Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst062Denominator hAst062DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst062Cross : equalCheck
    (mul hAst062Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst062Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst062Numerator) hAst062Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst062Code : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  hAst062Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst062Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst062Denominator)
    hAst062DenNonzero hAst062Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst063Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,5,0,3,0,3],[0],[-1,0,-4,0,-5,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst063Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst063Raw : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  (hAst062Code.add hAst010Code)
private theorem hAst063DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst063Denominator=true := by kernel_decide
private theorem hAst063DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst063Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst063Denominator hAst063DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst063Cross : equalCheck
    (mul hAst063Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst063Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst063Numerator) hAst063Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst063Code : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  hAst063Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst063Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst063Denominator)
    hAst063DenNonzero hAst063Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst064Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,10,0,31,0,36,0,39,0,18,0,9],[0],[0,0,-2,0,-18,0,-56,0,-84,0,-74,0,-42,0,-12],[0],[1,0,8,0,26,0,44,0,41,0,20,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst064Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,24,0,60,0,80,0,60,0,24,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst064Raw : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  (hAst063Code.pow 2)
private theorem hAst064DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst064Denominator=true := by kernel_decide
private theorem hAst064DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst064Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst064Denominator hAst064DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst064Cross : equalCheck
    (mul hAst064Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst064Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst064Numerator) hAst064Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst064Code : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  hAst064Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst064Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst064Denominator)
    hAst064DenNonzero hAst064Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst065Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-10,0,-31,0,-36,0,-39,0,-18,0,-9],[0],[0,0,2,0,18,0,56,0,84,0,74,0,42,0,12],[0],[-1,0,-8,0,-26,0,-44,0,-41,0,-20,0,-4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst065Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst065Raw : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  ((RationalCode.constant Source.domain (-1/4)).mul hAst064Code)
private theorem hAst065DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst065Denominator=true := by kernel_decide
private theorem hAst065DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst065Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst065Denominator hAst065DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst065Cross : equalCheck
    (mul hAst065Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst065Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst065Numerator) hAst065Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst065Code : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  hAst065Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst065Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst065Denominator)
    hAst065DenNonzero hAst065Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst066Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-3,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst066Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst066Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2))) :=
  ((RationalCode.constant Source.domain (-1)).add hPowerReal2Code)
private theorem hAst066DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst066Denominator=true := by kernel_decide
private theorem hAst066DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst066Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst066Denominator hAst066DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst066Cross : equalCheck
    (mul hAst066Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst066Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst066Numerator) hAst066Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst066Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2))) :=
  hAst066Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst066Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst066Denominator)
    hAst066DenNonzero hAst066Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst067Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,11,0,8,0,7,0,2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst067Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst067Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2) :=
  (hAst066Code.pow 2)
private theorem hAst067DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst067Denominator=true := by kernel_decide
private theorem hAst067DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst067Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst067Denominator hAst067DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst067Cross : equalCheck
    (mul hAst067Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst067Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst067Numerator) hAst067Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst067Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2) :=
  hAst067Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst067Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst067Denominator)
    hAst067DenNonzero hAst067Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst068Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,11,0,8,0,7,0,2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst068Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,16,0,24,0,16,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst068Raw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2)) :=
  ((RationalCode.constant Source.domain (1/4)).mul hAst067Code)
private theorem hAst068DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst068Denominator=true := by kernel_decide
private theorem hAst068DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst068Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst068Denominator hAst068DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst068Cross : equalCheck
    (mul hAst068Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst068Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst068Numerator) hAst068Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst068Code : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2)) :=
  hAst068Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst068Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst068Denominator)
    hAst068DenNonzero hAst068Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst069Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,2,0,-1],[0],[-1,0,-1,0,1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst069Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst069Raw : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  (hGradientImag2Code.add hAst018Code)
private theorem hAst069DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst069Denominator=true := by kernel_decide
private theorem hAst069DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst069Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst069Denominator hAst069DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst069Cross : equalCheck
    (mul hAst069Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst069Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst069Numerator) hAst069Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst069Code : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  hAst069Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst069Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst069Denominator)
    hAst069DenNonzero hAst069Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst070Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-3,0,1,0,-1],[0],[1,0,2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst070Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst070Raw : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst069Code.add hAst019Code)
private theorem hAst070DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst070Denominator=true := by kernel_decide
private theorem hAst070DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst070Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst070Denominator hAst070DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst070Cross : equalCheck
    (mul hAst070Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst070Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst070Numerator) hAst070Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst070Code : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  hAst070Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst070Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst070Denominator)
    hAst070DenNonzero hAst070Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst071Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,7,0,-4,0,7,0,-2,0,1],[0],[-2,0,-10,0,-12,0,-4,0,-2,0,-2],[0],[1,0,4,0,6,0,4,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst071Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,16,0,24,0,16,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst071Raw : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  (hAst070Code.pow 2)
private theorem hAst071DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst071Denominator=true := by kernel_decide
private theorem hAst071DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst071Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst071Denominator hAst071DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst071Cross : equalCheck
    (mul hAst071Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst071Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst071Numerator) hAst071Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst071Code : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  hAst071Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst071Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst071Denominator)
    hAst071DenNonzero hAst071Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst072Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-14,0,-9,0,-10,0,-1,0,-6,0,1,0,-1],[0],[0,0,2,0,12,0,24,0,26,0,18,0,8,0,4,0,2],[0],[0,0,-1,0,-5,0,-11,0,-14,0,-11,0,-5,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst072Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst072Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  (hAst023Code.mul hAst071Code)
private theorem hAst072DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst072Denominator=true := by kernel_decide
private theorem hAst072DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst072Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst072Denominator hAst072DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst072Cross : equalCheck
    (mul hAst072Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst072Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst072Numerator) hAst072Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst072Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  hAst072Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst072Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst072Denominator)
    hAst072DenNonzero hAst072Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst073Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst073Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst073Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 2))^2) :=
  (hPowerImag2Code.pow 2)
private theorem hAst073DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst073Denominator=true := by kernel_decide
private theorem hAst073DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst073Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst073Denominator hAst073DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst073Cross : equalCheck
    (mul hAst073Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst073Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst073Numerator) hAst073Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst073Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 2))^2) :=
  hAst073Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst073Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst073Denominator)
    hAst073DenNonzero hAst073Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst074Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,1,0,1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst074Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst074Raw : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 2))^2)) :=
  (hAst026Code.mul hAst073Code)
private theorem hAst074DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst074Denominator=true := by kernel_decide
private theorem hAst074DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst074Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst074Denominator hAst074DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst074Cross : equalCheck
    (mul hAst074Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst074Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst074Numerator) hAst074Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst074Code : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 2))^2)) :=
  hAst074Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst074Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst074Denominator)
    hAst074DenNonzero hAst074Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst075Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-10,0,-31,0,-36,0,-39,0,-18,0,-9],[0],[4,0,34,0,114,0,200,0,220,0,170,0,90,0,28,0,4],[0],[-1,0,-8,0,-26,0,-44,0,-41,0,-20,0,-4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst075Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst075Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2))) :=
  (hAst065Code.add hAst068Code)
private theorem hAst075DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst075Denominator=true := by kernel_decide
private theorem hAst075DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst075Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst075Denominator hAst075DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst075Cross : equalCheck
    (mul hAst075Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst075Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst075Numerator) hAst075Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst075Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2))) :=
  hAst075Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst075Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst075Denominator)
    hAst075DenNonzero hAst075Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst076Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1],[0],[4,0,28,0,66,0,64,0,52,0,20,0,6],[0],[-1,0,-7,0,-16,0,-16,0,-7,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst076Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst076Raw : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  (hAst075Code.add hAst072Code)
private theorem hAst076DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst076Denominator=true := by kernel_decide
private theorem hAst076DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst076Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst076Denominator hAst076DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst076Cross : equalCheck
    (mul hAst076Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst076Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst076Numerator) hAst076Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst076Code : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  hAst076Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst076Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst076Denominator)
    hAst076DenNonzero hAst076Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst077Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-6,0,-6,0,-5,0,-1],[0],[4,0,24,0,42,0,38,0,30,0,6],[0],[-1,0,-6,0,-10,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst077Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst077Raw : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 2))^2))) :=
  (hAst076Code.add hAst074Code)
private theorem hAst077DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst077Denominator=true := by kernel_decide
private theorem hAst077DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst077Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst077Denominator hAst077DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst077Cross : equalCheck
    (mul hAst077Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst077Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst077Numerator) hAst077Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst077Code : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 2))^2))) :=
  hAst077Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst077Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst077Denominator)
    hAst077DenNonzero hAst077Cross

/-- Article: proposed exact numerator for hRadius2. -/
def hRadius2Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-6,0,-6,0,-5,0,-1],[0],[4,0,24,0,42,0,38,0,30,0,6],[0],[-1,0,-6,0,-10,0,-6,0,-1]]
/-- Article: proposed positive denominator for hRadius2. -/
def hRadius2Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hRadius2Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 2))^2))) :=
  (hAst077Code.congr (by
    intro z hz
    ring))
private theorem hRadius2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 2)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 2))^2))=Source.radius z.1 z.2 2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.radius]; ring
private theorem hRadius2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hRadius2Denominator=true := by kernel_decide
private theorem hRadius2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hRadius2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hRadius2Denominator hRadius2DenCheck hz.1 hz.2).ne'
private theorem hRadius2Cross : equalCheck
    (mul hRadius2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hRadius2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hRadius2Numerator) hRadius2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hRadius2. -/
def hRadius2Code : RationalCode Source.domain (fun z => Source.radius z.1 z.2 2) :=
  (hRadius2Raw.congr hRadius2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius2Denominator)
    hRadius2DenNonzero hRadius2Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst078Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst078Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst078Raw : RationalCode Source.domain (fun z => (z.1)^4) :=
  ((RationalCode.first Source.domain).pow 4)
private theorem hAst078DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst078Denominator=true := by kernel_decide
private theorem hAst078DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst078Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst078Denominator hAst078DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst078Cross : equalCheck
    (mul hAst078Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst078Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst078Numerator) hAst078Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst078Code : RationalCode Source.domain (fun z => (z.1)^4) :=
  hAst078Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst078Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst078Denominator)
    hAst078DenNonzero hAst078Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst079Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst079Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst079Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^4)) :=
  ((RationalCode.constant Source.domain (-1)).add hAst078Code)
private theorem hAst079DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst079Denominator=true := by kernel_decide
private theorem hAst079DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst079Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst079Denominator hAst079DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst079Cross : equalCheck
    (mul hAst079Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst079Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst079Numerator) hAst079Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst079Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^4)) :=
  hAst079Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst079Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst079Denominator)
    hAst079DenNonzero hAst079Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst080Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,1,0,-1,0,-1],[0,2,-2,-2,4,-2,-2,2],[1,0,1,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst080Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,8,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst080Raw : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^4))) :=
  (hValueCode.mul hAst079Code)
private theorem hAst080DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst080Denominator=true := by kernel_decide
private theorem hAst080DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst080Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst080Denominator hAst080DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst080Cross : equalCheck
    (mul hAst080Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst080Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst080Numerator) hAst080Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst080Code : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^4))) :=
  hAst080Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst080Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst080Denominator)
    hAst080DenNonzero hAst080Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst081Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,3,0,2,0,3],[0],[2,0,4,0,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst081Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst081Raw : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2))) :=
  (hDRealCode.add hGradientReal2Code)
private theorem hAst081DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst081Denominator=true := by kernel_decide
private theorem hAst081DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst081Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst081Denominator hAst081DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst081Cross : equalCheck
    (mul hAst081Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst081Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst081Numerator) hAst081Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst081Code : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2))) :=
  hAst081Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst081Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst081Denominator)
    hAst081DenNonzero hAst081Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst082Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,1,0,1,0,3],[0],[1,0,2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst082Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst082Raw : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2))+(Source.multiplierReal z.1 z.2))) :=
  (hAst081Code.add hSRealCode)
private theorem hAst082DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst082Denominator=true := by kernel_decide
private theorem hAst082DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst082Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst082Denominator hAst082DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst082Cross : equalCheck
    (mul hAst082Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst082Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst082Numerator) hAst082Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst082Code : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2))+(Source.multiplierReal z.1 z.2))) :=
  hAst082Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst082Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst082Denominator)
    hAst082DenNonzero hAst082Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst083Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst083Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst083Raw : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))) :=
  ((RationalCode.constant Source.domain (-1/2)).mul hAst066Code)
private theorem hAst083DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst083Denominator=true := by kernel_decide
private theorem hAst083DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst083Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst083Denominator hAst083DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst083Cross : equalCheck
    (mul hAst083Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst083Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst083Numerator) hAst083Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst083Code : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))) :=
  hAst083Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst083Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst083Denominator)
    hAst083DenNonzero hAst083Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst084Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-2,0,3,0,6,0,11,0,4,0,3],[0],[1,0,5,0,8,0,6,0,3,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst084Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,20,0,40,0,40,0,20,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst084Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2))+(Source.multiplierReal z.1 z.2)))) :=
  (hAst083Code.mul hAst082Code)
private theorem hAst084DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst084Denominator=true := by kernel_decide
private theorem hAst084DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst084Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst084Denominator hAst084DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst084Cross : equalCheck
    (mul hAst084Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst084Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst084Numerator) hAst084Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst084Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2))+(Source.multiplierReal z.1 z.2)))) :=
  hAst084Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst084Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst084Denominator)
    hAst084DenNonzero hAst084Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst085Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,2,0,-1],[0],[1,0,3,0,3,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst085Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst085Raw : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 2))) :=
  (hDImagCode.add hGradientImag2Code)
private theorem hAst085DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst085Denominator=true := by kernel_decide
private theorem hAst085DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst085Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst085Denominator hAst085DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst085Cross : equalCheck
    (mul hAst085Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst085Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst085Numerator) hAst085Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst085Code : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 2))) :=
  hAst085Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst085Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst085Denominator)
    hAst085DenNonzero hAst085Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst086Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1,0,3,0,-1],[0],[1,0,2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst086Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst086Raw : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 2))+(Source.multiplierImag z.1 z.2))) :=
  (hAst085Code.add hSImagCode)
private theorem hAst086DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst086Denominator=true := by kernel_decide
private theorem hAst086DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst086Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst086Denominator hAst086DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst086Cross : equalCheck
    (mul hAst086Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst086Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst086Numerator) hAst086Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst086Code : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 2))+(Source.multiplierImag z.1 z.2))) :=
  hAst086Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst086Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst086Denominator)
    hAst086DenNonzero hAst086Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst087Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst087Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst087Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))) :=
  (hAst040Code.mul hPowerImag2Code)
private theorem hAst087DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst087Denominator=true := by kernel_decide
private theorem hAst087DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst087Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst087Denominator hAst087DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst087Cross : equalCheck
    (mul hAst087Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst087Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst087Numerator) hAst087Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst087Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))) :=
  hAst087Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst087Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst087Denominator)
    hAst087DenNonzero hAst087Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst088Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,2,0,5,0,3,0,2,0,-1],[0],[0,0,0,0,1,0,3,0,4,0,3,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst088Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst088Raw : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 2))+(Source.multiplierImag z.1 z.2)))) :=
  (hAst087Code.mul hAst086Code)
private theorem hAst088DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst088Denominator=true := by kernel_decide
private theorem hAst088DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst088Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst088Denominator hAst088DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst088Cross : equalCheck
    (mul hAst088Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst088Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst088Numerator) hAst088Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst088Code : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 2))+(Source.multiplierImag z.1 z.2)))) :=
  hAst088Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst088Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst088Denominator)
    hAst088DenNonzero hAst088Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst089Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,2,0,8,0,6,0,6,0,0,0,2],[0,2,-2,4,-2,-2,4,-8,4,-2,-2,4,-2,2],[2,0,9,0,13,0,6,0,-2,0,-3,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst089Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,20,0,40,0,40,0,20,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst089Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^4))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2))+(Source.multiplierReal z.1 z.2))))) :=
  (hAst080Code.add hAst084Code)
private theorem hAst089DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst089Denominator=true := by kernel_decide
private theorem hAst089DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst089Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst089Denominator hAst089DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst089Cross : equalCheck
    (mul hAst089Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst089Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst089Numerator) hAst089Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst089Code : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^4))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2))+(Source.multiplierReal z.1 z.2))))) :=
  hAst089Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst089Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst089Denominator)
    hAst089DenNonzero hAst089Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst090Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,4,0,4,0,4],[0,2,-2,0,2,-4,2,0,-2,2],[2,0,5,0,3,0,1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst090Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst090Raw : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^4))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 2))+(Source.multiplierImag z.1 z.2))))) :=
  (hAst089Code.add hAst088Code)
private theorem hAst090DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst090Denominator=true := by kernel_decide
private theorem hAst090DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst090Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst090Denominator hAst090DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst090Cross : equalCheck
    (mul hAst090Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst090Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst090Numerator) hAst090Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst090Code : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^4))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 2))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 2))+(Source.multiplierImag z.1 z.2))))) :=
  hAst090Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst090Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst090Denominator)
    hAst090DenNonzero hAst090Cross

/-- Article: proposed exact numerator for hDiscrepancy2. -/
def hDiscrepancy2Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,4,0,4,0,4],[0,2,-2,0,2,-4,2,0,-2,2],[2,0,5,0,3,0,1,0,1]]
/-- Article: proposed positive denominator for hDiscrepancy2. -/
def hDiscrepancy2Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDiscrepancy2Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^4))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 2)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 2)+(Source.multiplierImag z.1 z.2))))) :=
  (hAst090Code.congr (by
    intro z hz
    ring))
private theorem hDiscrepancy2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^4))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 2))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 2)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 2)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 2)+(Source.multiplierImag z.1 z.2))))=Source.discrepancy z.1 z.2 2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.discrepancy]; ring
private theorem hDiscrepancy2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDiscrepancy2Denominator=true := by kernel_decide
private theorem hDiscrepancy2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDiscrepancy2Denominator hDiscrepancy2DenCheck hz.1 hz.2).ne'
private theorem hDiscrepancy2Cross : equalCheck
    (mul hDiscrepancy2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy2Numerator) hDiscrepancy2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDiscrepancy2. -/
def hDiscrepancy2Code : RationalCode Source.domain (fun z => Source.discrepancy z.1 z.2 2) :=
  (hDiscrepancy2Raw.congr hDiscrepancy2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy2Denominator)
    hDiscrepancy2DenNonzero hDiscrepancy2Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst091Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-4,0,-4,0,-4],[0,-2,2,0,-2,4,-2,0,2,-2],[-2,0,-5,0,-3,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst091Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst091Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 2))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDiscrepancy2Code)
private theorem hAst091DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst091Denominator=true := by kernel_decide
private theorem hAst091DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst091Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst091Denominator hAst091DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst091Cross : equalCheck
    (mul hAst091Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst091Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst091Numerator) hAst091Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst091Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 2))) :=
  hAst091Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst091Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst091Denominator)
    hAst091DenNonzero hAst091Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst092Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-6,0,-6,0,-5,0,-1],[0],[20,0,72,0,90,0,54,0,30,0,6],[0],[31,0,90,0,86,0,26,0,-1],[0],[16,0,48,0,48,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst092Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst092Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 2)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)) :=
  (hRadius2Code.add hAst047Code)
private theorem hAst092DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst092Denominator=true := by kernel_decide
private theorem hAst092DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst092Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst092Denominator hAst092DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst092Cross : equalCheck
    (mul hAst092Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst092Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst092Numerator) hAst092Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst092Code : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 2)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)) :=
  hAst092Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst092Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst092Denominator)
    hAst092DenNonzero hAst092Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst093Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-6,0,-6,0,-5,0,-1],[0,0,0,0,-16,0,-16,0,-16],[20,-8,80,0,82,16,46,0,38,-8,6],[-8,0,-20,0,-12,0,-4,0,-4],[31,0,90,0,86,0,26,0,-1],[0],[16,0,48,0,48,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst093Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst093Raw : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 2)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 2)))) :=
  (hAst092Code.add hAst091Code)
private theorem hAst093DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst093Denominator=true := by kernel_decide
private theorem hAst093DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst093Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst093Denominator hAst093DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst093Cross : equalCheck
    (mul hAst093Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst093Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst093Numerator) hAst093Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst093Code : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 2)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 2)))) :=
  hAst093Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst093Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst093Denominator)
    hAst093DenNonzero hAst093Cross

/-- Article: proposed exact numerator for hPairLower2. -/
def hPairLower2Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-6,0,-6,0,-5,0,-1],[0,0,0,0,-16,0,-16,0,-16],[20,-8,80,0,82,16,46,0,38,-8,6],[-8,0,-20,0,-12,0,-4,0,-4],[31,0,90,0,86,0,26,0,-1],[0],[16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for hPairLower2. -/
def hPairLower2Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairLower2Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 2)+((((1 : ℚ) : ℝ)+(z.2)^2))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 2)))) :=
  (hAst093Code.congr (by
    intro z hz
    ring))
private theorem hPairLower2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.radius z.1 z.2 2)+((((1 : ℚ) : ℝ)+(z.2)^2))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 2)))=Source.pairSlack z.1 z.2 (-1) 2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairLower2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairLower2Denominator=true := by kernel_decide
private theorem hPairLower2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairLower2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairLower2Denominator hPairLower2DenCheck hz.1 hz.2).ne'
private theorem hPairLower2Cross : equalCheck
    (mul hPairLower2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairLower2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairLower2Numerator) hPairLower2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairLower2. -/
def hPairLower2Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (-1) 2) :=
  (hPairLower2Raw.congr hPairLower2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower2Denominator)
    hPairLower2DenNonzero hPairLower2Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst094Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-6,0,-6,0,-5,0,-1],[0,0,0,0,16,0,16,0,16],[4,8,16,0,50,-16,46,0,22,8,6],[8,0,20,0,12,0,4,0,4],[-1,0,-6,0,-10,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst094Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst094Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 2)+(Source.radius z.1 z.2 2))) :=
  (hDiscrepancy2Code.add hRadius2Code)
private theorem hAst094DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst094Denominator=true := by kernel_decide
private theorem hAst094DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst094Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst094Denominator hAst094DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst094Cross : equalCheck
    (mul hAst094Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst094Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst094Numerator) hAst094Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst094Code : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 2)+(Source.radius z.1 z.2 2))) :=
  hAst094Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst094Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst094Denominator)
    hAst094DenNonzero hAst094Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst095Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-6,0,-6,0,-5,0,-1],[0,0,0,0,16,0,16,0,16],[20,8,64,0,98,-16,62,0,22,8,6],[8,0,20,0,12,0,4,0,4],[31,0,90,0,86,0,26,0,-1],[0],[16,0,48,0,48,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst095Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst095Raw : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 2)+(Source.radius z.1 z.2 2))+((((1 : ℚ) : ℝ)+(z.2)^2))^2)) :=
  (hAst094Code.add hAst047Code)
private theorem hAst095DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst095Denominator=true := by kernel_decide
private theorem hAst095DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst095Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst095Denominator hAst095DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst095Cross : equalCheck
    (mul hAst095Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst095Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst095Numerator) hAst095Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst095Code : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 2)+(Source.radius z.1 z.2 2))+((((1 : ℚ) : ℝ)+(z.2)^2))^2)) :=
  hAst095Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst095Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst095Denominator)
    hAst095DenNonzero hAst095Cross

/-- Article: proposed exact numerator for hPairUpper2. -/
def hPairUpper2Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-6,0,-6,0,-5,0,-1],[0,0,0,0,16,0,16,0,16],[20,8,64,0,98,-16,62,0,22,8,6],[8,0,20,0,12,0,4,0,4],[31,0,90,0,86,0,26,0,-1],[0],[16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for hPairUpper2. -/
def hPairUpper2Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairUpper2Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 2)+(Source.radius z.1 z.2 2)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)) :=
  (hAst095Code.congr (by
    intro z hz
    ring))
private theorem hPairUpper2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.discrepancy z.1 z.2 2)+(Source.radius z.1 z.2 2)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)=Source.pairSlack z.1 z.2 (1) 2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairUpper2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairUpper2Denominator=true := by kernel_decide
private theorem hPairUpper2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairUpper2Denominator hPairUpper2DenCheck hz.1 hz.2).ne'
private theorem hPairUpper2Cross : equalCheck
    (mul hPairUpper2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper2Numerator) hPairUpper2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairUpper2. -/
def hPairUpper2Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (1) 2) :=
  (hPairUpper2Raw.congr hPairUpper2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper2Denominator)
    hPairUpper2DenNonzero hPairUpper2Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst096Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst096Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst096Raw : RationalCode Source.domain (fun z => (z.1)^3) :=
  ((RationalCode.first Source.domain).pow 3)
private theorem hAst096DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst096Denominator=true := by kernel_decide
private theorem hAst096DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst096Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst096Denominator hAst096DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst096Cross : equalCheck
    (mul hAst096Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst096Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst096Numerator) hAst096Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst096Code : RationalCode Source.domain (fun z => (z.1)^3) :=
  hAst096Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst096Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst096Denominator)
    hAst096DenNonzero hAst096Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst097Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,3,0,2,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst097Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst097Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 3 (radialCosine z.1))*(z.1)^3)) :=
  (hT3Code.mul hAst096Code)
private theorem hAst097DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst097Denominator=true := by kernel_decide
private theorem hAst097DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst097Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst097Denominator hAst097DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst097Cross : equalCheck
    (mul hAst097Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst097Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst097Numerator) hAst097Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst097Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 3 (radialCosine z.1))*(z.1)^3)) :=
  hAst097Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst097Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst097Denominator)
    hAst097DenNonzero hAst097Cross

/-- Article: proposed exact numerator for hPowerReal3. -/
def hPowerReal3Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,3,0,2,0,3]]
/-- Article: proposed positive denominator for hPowerReal3. -/
def hPowerReal3Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerReal3Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 3 (radialCosine z.1))*(z.1)^3)) :=
  (hAst097Code.congr (by
    intro z hz
    ring))
private theorem hPowerReal3Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebT 3 (radialCosine z.1))*(z.1)^3)=Source.powerReal z.1 3 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.powerReal]; ring
private theorem hPowerReal3DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerReal3Denominator=true := by kernel_decide
private theorem hPowerReal3DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal3Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerReal3Denominator hPowerReal3DenCheck hz.1 hz.2).ne'
private theorem hPowerReal3Cross : equalCheck
    (mul hPowerReal3Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal3Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal3Numerator) hPowerReal3Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerReal3. -/
def hPowerReal3Code : RationalCode Source.domain (fun z => Source.powerReal z.1 3) :=
  (hPowerReal3Raw.congr hPowerReal3Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal3Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal3Denominator)
    hPowerReal3DenNonzero hPowerReal3Cross

end
end polyak.Certificates.Startup.Codes
