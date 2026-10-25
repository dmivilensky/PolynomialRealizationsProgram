import polyak.Certificates.Startup.Code04

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: proposed exact numerator for hResidueUpper0. -/
def hResidueUpper0Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,-8,7,-8],[0,0,-4,0,-6,0,-2],[-1,0,-3,0,-2]]
/-- Article: proposed positive denominator for hResidueUpper0. -/
def hResidueUpper0Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,16,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hResidueUpper0Raw : RationalCode Source.domain (fun z => (Source.betaReal z.1 z.2 (1))) :=
  hBetaRealUpperCode
private theorem hResidueUpper0Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.betaReal z.1 z.2 (1))=Source.residue z.1 z.2 (1) 0 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem hResidueUpper0DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hResidueUpper0Denominator=true := by kernel_decide
private theorem hResidueUpper0DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper0Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hResidueUpper0Denominator hResidueUpper0DenCheck hz.1 hz.2).ne'
private theorem hResidueUpper0Cross : equalCheck
    (mul hResidueUpper0Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper0Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper0Numerator) hResidueUpper0Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hResidueUpper0. -/
def hResidueUpper0Code : RationalCode Source.domain (fun z => Source.residue z.1 z.2 (1) 0) :=
  (hResidueUpper0Raw.congr hResidueUpper0Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper0Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper0Denominator)
    hResidueUpper0DenNonzero hResidueUpper0Cross

/-- Article: proposed exact numerator for hResidueUpper1. -/
def hResidueUpper1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-8,4,-8,-3,-8,4,-8,-1],[-2,0,0,0,2],[2,0,5,0,4,0,1]]
/-- Article: proposed positive denominator for hResidueUpper1. -/
def hResidueUpper1Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,8,0,24,0,24,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hResidueUpper1Raw : RationalCode Source.domain (fun z => (((Source.betaReal z.1 z.2 (1))*(polyak.Spectral.chebT 1 (radialCosine z.1)))+((((-1) : ℚ) : ℝ)*(Source.betaImag z.1 z.2 (1))*(Source.imaginarySquare z.1)*(polyak.Spectral.chebU 0 (radialCosine z.1))*(z.1)⁻¹))) :=
  ((hBetaRealUpperCode.mul hT1Code).add (((((RationalCode.constant Source.domain (-1)).mul hBetaImagUpperCode).mul hImSqCode).mul hU0Code).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))))
private theorem hResidueUpper1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.betaReal z.1 z.2 (1))*(polyak.Spectral.chebT 1 (radialCosine z.1)))+((((-1) : ℚ) : ℝ)*(Source.betaImag z.1 z.2 (1))*(Source.imaginarySquare z.1)*(polyak.Spectral.chebU 0 (radialCosine z.1))*(z.1)⁻¹))=Source.residue z.1 z.2 (1) 1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.residue,ite_eq_right (by decide)]; ring
private theorem hResidueUpper1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hResidueUpper1Denominator=true := by kernel_decide
private theorem hResidueUpper1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hResidueUpper1Denominator hResidueUpper1DenCheck hz.1 hz.2).ne'
private theorem hResidueUpper1Cross : equalCheck
    (mul hResidueUpper1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper1Numerator) hResidueUpper1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hResidueUpper1. -/
def hResidueUpper1Code : RationalCode Source.domain (fun z => Source.residue z.1 z.2 (1) 1) :=
  (hResidueUpper1Raw.congr hResidueUpper1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper1Denominator)
    hResidueUpper1DenNonzero hResidueUpper1Cross

/-- Article: proposed exact numerator for hResidueUpper2. -/
def hResidueUpper2Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,24,-17,40,-9,40,-15,24,2],[0,0,8,0,14,0,14,0,10,0,2],[1,0,1,0,-1,0,-1]]
/-- Article: proposed positive denominator for hResidueUpper2. -/
def hResidueUpper2Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,32,0,48,0,32,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hResidueUpper2Raw : RationalCode Source.domain (fun z => (((Source.betaReal z.1 z.2 (1))*(polyak.Spectral.chebT 2 (radialCosine z.1)))+((((-1) : ℚ) : ℝ)*(Source.betaImag z.1 z.2 (1))*(Source.imaginarySquare z.1)*(polyak.Spectral.chebU 1 (radialCosine z.1))*(z.1)⁻¹))) :=
  ((hBetaRealUpperCode.mul hT2Code).add (((((RationalCode.constant Source.domain (-1)).mul hBetaImagUpperCode).mul hImSqCode).mul hU1Code).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))))
private theorem hResidueUpper2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.betaReal z.1 z.2 (1))*(polyak.Spectral.chebT 2 (radialCosine z.1)))+((((-1) : ℚ) : ℝ)*(Source.betaImag z.1 z.2 (1))*(Source.imaginarySquare z.1)*(polyak.Spectral.chebU 1 (radialCosine z.1))*(z.1)⁻¹))=Source.residue z.1 z.2 (1) 2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.residue,ite_eq_right (by decide)]; ring
private theorem hResidueUpper2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hResidueUpper2Denominator=true := by kernel_decide
private theorem hResidueUpper2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hResidueUpper2Denominator hResidueUpper2DenCheck hz.1 hz.2).ne'
private theorem hResidueUpper2Cross : equalCheck
    (mul hResidueUpper2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper2Numerator) hResidueUpper2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hResidueUpper2. -/
def hResidueUpper2Code : RationalCode Source.domain (fun z => Source.residue z.1 z.2 (1) 2) :=
  (hResidueUpper2Raw.congr hResidueUpper2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueUpper2Denominator)
    hResidueUpper2DenNonzero hResidueUpper2Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst000Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst000Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst000Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 1 (radialCosine z.1))*z.1)) :=
  (hT1Code.mul (RationalCode.first Source.domain))
private theorem hAst000DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst000Denominator=true := by kernel_decide
private theorem hAst000DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst000Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst000Denominator hAst000DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst000Cross : equalCheck
    (mul hAst000Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst000Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst000Numerator) hAst000Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst000Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 1 (radialCosine z.1))*z.1)) :=
  hAst000Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst000Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst000Denominator)
    hAst000DenNonzero hAst000Cross

/-- Article: proposed exact numerator for hPowerReal1. -/
def hPowerReal1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1]]
/-- Article: proposed positive denominator for hPowerReal1. -/
def hPowerReal1Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerReal1Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 1 (radialCosine z.1))*z.1)) :=
  (hAst000Code.congr (by
    intro z hz
    ring))
private theorem hPowerReal1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebT 1 (radialCosine z.1))*z.1)=Source.powerReal z.1 1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.powerReal]; ring
private theorem hPowerReal1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerReal1Denominator=true := by kernel_decide
private theorem hPowerReal1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerReal1Denominator hPowerReal1DenCheck hz.1 hz.2).ne'
private theorem hPowerReal1Cross : equalCheck
    (mul hPowerReal1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal1Numerator) hPowerReal1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerReal1. -/
def hPowerReal1Code : RationalCode Source.domain (fun z => Source.powerReal z.1 1) :=
  (hPowerReal1Raw.congr hPowerReal1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal1Denominator)
    hPowerReal1DenNonzero hPowerReal1Cross

/-- Article: proposed exact numerator for hPowerImag1. -/
def hPowerImag1Numerator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: proposed positive denominator for hPowerImag1. -/
def hPowerImag1Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerImag1Raw : RationalCode Source.domain (fun z => (polyak.Spectral.chebU 0 (radialCosine z.1))) :=
  (hU0Code.congr (by
    intro z hz
    ring))
private theorem hPowerImag1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (polyak.Spectral.chebU 0 (radialCosine z.1))=Source.powerImag z.1 1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.powerImag,ite_eq_right (by decide)]; ring
private theorem hPowerImag1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerImag1Denominator=true := by kernel_decide
private theorem hPowerImag1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerImag1Denominator hPowerImag1DenCheck hz.1 hz.2).ne'
private theorem hPowerImag1Cross : equalCheck
    (mul hPowerImag1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag1Numerator) hPowerImag1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerImag1. -/
def hPowerImag1Code : RationalCode Source.domain (fun z => Source.powerImag z.1 1) :=
  (hPowerImag1Raw.congr hPowerImag1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag1Denominator)
    hPowerImag1DenNonzero hPowerImag1Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst001Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1],[0],[0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst001Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst001Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 1)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerReal1Code.mul hSRealCode)
private theorem hAst001DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst001Denominator=true := by kernel_decide
private theorem hAst001DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst001Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst001Denominator hAst001DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst001Cross : equalCheck
    (mul hAst001Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst001Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst001Numerator) hAst001Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst001Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 1)*(Source.multiplierReal z.1 z.2))) :=
  hAst001Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst001Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst001Denominator)
    hAst001DenNonzero hAst001Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst002Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst002Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst002Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))) :=
  ((RationalCode.constant Source.domain (-1)).mul hImSqCode)
private theorem hAst002DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst002Denominator=true := by kernel_decide
private theorem hAst002DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst002Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst002Denominator hAst002DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst002Cross : equalCheck
    (mul hAst002Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst002Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst002Numerator) hAst002Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst002Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))) :=
  hAst002Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst002Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst002Denominator)
    hAst002DenNonzero hAst002Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst003Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst003Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst003Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))) :=
  (hAst002Code.mul hPowerImag1Code)
private theorem hAst003DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst003Denominator=true := by kernel_decide
private theorem hAst003DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst003Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst003Denominator hAst003DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst003Cross : equalCheck
    (mul hAst003Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst003Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst003Numerator) hAst003Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst003Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))) :=
  hAst003Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst003Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst003Denominator)
    hAst003DenNonzero hAst003Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst004Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-1,0,-1],[0],[1,0,1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst004Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst004Raw : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))*(Source.multiplierImag z.1 z.2))) :=
  (hAst003Code.mul hSImagCode)
private theorem hAst004DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst004Denominator=true := by kernel_decide
private theorem hAst004DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst004Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst004Denominator hAst004DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst004Cross : equalCheck
    (mul hAst004Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst004Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst004Numerator) hAst004Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst004Code : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))*(Source.multiplierImag z.1 z.2))) :=
  hAst004Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst004Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst004Denominator)
    hAst004DenNonzero hAst004Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst005Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,0,0,-1],[0],[1,0,2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst005Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst005Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 1)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))*(Source.multiplierImag z.1 z.2)))) :=
  (hAst001Code.add hAst004Code)
private theorem hAst005DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst005Denominator=true := by kernel_decide
private theorem hAst005DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst005Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst005Denominator hAst005DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst005Cross : equalCheck
    (mul hAst005Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst005Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst005Numerator) hAst005Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst005Code : RationalCode Source.domain (fun z => (((Source.powerReal z.1 1)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))*(Source.multiplierImag z.1 z.2)))) :=
  hAst005Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst005Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst005Denominator)
    hAst005DenNonzero hAst005Cross

/-- Article: proposed exact numerator for hGradientReal1. -/
def hGradientReal1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,0,0,-1],[0],[1,0,2,0,1]]
/-- Article: proposed positive denominator for hGradientReal1. -/
def hGradientReal1Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientReal1Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 1)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 1)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst005Code.congr (by
    intro z hz
    ring))
private theorem hGradientReal1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerReal z.1 1)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 1)*(Source.multiplierImag z.1 z.2)))=Source.gradientReal z.1 z.2 1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientReal]; ring
private theorem hGradientReal1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientReal1Denominator=true := by kernel_decide
private theorem hGradientReal1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientReal1Denominator hGradientReal1DenCheck hz.1 hz.2).ne'
private theorem hGradientReal1Cross : equalCheck
    (mul hGradientReal1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal1Numerator) hGradientReal1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientReal1. -/
def hGradientReal1Code : RationalCode Source.domain (fun z => Source.gradientReal z.1 z.2 1) :=
  (hGradientReal1Raw.congr hGradientReal1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal1Denominator)
    hGradientReal1DenNonzero hGradientReal1Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst006Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1],[0],[-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst006Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst006Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 1)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerImag1Code.mul hSRealCode)
private theorem hAst006DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst006Denominator=true := by kernel_decide
private theorem hAst006DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst006Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst006Denominator hAst006DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst006Cross : equalCheck
    (mul hAst006Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst006Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst006Numerator) hAst006Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst006Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 1)*(Source.multiplierReal z.1 z.2))) :=
  hAst006Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst006Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst006Denominator)
    hAst006DenNonzero hAst006Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst007Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst007Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst007Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 1)*(Source.multiplierImag z.1 z.2))) :=
  (hPowerReal1Code.mul hSImagCode)
private theorem hAst007DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst007Denominator=true := by kernel_decide
private theorem hAst007DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst007Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst007Denominator hAst007DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst007Cross : equalCheck
    (mul hAst007Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst007Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst007Numerator) hAst007Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst007Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 1)*(Source.multiplierImag z.1 z.2))) :=
  hAst007Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst007Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst007Denominator)
    hAst007DenNonzero hAst007Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst008Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst008Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst008Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 1)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 1)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst006Code.add hAst007Code)
private theorem hAst008DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst008Denominator=true := by kernel_decide
private theorem hAst008DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst008Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst008Denominator hAst008DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst008Cross : equalCheck
    (mul hAst008Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst008Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst008Numerator) hAst008Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst008Code : RationalCode Source.domain (fun z => (((Source.powerImag z.1 1)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 1)*(Source.multiplierImag z.1 z.2)))) :=
  hAst008Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst008Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst008Denominator)
    hAst008DenNonzero hAst008Cross

/-- Article: proposed exact numerator for hGradientImag1. -/
def hGradientImag1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1]]
/-- Article: proposed positive denominator for hGradientImag1. -/
def hGradientImag1Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientImag1Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 1)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 1)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst008Code.congr (by
    intro z hz
    ring))
private theorem hGradientImag1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerImag z.1 1)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 1)*(Source.multiplierImag z.1 z.2)))=Source.gradientImag z.1 z.2 1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientImag]; ring
private theorem hGradientImag1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientImag1Denominator=true := by kernel_decide
private theorem hGradientImag1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientImag1Denominator hGradientImag1DenCheck hz.1 hz.2).ne'
private theorem hGradientImag1Cross : equalCheck
    (mul hGradientImag1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag1Numerator) hGradientImag1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientImag1. -/
def hGradientImag1Code : RationalCode Source.domain (fun z => Source.gradientImag z.1 z.2 1) :=
  (hGradientImag1Raw.congr hGradientImag1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag1Denominator)
    hGradientImag1DenNonzero hGradientImag1Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst009Numerator : polyak.Numerics.IntegerBivariate.Source := [[0],[-2,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst009Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst009Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDRealCode)
private theorem hAst009DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst009Denominator=true := by kernel_decide
private theorem hAst009DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst009Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst009Denominator hAst009DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst009Cross : equalCheck
    (mul hAst009Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst009Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst009Numerator) hAst009Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst009Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))) :=
  hAst009Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst009Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst009Denominator)
    hAst009DenNonzero hAst009Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst010Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst010Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst010Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))) :=
  ((RationalCode.constant Source.domain (-1)).mul hSRealCode)
private theorem hAst010DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst010Denominator=true := by kernel_decide
private theorem hAst010DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst010Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst010Denominator hAst010DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst010Cross : equalCheck
    (mul hAst010Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst010Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst010Numerator) hAst010Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst010Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))) :=
  hAst010Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst010Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst010Denominator)
    hAst010DenNonzero hAst010Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst011Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,0,0,-1],[0],[-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst011Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst011Raw : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  (hGradientReal1Code.add hAst009Code)
private theorem hAst011DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst011Denominator=true := by kernel_decide
private theorem hAst011DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst011Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst011Denominator hAst011DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst011Cross : equalCheck
    (mul hAst011Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst011Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst011Numerator) hAst011Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst011Code : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  hAst011Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst011Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst011Denominator)
    hAst011DenNonzero hAst011Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst012Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst012Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst012Raw : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  (hAst011Code.add hAst010Code)
private theorem hAst012DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst012Denominator=true := by kernel_decide
private theorem hAst012DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst012Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst012Denominator hAst012DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst012Cross : equalCheck
    (mul hAst012Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst012Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst012Numerator) hAst012Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst012Code : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  hAst012Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst012Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst012Denominator)
    hAst012DenNonzero hAst012Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst013Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst013Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,16,0,24,0,16,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst013Raw : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  (hAst012Code.pow 2)
private theorem hAst013DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst013Denominator=true := by kernel_decide
private theorem hAst013DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst013Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst013Denominator hAst013DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst013Cross : equalCheck
    (mul hAst013Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst013Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst013Numerator) hAst013Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst013Code : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  hAst013Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst013Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst013Denominator)
    hAst013DenNonzero hAst013Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst014Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,-1,0,2,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst014Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst014Raw : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  ((RationalCode.constant Source.domain (-1/4)).mul hAst013Code)
private theorem hAst014DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst014Denominator=true := by kernel_decide
private theorem hAst014DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst014Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst014Denominator hAst014DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst014Cross : equalCheck
    (mul hAst014Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst014Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst014Numerator) hAst014Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst014Code : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  hAst014Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst014Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst014Denominator)
    hAst014DenNonzero hAst014Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst015Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst015Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst015Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1))) :=
  ((RationalCode.constant Source.domain (-1)).add hPowerReal1Code)
private theorem hAst015DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst015Denominator=true := by kernel_decide
private theorem hAst015DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst015Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst015Denominator hAst015DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst015Cross : equalCheck
    (mul hAst015Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst015Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst015Numerator) hAst015Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst015Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1))) :=
  hAst015Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst015Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst015Denominator)
    hAst015DenNonzero hAst015Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst016Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst016Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst016Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2) :=
  (hAst015Code.pow 2)
private theorem hAst016DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst016Denominator=true := by kernel_decide
private theorem hAst016DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst016Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst016Denominator hAst016DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst016Cross : equalCheck
    (mul hAst016Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst016Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst016Numerator) hAst016Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst016Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2) :=
  hAst016Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst016Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst016Denominator)
    hAst016DenNonzero hAst016Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst017Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst017Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,8,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst017Raw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2)) :=
  ((RationalCode.constant Source.domain (1/4)).mul hAst016Code)
private theorem hAst017DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst017Denominator=true := by kernel_decide
private theorem hAst017DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst017Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst017Denominator hAst017DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst017Cross : equalCheck
    (mul hAst017Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst017Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst017Numerator) hAst017Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst017Code : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2)) :=
  hAst017Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst017Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst017Denominator)
    hAst017DenNonzero hAst017Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst018Numerator : polyak.Numerics.IntegerBivariate.Source := [[0],[-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst018Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst018Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDImagCode)
private theorem hAst018DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst018Denominator=true := by kernel_decide
private theorem hAst018DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst018Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst018Denominator hAst018DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst018Cross : equalCheck
    (mul hAst018Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst018Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst018Numerator) hAst018Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst018Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))) :=
  hAst018Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst018Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst018Denominator)
    hAst018DenNonzero hAst018Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst019Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst019Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst019Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))) :=
  ((RationalCode.constant Source.domain (-1)).mul hSImagCode)
private theorem hAst019DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst019Denominator=true := by kernel_decide
private theorem hAst019DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst019Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst019Denominator hAst019DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst019Cross : equalCheck
    (mul hAst019Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst019Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst019Numerator) hAst019Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst019Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))) :=
  hAst019Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst019Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst019Denominator)
    hAst019DenNonzero hAst019Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst020Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-2],[0],[-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst020Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst020Raw : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  (hGradientImag1Code.add hAst018Code)
private theorem hAst020DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst020Denominator=true := by kernel_decide
private theorem hAst020DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst020Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst020Denominator hAst020DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst020Cross : equalCheck
    (mul hAst020Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst020Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst020Numerator) hAst020Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst020Code : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  hAst020Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst020Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst020Denominator)
    hAst020DenNonzero hAst020Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst021Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst021Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst021Raw : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst020Code.add hAst019Code)
private theorem hAst021DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst021Denominator=true := by kernel_decide
private theorem hAst021DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst021Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst021Denominator hAst021DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst021Cross : equalCheck
    (mul hAst021Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst021Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst021Numerator) hAst021Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst021Code : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  hAst021Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst021Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst021Denominator)
    hAst021DenNonzero hAst021Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst022Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst022Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,8,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst022Raw : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  (hAst021Code.pow 2)
private theorem hAst022DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst022Denominator=true := by kernel_decide
private theorem hAst022DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst022Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst022Denominator hAst022DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst022Cross : equalCheck
    (mul hAst022Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst022Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst022Numerator) hAst022Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst022Code : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  hAst022Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst022Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst022Denominator)
    hAst022DenNonzero hAst022Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst023Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst023Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,8,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst023Raw : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))) :=
  ((RationalCode.constant Source.domain (-1/4)).mul hImSqCode)
private theorem hAst023DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst023Denominator=true := by kernel_decide
private theorem hAst023DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst023Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst023Denominator hAst023DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst023Cross : equalCheck
    (mul hAst023Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst023Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst023Numerator) hAst023Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst023Code : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))) :=
  hAst023Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst023Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst023Denominator)
    hAst023DenNonzero hAst023Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst024Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-16,0,-15,0,-9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst024Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst024Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  (hAst023Code.mul hAst022Code)
private theorem hAst024DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst024Denominator=true := by kernel_decide
private theorem hAst024DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst024Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst024Denominator hAst024DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst024Cross : equalCheck
    (mul hAst024Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst024Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst024Numerator) hAst024Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst024Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  hAst024Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst024Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst024Denominator)
    hAst024DenNonzero hAst024Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst025Numerator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst025Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst025Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 1))^2) :=
  (hPowerImag1Code.pow 2)
private theorem hAst025DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst025Denominator=true := by kernel_decide
private theorem hAst025DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst025Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst025Denominator hAst025DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst025Cross : equalCheck
    (mul hAst025Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst025Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst025Numerator) hAst025Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst025Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 1))^2) :=
  hAst025Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst025Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst025Denominator)
    hAst025DenNonzero hAst025Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst026Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst026Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,8,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst026Raw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))) :=
  ((RationalCode.constant Source.domain (1/4)).mul hImSqCode)
private theorem hAst026DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst026Denominator=true := by kernel_decide
private theorem hAst026DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst026Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst026Denominator hAst026DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst026Cross : equalCheck
    (mul hAst026Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst026Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst026Numerator) hAst026Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst026Code : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))) :=
  hAst026Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst026Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst026Denominator)
    hAst026DenNonzero hAst026Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst027Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst027Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,8,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst027Raw : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 1))^2)) :=
  (hAst026Code.mul hAst025Code)
private theorem hAst027DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst027Denominator=true := by kernel_decide
private theorem hAst027DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst027Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst027Denominator hAst027DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst027Cross : equalCheck
    (mul hAst027Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst027Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst027Numerator) hAst027Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst027Code : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 1))^2)) :=
  hAst027Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst027Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst027Denominator)
    hAst027DenNonzero hAst027Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst028Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,-1,0,2,0,-1],[0],[4,0,24,0,52,0,48,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst028Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst028Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2))) :=
  (hAst014Code.add hAst017Code)
private theorem hAst028DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst028Denominator=true := by kernel_decide
private theorem hAst028DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst028Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst028Denominator hAst028DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst028Cross : equalCheck
    (mul hAst028Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst028Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst028Numerator) hAst028Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst028Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2))) :=
  hAst028Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst028Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst028Denominator)
    hAst028DenNonzero hAst028Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst029Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-5,0,-1],[0],[4,0,16,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst029Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,32,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst029Raw : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  (hAst028Code.add hAst024Code)
private theorem hAst029DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst029Denominator=true := by kernel_decide
private theorem hAst029DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst029Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst029Denominator hAst029DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst029Cross : equalCheck
    (mul hAst029Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst029Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst029Numerator) hAst029Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst029Code : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  hAst029Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst029Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst029Denominator)
    hAst029DenNonzero hAst029Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst030Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,-1],[0],[4,0,16,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst030Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst030Raw : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 1))^2))) :=
  (hAst029Code.add hAst027Code)
private theorem hAst030DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst030Denominator=true := by kernel_decide
private theorem hAst030DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst030Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst030Denominator hAst030DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst030Cross : equalCheck
    (mul hAst030Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst030Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst030Numerator) hAst030Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst030Code : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 1))^2))) :=
  hAst030Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst030Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst030Denominator)
    hAst030DenNonzero hAst030Cross

/-- Article: proposed exact numerator for hRadius1. -/
def hRadius1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,-1],[0],[4,0,16,0,4]]
/-- Article: proposed positive denominator for hRadius1. -/
def hRadius1Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hRadius1Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 1))^2))) :=
  (hAst030Code.congr (by
    intro z hz
    ring))
private theorem hRadius1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 1)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 1))^2))=Source.radius z.1 z.2 1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.radius]; ring
private theorem hRadius1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hRadius1Denominator=true := by kernel_decide
private theorem hRadius1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hRadius1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hRadius1Denominator hRadius1DenCheck hz.1 hz.2).ne'
private theorem hRadius1Cross : equalCheck
    (mul hRadius1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hRadius1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hRadius1Numerator) hRadius1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hRadius1. -/
def hRadius1Code : RationalCode Source.domain (fun z => Source.radius z.1 z.2 1) :=
  (hRadius1Raw.congr hRadius1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius1Denominator)
    hRadius1DenNonzero hRadius1Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst031Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst031Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst031Raw : RationalCode Source.domain (fun z => (z.1)^2) :=
  ((RationalCode.first Source.domain).pow 2)
private theorem hAst031DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst031Denominator=true := by kernel_decide
private theorem hAst031DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst031Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst031Denominator hAst031DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst031Cross : equalCheck
    (mul hAst031Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst031Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst031Numerator) hAst031Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst031Code : RationalCode Source.domain (fun z => (z.1)^2) :=
  hAst031Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst031Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst031Denominator)
    hAst031DenNonzero hAst031Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst032Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst032Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst032Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^2)) :=
  ((RationalCode.constant Source.domain (-1)).add hAst031Code)
private theorem hAst032DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst032Denominator=true := by kernel_decide
private theorem hAst032DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst032Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst032Denominator hAst032DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst032Cross : equalCheck
    (mul hAst032Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst032Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst032Numerator) hAst032Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst032Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^2)) :=
  hAst032Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst032Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst032Denominator)
    hAst032DenNonzero hAst032Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst033Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,1,0,-1,0,-1],[0,2,-2,-2,4,-2,-2,2],[1,0,1,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst033Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst033Raw : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^2))) :=
  (hValueCode.mul hAst032Code)
private theorem hAst033DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst033Denominator=true := by kernel_decide
private theorem hAst033DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst033Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst033Denominator hAst033DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst033Cross : equalCheck
    (mul hAst033Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst033Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst033Numerator) hAst033Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst033Code : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^2))) :=
  hAst033Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst033Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst033Denominator)
    hAst033DenNonzero hAst033Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst034Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,0,0,-1],[0],[3,0,5,0,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst034Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst034Raw : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1))) :=
  (hDRealCode.add hGradientReal1Code)
private theorem hAst034DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst034Denominator=true := by kernel_decide
private theorem hAst034DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst034Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst034Denominator hAst034DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst034Cross : equalCheck
    (mul hAst034Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst034Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst034Numerator) hAst034Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst034Code : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1))) :=
  hAst034Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst034Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst034Denominator)
    hAst034DenNonzero hAst034Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst035Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2,0,-1,0,-1],[0],[2,0,4,0,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst035Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst035Raw : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1))+(Source.multiplierReal z.1 z.2))) :=
  (hAst034Code.add hSRealCode)
private theorem hAst035DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst035Denominator=true := by kernel_decide
private theorem hAst035DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst035Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst035Denominator hAst035DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst035Cross : equalCheck
    (mul hAst035Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst035Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst035Numerator) hAst035Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst035Code : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1))+(Source.multiplierReal z.1 z.2))) :=
  hAst035Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst035Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst035Denominator)
    hAst035DenNonzero hAst035Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst036Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst036Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst036Raw : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))) :=
  ((RationalCode.constant Source.domain (-1/2)).mul hAst015Code)
private theorem hAst036DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst036Denominator=true := by kernel_decide
private theorem hAst036DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst036Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst036Denominator hAst036DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst036Cross : equalCheck
    (mul hAst036Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst036Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst036Numerator) hAst036Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst036Code : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))) :=
  hAst036Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst036Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst036Denominator)
    hAst036DenNonzero hAst036Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst037Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2,0,-5,0,-3,0,-2],[0],[2,0,8,0,10,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst037Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst037Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1))+(Source.multiplierReal z.1 z.2)))) :=
  (hAst036Code.mul hAst035Code)
private theorem hAst037DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst037Denominator=true := by kernel_decide
private theorem hAst037DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst037Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst037Denominator hAst037DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst037Cross : equalCheck
    (mul hAst037Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst037Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst037Numerator) hAst037Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst037Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1))+(Source.multiplierReal z.1 z.2)))) :=
  hAst037Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst037Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst037Denominator)
    hAst037DenNonzero hAst037Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst038Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-2],[0],[1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst038Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst038Raw : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 1))) :=
  (hDImagCode.add hGradientImag1Code)
private theorem hAst038DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst038Denominator=true := by kernel_decide
private theorem hAst038DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst038Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst038Denominator hAst038DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst038Cross : equalCheck
    (mul hAst038Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst038Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst038Numerator) hAst038Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst038Code : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 1))) :=
  hAst038Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst038Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst038Denominator)
    hAst038DenNonzero hAst038Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst039Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst039Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst039Raw : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 1))+(Source.multiplierImag z.1 z.2))) :=
  (hAst038Code.add hSImagCode)
private theorem hAst039DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst039Denominator=true := by kernel_decide
private theorem hAst039DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst039Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst039Denominator hAst039DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst039Cross : equalCheck
    (mul hAst039Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst039Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst039Numerator) hAst039Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst039Code : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 1))+(Source.multiplierImag z.1 z.2))) :=
  hAst039Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst039Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst039Denominator)
    hAst039DenNonzero hAst039Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst040Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst040Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst040Raw : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))) :=
  ((RationalCode.constant Source.domain (-1/2)).mul hImSqCode)
private theorem hAst040DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst040Denominator=true := by kernel_decide
private theorem hAst040DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst040Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst040Denominator hAst040DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst040Cross : equalCheck
    (mul hAst040Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst040Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst040Numerator) hAst040Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst040Code : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))) :=
  hAst040Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst040Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst040Denominator)
    hAst040DenNonzero hAst040Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst041Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst041Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,4,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst041Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))) :=
  (hAst040Code.mul hPowerImag1Code)
private theorem hAst041DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst041Denominator=true := by kernel_decide
private theorem hAst041DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst041Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst041Denominator hAst041DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst041Cross : equalCheck
    (mul hAst041Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst041Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst041Numerator) hAst041Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst041Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))) :=
  hAst041Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst041Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst041Denominator)
    hAst041DenNonzero hAst041Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst042Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst042Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst042Raw : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 1))+(Source.multiplierImag z.1 z.2)))) :=
  (hAst041Code.mul hAst039Code)
private theorem hAst042DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst042Denominator=true := by kernel_decide
private theorem hAst042DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst042Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst042Denominator hAst042DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst042Cross : equalCheck
    (mul hAst042Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst042Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst042Numerator) hAst042Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst042Code : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 1))+(Source.multiplierImag z.1 z.2)))) :=
  hAst042Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst042Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst042Denominator)
    hAst042DenNonzero hAst042Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst043Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,-4,0,-3],[0,2,-2,-2,4,-2,-2,2],[3,0,9,0,9,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst043Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst043Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^2))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1))+(Source.multiplierReal z.1 z.2))))) :=
  (hAst033Code.add hAst037Code)
private theorem hAst043DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst043Denominator=true := by kernel_decide
private theorem hAst043DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst043Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst043Denominator hAst043DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst043Cross : equalCheck
    (mul hAst043Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst043Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst043Numerator) hAst043Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst043Code : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^2))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1))+(Source.multiplierReal z.1 z.2))))) :=
  hAst043Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst043Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst043Denominator)
    hAst043DenNonzero hAst043Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst044Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2,0,-4,0,-4,0,-2],[0,2,-2,-2,4,-2,-2,2],[3,0,9,0,9,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst044Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst044Raw : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^2))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 1))+(Source.multiplierImag z.1 z.2))))) :=
  (hAst043Code.add hAst042Code)
private theorem hAst044DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst044Denominator=true := by kernel_decide
private theorem hAst044DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst044Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst044Denominator hAst044DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst044Cross : equalCheck
    (mul hAst044Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst044Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst044Numerator) hAst044Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst044Code : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^2))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 1))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 1))+(Source.multiplierImag z.1 z.2))))) :=
  hAst044Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst044Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst044Denominator)
    hAst044DenNonzero hAst044Cross

/-- Article: proposed exact numerator for hDiscrepancy1. -/
def hDiscrepancy1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2,0,-4,0,-4,0,-2],[0,2,-2,-2,4,-2,-2,2],[3,0,9,0,9,0,3]]
/-- Article: proposed positive denominator for hDiscrepancy1. -/
def hDiscrepancy1Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDiscrepancy1Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^2))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 1)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 1)+(Source.multiplierImag z.1 z.2))))) :=
  (hAst044Code.congr (by
    intro z hz
    ring))
private theorem hDiscrepancy1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^2))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 1))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 1)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 1)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 1)+(Source.multiplierImag z.1 z.2))))=Source.discrepancy z.1 z.2 1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.discrepancy]; ring
private theorem hDiscrepancy1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDiscrepancy1Denominator=true := by kernel_decide
private theorem hDiscrepancy1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDiscrepancy1Denominator hDiscrepancy1DenCheck hz.1 hz.2).ne'
private theorem hDiscrepancy1Cross : equalCheck
    (mul hDiscrepancy1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy1Numerator) hDiscrepancy1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDiscrepancy1. -/
def hDiscrepancy1Code : RationalCode Source.domain (fun z => Source.discrepancy z.1 z.2 1) :=
  (hDiscrepancy1Raw.congr hDiscrepancy1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy1Denominator)
    hDiscrepancy1DenNonzero hDiscrepancy1Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst045Numerator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst045Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst045Raw : RationalCode Source.domain (fun z => (z.2)^2) :=
  ((RationalCode.second Source.domain).pow 2)
private theorem hAst045DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst045Denominator=true := by kernel_decide
private theorem hAst045DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst045Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst045Denominator hAst045DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst045Cross : equalCheck
    (mul hAst045Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst045Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst045Numerator) hAst045Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst045Code : RationalCode Source.domain (fun z => (z.2)^2) :=
  hAst045Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst045Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst045Denominator)
    hAst045DenNonzero hAst045Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst046Numerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst046Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst046Raw : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+(z.2)^2)) :=
  ((RationalCode.constant Source.domain 1).add hAst045Code)
private theorem hAst046DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst046Denominator=true := by kernel_decide
private theorem hAst046DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst046Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst046Denominator hAst046DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst046Cross : equalCheck
    (mul hAst046Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst046Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst046Numerator) hAst046Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst046Code : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+(z.2)^2)) :=
  hAst046Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst046Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst046Denominator)
    hAst046DenNonzero hAst046Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst047Numerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[2],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst047Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst047Raw : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+(z.2)^2))^2) :=
  (hAst046Code.pow 2)
private theorem hAst047DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst047Denominator=true := by kernel_decide
private theorem hAst047DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst047Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst047Denominator hAst047DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst047Cross : equalCheck
    (mul hAst047Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst047Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst047Numerator) hAst047Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst047Code : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+(z.2)^2))^2) :=
  hAst047Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst047Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst047Denominator)
    hAst047DenNonzero hAst047Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst048Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,2,0,4,0,4,0,2],[0,-2,2,2,-4,2,2,-2],[-3,0,-9,0,-9,0,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst048Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst048Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 1))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDiscrepancy1Code)
private theorem hAst048DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst048Denominator=true := by kernel_decide
private theorem hAst048DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst048Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst048Denominator hAst048DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst048Cross : equalCheck
    (mul hAst048Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst048Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst048Numerator) hAst048Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst048Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 1))) :=
  hAst048Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst048Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst048Denominator)
    hAst048DenNonzero hAst048Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst049Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,-1],[0],[20,0,32,0,4],[0],[32,0,32],[0],[16,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst049Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst049Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 1)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)) :=
  (hRadius1Code.add hAst047Code)
private theorem hAst049DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst049Denominator=true := by kernel_decide
private theorem hAst049DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst049Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst049Denominator hAst049DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst049Cross : equalCheck
    (mul hAst049Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst049Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst049Numerator) hAst049Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst049Code : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 1)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)) :=
  hAst049Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst049Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst049Denominator)
    hAst049DenNonzero hAst049Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst050Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-10,0,-6,0,-1],[0,0,8,0,16,0,16,0,8],[20,-8,80,8,72,8,48,-8,4],[-12,0,-36,0,-36,0,-12],[32,0,96,0,96,0,32],[0],[16,0,48,0,48,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst050Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst050Raw : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 1)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 1)))) :=
  (hAst049Code.add hAst048Code)
private theorem hAst050DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst050Denominator=true := by kernel_decide
private theorem hAst050DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst050Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst050Denominator hAst050DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst050Cross : equalCheck
    (mul hAst050Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst050Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst050Numerator) hAst050Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst050Code : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 1)+((((1 : ℚ) : ℝ)+(z.2)^2))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 1)))) :=
  hAst050Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst050Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst050Denominator)
    hAst050DenNonzero hAst050Cross

/-- Article: proposed exact numerator for hPairLower1. -/
def hPairLower1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-10,0,-6,0,-1],[0,0,8,0,16,0,16,0,8],[20,-8,80,8,72,8,48,-8,4],[-12,0,-36,0,-36,0,-12],[32,0,96,0,96,0,32],[0],[16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for hPairLower1. -/
def hPairLower1Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairLower1Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 1)+((((1 : ℚ) : ℝ)+(z.2)^2))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 1)))) :=
  (hAst050Code.congr (by
    intro z hz
    ring))
private theorem hPairLower1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.radius z.1 z.2 1)+((((1 : ℚ) : ℝ)+(z.2)^2))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 1)))=Source.pairSlack z.1 z.2 (-1) 1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairLower1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairLower1Denominator=true := by kernel_decide
private theorem hPairLower1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairLower1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairLower1Denominator hPairLower1DenCheck hz.1 hz.2).ne'
private theorem hPairLower1Cross : equalCheck
    (mul hPairLower1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairLower1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairLower1Numerator) hPairLower1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairLower1. -/
def hPairLower1Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (-1) 1) :=
  (hPairLower1Raw.congr hPairLower1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower1Denominator)
    hPairLower1DenNonzero hPairLower1Cross

end
end polyak.Certificates.Startup.Codes
