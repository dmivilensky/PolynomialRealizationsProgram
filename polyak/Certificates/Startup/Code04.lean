import polyak.Certificates.Startup.Code03

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: proposed exact numerator for hResidueLower0. -/
def hResidueLower0Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,-8,7,-8],[0,0,4,0,6,0,2],[-1,0,-3,0,-2]]
/-- Article: proposed positive denominator for hResidueLower0. -/
def hResidueLower0Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,16,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hResidueLower0Raw : RationalCode Source.domain (fun z => (Source.betaReal z.1 z.2 (-1))) :=
  hBetaRealLowerCode
private theorem hResidueLower0Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.betaReal z.1 z.2 (-1))=Source.residue z.1 z.2 (-1) 0 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem hResidueLower0DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hResidueLower0Denominator=true := by kernel_decide
private theorem hResidueLower0DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower0Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hResidueLower0Denominator hResidueLower0DenCheck hz.1 hz.2).ne'
private theorem hResidueLower0Cross : equalCheck
    (mul hResidueLower0Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower0Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower0Numerator) hResidueLower0Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hResidueLower0. -/
def hResidueLower0Code : RationalCode Source.domain (fun z => Source.residue z.1 z.2 (-1) 0) :=
  (hResidueLower0Raw.congr hResidueLower0Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower0Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower0Denominator)
    hResidueLower0DenNonzero hResidueLower0Cross

/-- Article: proposed exact numerator for hResidueLower1. -/
def hResidueLower1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,8,-12,24,-19,24,-12,8,-1],[2,0,0,0,-2],[2,0,5,0,4,0,1]]
/-- Article: proposed positive denominator for hResidueLower1. -/
def hResidueLower1Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,8,0,24,0,24,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hResidueLower1Raw : RationalCode Source.domain (fun z => (((Source.betaReal z.1 z.2 (-1))*(polyak.Spectral.chebT 1 (radialCosine z.1)))+((((-1) : ℚ) : ℝ)*(Source.betaImag z.1 z.2 (-1))*(Source.imaginarySquare z.1)*(polyak.Spectral.chebU 0 (radialCosine z.1))*(z.1)⁻¹))) :=
  ((hBetaRealLowerCode.mul hT1Code).add (((((RationalCode.constant Source.domain (-1)).mul hBetaImagLowerCode).mul hImSqCode).mul hU0Code).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))))
private theorem hResidueLower1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.betaReal z.1 z.2 (-1))*(polyak.Spectral.chebT 1 (radialCosine z.1)))+((((-1) : ℚ) : ℝ)*(Source.betaImag z.1 z.2 (-1))*(Source.imaginarySquare z.1)*(polyak.Spectral.chebU 0 (radialCosine z.1))*(z.1)⁻¹))=Source.residue z.1 z.2 (-1) 1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.residue,ite_eq_right (by decide)]; ring
private theorem hResidueLower1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hResidueLower1Denominator=true := by kernel_decide
private theorem hResidueLower1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hResidueLower1Denominator hResidueLower1DenCheck hz.1 hz.2).ne'
private theorem hResidueLower1Cross : equalCheck
    (mul hResidueLower1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower1Numerator) hResidueLower1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hResidueLower1. -/
def hResidueLower1Code : RationalCode Source.domain (fun z => Source.residue z.1 z.2 (-1) 1) :=
  (hResidueLower1Raw.congr hResidueLower1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower1Denominator)
    hResidueLower1DenNonzero hResidueLower1Cross

/-- Article: proposed exact numerator for hResidueLower2. -/
def hResidueLower2Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,-8,15,-24,23,-24,17,-8,2],[0,0,-8,0,-14,0,-14,0,-10,0,-2],[1,0,1,0,-1,0,-1]]
/-- Article: proposed positive denominator for hResidueLower2. -/
def hResidueLower2Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,32,0,48,0,32,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hResidueLower2Raw : RationalCode Source.domain (fun z => (((Source.betaReal z.1 z.2 (-1))*(polyak.Spectral.chebT 2 (radialCosine z.1)))+((((-1) : ℚ) : ℝ)*(Source.betaImag z.1 z.2 (-1))*(Source.imaginarySquare z.1)*(polyak.Spectral.chebU 1 (radialCosine z.1))*(z.1)⁻¹))) :=
  ((hBetaRealLowerCode.mul hT2Code).add (((((RationalCode.constant Source.domain (-1)).mul hBetaImagLowerCode).mul hImSqCode).mul hU1Code).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))))
private theorem hResidueLower2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.betaReal z.1 z.2 (-1))*(polyak.Spectral.chebT 2 (radialCosine z.1)))+((((-1) : ℚ) : ℝ)*(Source.betaImag z.1 z.2 (-1))*(Source.imaginarySquare z.1)*(polyak.Spectral.chebU 1 (radialCosine z.1))*(z.1)⁻¹))=Source.residue z.1 z.2 (-1) 2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.residue,ite_eq_right (by decide)]; ring
private theorem hResidueLower2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hResidueLower2Denominator=true := by kernel_decide
private theorem hResidueLower2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hResidueLower2Denominator hResidueLower2DenCheck hz.1 hz.2).ne'
private theorem hResidueLower2Cross : equalCheck
    (mul hResidueLower2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower2Numerator) hResidueLower2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hResidueLower2. -/
def hResidueLower2Code : RationalCode Source.domain (fun z => Source.residue z.1 z.2 (-1) 2) :=
  (hResidueLower2Raw.congr hResidueLower2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hResidueLower2Denominator)
    hResidueLower2DenNonzero hResidueLower2Cross

/-- Article: proposed exact numerator for hAlphaRealUpper. -/
def hAlphaRealUpperNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,-1],[0,0,-4,0,-6,0,-2],[-1,0,-3,0,-2]]
/-- Article: proposed positive denominator for hAlphaRealUpper. -/
def hAlphaRealUpperDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,16,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hAlphaRealUpperRaw : RationalCode Source.domain (fun z => (((((1/2) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)*((((-1) : ℚ) : ℝ)+(Source.multiplierReal z.1 z.2)))+((((1/2) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)*(Source.imaginarySquare z.1)*(Source.multiplierImag z.1 z.2)))) :=
  ((((RationalCode.constant Source.domain (1/2)).mul hDRealCode).mul ((RationalCode.constant Source.domain (-1)).add hSRealCode)).add ((((RationalCode.constant Source.domain (1/2)).mul hDImagCode).mul hImSqCode).mul hSImagCode))
private theorem hAlphaRealUpperIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((1/2) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)*((((-1) : ℚ) : ℝ)+(Source.multiplierReal z.1 z.2)))+((((1/2) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)*(Source.imaginarySquare z.1)*(Source.multiplierImag z.1 z.2)))=Source.alphaReal z.1 z.2 (1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.alphaReal]; ring
private theorem hAlphaRealUpperDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAlphaRealUpperDenominator=true := by kernel_decide
private theorem hAlphaRealUpperDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAlphaRealUpperDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAlphaRealUpperDenominator hAlphaRealUpperDenCheck hz.1 hz.2).ne'
private theorem hAlphaRealUpperCross : equalCheck
    (mul hAlphaRealUpperRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAlphaRealUpperDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAlphaRealUpperNumerator) hAlphaRealUpperRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hAlphaRealUpper. -/
def hAlphaRealUpperCode : RationalCode Source.domain (fun z => Source.alphaReal z.1 z.2 (1)) :=
  (hAlphaRealUpperRaw.congr hAlphaRealUpperIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAlphaRealUpperNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAlphaRealUpperDenominator)
    hAlphaRealUpperDenNonzero hAlphaRealUpperCross

/-- Article: proposed exact numerator for hAlphaImagUpper. -/
def hAlphaImagUpperNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,3,0,1],[2,0,2],[-1,0,-1]]
/-- Article: proposed positive denominator for hAlphaImagUpper. -/
def hAlphaImagUpperDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hAlphaImagUpperRaw : RationalCode Source.domain (fun z => (((((1/2) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)*(Source.multiplierImag z.1 z.2))+((((-1/2) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)*((((-1) : ℚ) : ℝ)+(Source.multiplierReal z.1 z.2))))) :=
  ((((RationalCode.constant Source.domain (1/2)).mul hDRealCode).mul hSImagCode).add (((RationalCode.constant Source.domain (-1/2)).mul hDImagCode).mul ((RationalCode.constant Source.domain (-1)).add hSRealCode)))
private theorem hAlphaImagUpperIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((1/2) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)*(Source.multiplierImag z.1 z.2))+((((-1/2) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)*((((-1) : ℚ) : ℝ)+(Source.multiplierReal z.1 z.2))))=Source.alphaImag z.1 z.2 (1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.alphaImag]; ring
private theorem hAlphaImagUpperDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAlphaImagUpperDenominator=true := by kernel_decide
private theorem hAlphaImagUpperDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAlphaImagUpperDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAlphaImagUpperDenominator hAlphaImagUpperDenCheck hz.1 hz.2).ne'
private theorem hAlphaImagUpperCross : equalCheck
    (mul hAlphaImagUpperRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAlphaImagUpperDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAlphaImagUpperNumerator) hAlphaImagUpperRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hAlphaImagUpper. -/
def hAlphaImagUpperCode : RationalCode Source.domain (fun z => Source.alphaImag z.1 z.2 (1)) :=
  (hAlphaImagUpperRaw.congr hAlphaImagUpperIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAlphaImagUpperNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAlphaImagUpperDenominator)
    hAlphaImagUpperDenNonzero hAlphaImagUpperCross

/-- Article: proposed exact numerator for hBetaRealUpper. -/
def hBetaRealUpperNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,-8,7,-8],[0,0,-4,0,-6,0,-2],[-1,0,-3,0,-2]]
/-- Article: proposed positive denominator for hBetaRealUpper. -/
def hBetaRealUpperDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,16,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hBetaRealUpperRaw : RationalCode Source.domain (fun z => ((Source.alphaReal z.1 z.2 (1))+((Source.hyperbolic z.1)*(Source.gap z.1)*(Source.lambdaReal z.1)*(z.1)⁻¹))) :=
  (hAlphaRealUpperCode.add (((hGCode.mul hGapCode).mul hRealCode).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))))
private theorem hBetaRealUpperIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.alphaReal z.1 z.2 (1))+((Source.hyperbolic z.1)*(Source.gap z.1)*(Source.lambdaReal z.1)*(z.1)⁻¹))=Source.betaReal z.1 z.2 (1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.betaReal]; ring
private theorem hBetaRealUpperDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hBetaRealUpperDenominator=true := by kernel_decide
private theorem hBetaRealUpperDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hBetaRealUpperDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hBetaRealUpperDenominator hBetaRealUpperDenCheck hz.1 hz.2).ne'
private theorem hBetaRealUpperCross : equalCheck
    (mul hBetaRealUpperRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hBetaRealUpperDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hBetaRealUpperNumerator) hBetaRealUpperRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hBetaRealUpper. -/
def hBetaRealUpperCode : RationalCode Source.domain (fun z => Source.betaReal z.1 z.2 (1)) :=
  (hBetaRealUpperRaw.congr hBetaRealUpperIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaRealUpperNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaRealUpperDenominator)
    hBetaRealUpperDenNonzero hBetaRealUpperCross

/-- Article: proposed exact numerator for hBetaImagUpper. -/
def hBetaImagUpperNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,8,-5,8,1],[2,0,2],[-1,0,-1]]
/-- Article: proposed positive denominator for hBetaImagUpper. -/
def hBetaImagUpperDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hBetaImagUpperRaw : RationalCode Source.domain (fun z => ((Source.alphaImag z.1 z.2 (1))+((Source.hyperbolic z.1)*(Source.gap z.1)*(z.1)⁻¹))) :=
  (hAlphaImagUpperCode.add ((hGCode.mul hGapCode).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))))
private theorem hBetaImagUpperIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.alphaImag z.1 z.2 (1))+((Source.hyperbolic z.1)*(Source.gap z.1)*(z.1)⁻¹))=Source.betaImag z.1 z.2 (1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.betaImag]; ring
private theorem hBetaImagUpperDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hBetaImagUpperDenominator=true := by kernel_decide
private theorem hBetaImagUpperDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hBetaImagUpperDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hBetaImagUpperDenominator hBetaImagUpperDenCheck hz.1 hz.2).ne'
private theorem hBetaImagUpperCross : equalCheck
    (mul hBetaImagUpperRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hBetaImagUpperDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hBetaImagUpperNumerator) hBetaImagUpperRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hBetaImagUpper. -/
def hBetaImagUpperCode : RationalCode Source.domain (fun z => Source.betaImag z.1 z.2 (1)) :=
  (hBetaImagUpperRaw.congr hBetaImagUpperIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaImagUpperNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaImagUpperDenominator)
    hBetaImagUpperDenNonzero hBetaImagUpperCross

/-- Article: proposed exact numerator for hBetaNormUpper. -/
def hBetaNormUpperNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,65,-96,230,-176,218,-64,54,16,1],[0,0,0,32,-28,128,-76,160,-44,64,4],[0,0,2,0,16,16,20,0,32,-16,2],[0,0,4,0,20,0,20,0,4],[1,0,6,0,10,0,6,0,1]]
/-- Article: proposed positive denominator for hBetaNormUpper. -/
def hBetaNormUpperDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,192,0,192,0,64]]
/-- Article: composition of proved source-preserving rational operations. -/
def hBetaNormUpperRaw : RationalCode Source.domain (fun z => (((Source.betaReal z.1 z.2 (1)))^2+((Source.imaginarySquare z.1)*((Source.betaImag z.1 z.2 (1)))^2))) :=
  ((hBetaRealUpperCode.pow 2).add (hImSqCode.mul (hBetaImagUpperCode.pow 2)))
private theorem hBetaNormUpperIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.betaReal z.1 z.2 (1)))^2+((Source.imaginarySquare z.1)*((Source.betaImag z.1 z.2 (1)))^2))=Source.betaNorm z.1 z.2 (1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem hBetaNormUpperDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hBetaNormUpperDenominator=true := by kernel_decide
private theorem hBetaNormUpperDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hBetaNormUpperDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hBetaNormUpperDenominator hBetaNormUpperDenCheck hz.1 hz.2).ne'
private theorem hBetaNormUpperCross : equalCheck
    (mul hBetaNormUpperRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hBetaNormUpperDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hBetaNormUpperNumerator) hBetaNormUpperRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hBetaNormUpper. -/
def hBetaNormUpperCode : RationalCode Source.domain (fun z => Source.betaNorm z.1 z.2 (1)) :=
  (hBetaNormUpperRaw.congr hBetaNormUpperIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaNormUpperNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaNormUpperDenominator)
    hBetaNormUpperDenNonzero hBetaNormUpperCross

/-- Article: proposed exact numerator for hQuadraticUpper. -/
def hQuadraticUpperNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,1,-1,1]]
/-- Article: proposed positive denominator for hQuadraticUpper. -/
def hQuadraticUpperDenominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hQuadraticUpperRaw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(Source.gap z.1)*z.1*((Source.hyperbolic z.1))⁻¹)) :=
  ((((RationalCode.constant Source.domain (1/4)).mul hGapCode).mul (RationalCode.first Source.domain)).mul (hGCode.invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      dsimp only [Source.hyperbolic]
      positivity)))
private theorem hQuadraticUpperIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((1/4) : ℚ) : ℝ)*(Source.gap z.1)*z.1*((Source.hyperbolic z.1))⁻¹)=Source.quadratic z.1 (1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.quadratic]; ring
private theorem hQuadraticUpperDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hQuadraticUpperDenominator=true := by kernel_decide
private theorem hQuadraticUpperDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hQuadraticUpperDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hQuadraticUpperDenominator hQuadraticUpperDenCheck hz.1 hz.2).ne'
private theorem hQuadraticUpperCross : equalCheck
    (mul hQuadraticUpperRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hQuadraticUpperDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hQuadraticUpperNumerator) hQuadraticUpperRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hQuadraticUpper. -/
def hQuadraticUpperCode : RationalCode Source.domain (fun z => Source.quadratic z.1 (1)) :=
  (hQuadraticUpperRaw.congr hQuadraticUpperIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hQuadraticUpperNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hQuadraticUpperDenominator)
    hQuadraticUpperDenNonzero hQuadraticUpperCross

/-- Article: proposed exact numerator for hConstantUpper. -/
def hConstantUpperNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2,16,-16,16,2],[0,0,8,0,20,0,16,0,4],[1,0,2,0,0,0,-2,0,-1]]
/-- Article: proposed positive denominator for hConstantUpper. -/
def hConstantUpperDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hConstantUpperRaw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.alphaReal z.1 z.2 (1)))+((((-1/4) : ℚ) : ℝ)*(Source.defectNorm z.1 z.2))+((((1/4) : ℚ) : ℝ)*(Source.gap z.1)*((Source.hyperbolic z.1))⁻¹*(z.1)⁻¹))) :=
  ((((RationalCode.constant Source.domain (-1)).mul hAlphaRealUpperCode).add ((RationalCode.constant Source.domain (-1/4)).mul hDNormCode)).add ((((RationalCode.constant Source.domain (1/4)).mul hGapCode).mul (hGCode.invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      dsimp only [Source.hyperbolic]
      positivity))).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))))
private theorem hConstantUpperIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(Source.alphaReal z.1 z.2 (1)))+((((-1/4) : ℚ) : ℝ)*(Source.defectNorm z.1 z.2))+((((1/4) : ℚ) : ℝ)*(Source.gap z.1)*((Source.hyperbolic z.1))⁻¹*(z.1)⁻¹))=Source.constant z.1 z.2 (1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.constant]; ring
private theorem hConstantUpperDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hConstantUpperDenominator=true := by kernel_decide
private theorem hConstantUpperDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hConstantUpperDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hConstantUpperDenominator hConstantUpperDenCheck hz.1 hz.2).ne'
private theorem hConstantUpperCross : equalCheck
    (mul hConstantUpperRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hConstantUpperDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hConstantUpperNumerator) hConstantUpperRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hConstantUpper. -/
def hConstantUpperCode : RationalCode Source.domain (fun z => Source.constant z.1 z.2 (1)) :=
  (hConstantUpperRaw.congr hConstantUpperIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hConstantUpperNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hConstantUpperDenominator)
    hConstantUpperDenNonzero hConstantUpperCross

end
end polyak.Certificates.Startup.Codes
