import polyak.Certificates.Startup.Code02

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: proposed exact numerator for hU7. -/
def hU7Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,8,0,-32,0,-8,0,-64,0,-8,0,-32,0,8]]
/-- Article: proposed positive denominator for hU7. -/
def hU7Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hU7Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 5 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 6 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hU5Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hU6Code))
private theorem hU7Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 5 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 6 (radialCosine z.1))))=polyak.Spectral.chebU 7 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebU_rec 5]; ring
private theorem hU7DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hU7Denominator=true := by kernel_decide
private theorem hU7DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hU7Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hU7Denominator hU7DenCheck hz.1 hz.2).ne'
private theorem hU7Cross : equalCheck
    (mul hU7Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hU7Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hU7Numerator) hU7Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hU7. -/
def hU7Code : RationalCode Source.domain (fun z => polyak.Spectral.chebU 7 (radialCosine z.1)) :=
  (hU7Raw.congr hU7Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hU7Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hU7Denominator)
    hU7DenNonzero hU7Cross

/-- Article: proposed exact numerator for hU8. -/
def hU8Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,-32,0,28,0,-32,0,70,0,-32,0,28,0,-32,0,1]]
/-- Article: proposed positive denominator for hU8. -/
def hU8Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hU8Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 6 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 7 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hU6Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hU7Code))
private theorem hU8Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 6 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 7 (radialCosine z.1))))=polyak.Spectral.chebU 8 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebU_rec 6]; ring
private theorem hU8DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hU8Denominator=true := by kernel_decide
private theorem hU8DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hU8Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hU8Denominator hU8DenCheck hz.1 hz.2).ne'
private theorem hU8Cross : equalCheck
    (mul hU8Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hU8Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hU8Numerator) hU8Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hU8. -/
def hU8Code : RationalCode Source.domain (fun z => polyak.Spectral.chebU 8 (radialCosine z.1)) :=
  (hU8Raw.congr hU8Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hU8Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hU8Denominator)
    hU8DenNonzero hU8Cross

/-- Article: proposed exact numerator for hU9. -/
def hU9Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-10,0,80,0,8,0,176,0,4,0,176,0,8,0,80,0,-10]]
/-- Article: proposed positive denominator for hU9. -/
def hU9Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hU9Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 7 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 8 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hU7Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hU8Code))
private theorem hU9Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 7 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 8 (radialCosine z.1))))=polyak.Spectral.chebU 9 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebU_rec 7]; ring
private theorem hU9DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hU9Denominator=true := by kernel_decide
private theorem hU9DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hU9Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hU9Denominator hU9DenCheck hz.1 hz.2).ne'
private theorem hU9Cross : equalCheck
    (mul hU9Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hU9Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hU9Numerator) hU9Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hU9. -/
def hU9Code : RationalCode Source.domain (fun z => polyak.Spectral.chebU 9 (radialCosine z.1)) :=
  (hU9Raw.congr hU9Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hU9Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hU9Denominator)
    hU9DenNonzero hU9Cross

/-- Article: proposed exact numerator for hAlphaRealLower. -/
def hAlphaRealLowerNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,-1],[0,0,4,0,6,0,2],[-1,0,-3,0,-2]]
/-- Article: proposed positive denominator for hAlphaRealLower. -/
def hAlphaRealLowerDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,16,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hAlphaRealLowerRaw : RationalCode Source.domain (fun z => (((((1/2) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)*(((1 : ℚ) : ℝ)+(Source.multiplierReal z.1 z.2)))+((((1/2) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)*(Source.imaginarySquare z.1)*(Source.multiplierImag z.1 z.2)))) :=
  ((((RationalCode.constant Source.domain (1/2)).mul hDRealCode).mul ((RationalCode.constant Source.domain 1).add hSRealCode)).add ((((RationalCode.constant Source.domain (1/2)).mul hDImagCode).mul hImSqCode).mul hSImagCode))
private theorem hAlphaRealLowerIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((1/2) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)*(((1 : ℚ) : ℝ)+(Source.multiplierReal z.1 z.2)))+((((1/2) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)*(Source.imaginarySquare z.1)*(Source.multiplierImag z.1 z.2)))=Source.alphaReal z.1 z.2 (-1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.alphaReal]; ring
private theorem hAlphaRealLowerDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAlphaRealLowerDenominator=true := by kernel_decide
private theorem hAlphaRealLowerDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAlphaRealLowerDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAlphaRealLowerDenominator hAlphaRealLowerDenCheck hz.1 hz.2).ne'
private theorem hAlphaRealLowerCross : equalCheck
    (mul hAlphaRealLowerRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAlphaRealLowerDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAlphaRealLowerNumerator) hAlphaRealLowerRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hAlphaRealLower. -/
def hAlphaRealLowerCode : RationalCode Source.domain (fun z => Source.alphaReal z.1 z.2 (-1)) :=
  (hAlphaRealLowerRaw.congr hAlphaRealLowerIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAlphaRealLowerNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAlphaRealLowerDenominator)
    hAlphaRealLowerDenNonzero hAlphaRealLowerCross

/-- Article: proposed exact numerator for hAlphaImagLower. -/
def hAlphaImagLowerNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,3,0,1],[-2,0,-2],[-1,0,-1]]
/-- Article: proposed positive denominator for hAlphaImagLower. -/
def hAlphaImagLowerDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hAlphaImagLowerRaw : RationalCode Source.domain (fun z => (((((1/2) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)*(Source.multiplierImag z.1 z.2))+((((-1/2) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)*(((1 : ℚ) : ℝ)+(Source.multiplierReal z.1 z.2))))) :=
  ((((RationalCode.constant Source.domain (1/2)).mul hDRealCode).mul hSImagCode).add (((RationalCode.constant Source.domain (-1/2)).mul hDImagCode).mul ((RationalCode.constant Source.domain 1).add hSRealCode)))
private theorem hAlphaImagLowerIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((1/2) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)*(Source.multiplierImag z.1 z.2))+((((-1/2) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)*(((1 : ℚ) : ℝ)+(Source.multiplierReal z.1 z.2))))=Source.alphaImag z.1 z.2 (-1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.alphaImag]; ring
private theorem hAlphaImagLowerDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAlphaImagLowerDenominator=true := by kernel_decide
private theorem hAlphaImagLowerDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAlphaImagLowerDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAlphaImagLowerDenominator hAlphaImagLowerDenCheck hz.1 hz.2).ne'
private theorem hAlphaImagLowerCross : equalCheck
    (mul hAlphaImagLowerRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAlphaImagLowerDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAlphaImagLowerNumerator) hAlphaImagLowerRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hAlphaImagLower. -/
def hAlphaImagLowerCode : RationalCode Source.domain (fun z => Source.alphaImag z.1 z.2 (-1)) :=
  (hAlphaImagLowerRaw.congr hAlphaImagLowerIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAlphaImagLowerNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAlphaImagLowerDenominator)
    hAlphaImagLowerDenNonzero hAlphaImagLowerCross

/-- Article: proposed exact numerator for hBetaRealLower. -/
def hBetaRealLowerNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,-8,7,-8],[0,0,4,0,6,0,2],[-1,0,-3,0,-2]]
/-- Article: proposed positive denominator for hBetaRealLower. -/
def hBetaRealLowerDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,16,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hBetaRealLowerRaw : RationalCode Source.domain (fun z => ((Source.alphaReal z.1 z.2 (-1))+((Source.hyperbolic z.1)*(Source.gap z.1)*(Source.lambdaReal z.1)*(z.1)⁻¹))) :=
  (hAlphaRealLowerCode.add (((hGCode.mul hGapCode).mul hRealCode).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))))
private theorem hBetaRealLowerIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.alphaReal z.1 z.2 (-1))+((Source.hyperbolic z.1)*(Source.gap z.1)*(Source.lambdaReal z.1)*(z.1)⁻¹))=Source.betaReal z.1 z.2 (-1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.betaReal]; ring
private theorem hBetaRealLowerDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hBetaRealLowerDenominator=true := by kernel_decide
private theorem hBetaRealLowerDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hBetaRealLowerDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hBetaRealLowerDenominator hBetaRealLowerDenCheck hz.1 hz.2).ne'
private theorem hBetaRealLowerCross : equalCheck
    (mul hBetaRealLowerRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hBetaRealLowerDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hBetaRealLowerNumerator) hBetaRealLowerRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hBetaRealLower. -/
def hBetaRealLowerCode : RationalCode Source.domain (fun z => Source.betaReal z.1 z.2 (-1)) :=
  (hBetaRealLowerRaw.congr hBetaRealLowerIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaRealLowerNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaRealLowerDenominator)
    hBetaRealLowerDenNonzero hBetaRealLowerCross

/-- Article: proposed exact numerator for hBetaImagLower. -/
def hBetaImagLowerNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,-8,11,-8,1],[-2,0,-2],[-1,0,-1]]
/-- Article: proposed positive denominator for hBetaImagLower. -/
def hBetaImagLowerDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,8,0,8]]
/-- Article: composition of proved source-preserving rational operations. -/
def hBetaImagLowerRaw : RationalCode Source.domain (fun z => ((Source.alphaImag z.1 z.2 (-1))+((((-1) : ℚ) : ℝ)*(Source.hyperbolic z.1)*(Source.gap z.1)*(z.1)⁻¹))) :=
  (hAlphaImagLowerCode.add ((((RationalCode.constant Source.domain (-1)).mul hGCode).mul hGapCode).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))))
private theorem hBetaImagLowerIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.alphaImag z.1 z.2 (-1))+((((-1) : ℚ) : ℝ)*(Source.hyperbolic z.1)*(Source.gap z.1)*(z.1)⁻¹))=Source.betaImag z.1 z.2 (-1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.betaImag]; ring
private theorem hBetaImagLowerDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hBetaImagLowerDenominator=true := by kernel_decide
private theorem hBetaImagLowerDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hBetaImagLowerDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hBetaImagLowerDenominator hBetaImagLowerDenCheck hz.1 hz.2).ne'
private theorem hBetaImagLowerCross : equalCheck
    (mul hBetaImagLowerRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hBetaImagLowerDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hBetaImagLowerNumerator) hBetaImagLowerRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hBetaImagLower. -/
def hBetaImagLowerCode : RationalCode Source.domain (fun z => Source.betaImag z.1 z.2 (-1)) :=
  (hBetaImagLowerRaw.congr hBetaImagLowerIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaImagLowerNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaImagLowerDenominator)
    hBetaImagLowerDenNonzero hBetaImagLowerCross

/-- Article: proposed exact numerator for hBetaNormLower. -/
def hBetaNormLowerNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,65,-192,391,-496,576,-496,400,-208,87,-16,1],[0,0,0,32,-36,32,-24,-32,-8,-32,-24,0,-4],[0,0,2,32,-14,112,-28,144,-12,80,2,16,2],[0,0,-4,0,-24,0,-40,0,-24,0,-4],[1,0,7,0,16,0,16,0,7,0,1]]
/-- Article: proposed positive denominator for hBetaNormLower. -/
def hBetaNormLowerDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,256,0,384,0,256,0,64]]
/-- Article: composition of proved source-preserving rational operations. -/
def hBetaNormLowerRaw : RationalCode Source.domain (fun z => (((Source.betaReal z.1 z.2 (-1)))^2+((Source.imaginarySquare z.1)*((Source.betaImag z.1 z.2 (-1)))^2))) :=
  ((hBetaRealLowerCode.pow 2).add (hImSqCode.mul (hBetaImagLowerCode.pow 2)))
private theorem hBetaNormLowerIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.betaReal z.1 z.2 (-1)))^2+((Source.imaginarySquare z.1)*((Source.betaImag z.1 z.2 (-1)))^2))=Source.betaNorm z.1 z.2 (-1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem hBetaNormLowerDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hBetaNormLowerDenominator=true := by kernel_decide
private theorem hBetaNormLowerDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hBetaNormLowerDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hBetaNormLowerDenominator hBetaNormLowerDenCheck hz.1 hz.2).ne'
private theorem hBetaNormLowerCross : equalCheck
    (mul hBetaNormLowerRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hBetaNormLowerDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hBetaNormLowerNumerator) hBetaNormLowerRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hBetaNormLower. -/
def hBetaNormLowerCode : RationalCode Source.domain (fun z => Source.betaNorm z.1 z.2 (-1)) :=
  (hBetaNormLowerRaw.congr hBetaNormLowerIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaNormLowerNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hBetaNormLowerDenominator)
    hBetaNormLowerDenNonzero hBetaNormLowerCross

/-- Article: proposed exact numerator for hQuadraticLower. -/
def hQuadraticLowerNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,1,-1,1]]
/-- Article: proposed positive denominator for hQuadraticLower. -/
def hQuadraticLowerDenominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hQuadraticLowerRaw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(Source.gap z.1)*((Source.hyperbolic z.1))⁻¹*(z.1)⁻¹)) :=
  ((((RationalCode.constant Source.domain (1/4)).mul hGapCode).mul (hGCode.invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      dsimp only [Source.hyperbolic]
      positivity))).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity)))
private theorem hQuadraticLowerIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((1/4) : ℚ) : ℝ)*(Source.gap z.1)*((Source.hyperbolic z.1))⁻¹*(z.1)⁻¹)=Source.quadratic z.1 (-1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.quadratic]; ring
private theorem hQuadraticLowerDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hQuadraticLowerDenominator=true := by kernel_decide
private theorem hQuadraticLowerDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hQuadraticLowerDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hQuadraticLowerDenominator hQuadraticLowerDenCheck hz.1 hz.2).ne'
private theorem hQuadraticLowerCross : equalCheck
    (mul hQuadraticLowerRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hQuadraticLowerDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hQuadraticLowerNumerator) hQuadraticLowerRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hQuadraticLower. -/
def hQuadraticLowerCode : RationalCode Source.domain (fun z => Source.quadratic z.1 (-1)) :=
  (hQuadraticLowerRaw.congr hQuadraticLowerIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hQuadraticLowerNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hQuadraticLowerDenominator)
    hQuadraticLowerDenNonzero hQuadraticLowerCross

/-- Article: proposed exact numerator for hConstantLower. -/
def hConstantLowerNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2,0,0,16,-14,16],[0,0,-8,0,-20,0,-16,0,-4],[1,0,2,0,0,0,-2,0,-1]]
/-- Article: proposed positive denominator for hConstantLower. -/
def hConstantLowerDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hConstantLowerRaw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.alphaReal z.1 z.2 (-1)))+((((-1/4) : ℚ) : ℝ)*(Source.defectNorm z.1 z.2))+((((1/4) : ℚ) : ℝ)*(Source.gap z.1)*z.1*((Source.hyperbolic z.1))⁻¹))) :=
  ((((RationalCode.constant Source.domain (-1)).mul hAlphaRealLowerCode).add ((RationalCode.constant Source.domain (-1/4)).mul hDNormCode)).add ((((RationalCode.constant Source.domain (1/4)).mul hGapCode).mul (RationalCode.first Source.domain)).mul (hGCode.invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      dsimp only [Source.hyperbolic]
      positivity))))
private theorem hConstantLowerIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(Source.alphaReal z.1 z.2 (-1)))+((((-1/4) : ℚ) : ℝ)*(Source.defectNorm z.1 z.2))+((((1/4) : ℚ) : ℝ)*(Source.gap z.1)*z.1*((Source.hyperbolic z.1))⁻¹))=Source.constant z.1 z.2 (-1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.constant]; ring
private theorem hConstantLowerDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hConstantLowerDenominator=true := by kernel_decide
private theorem hConstantLowerDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hConstantLowerDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hConstantLowerDenominator hConstantLowerDenCheck hz.1 hz.2).ne'
private theorem hConstantLowerCross : equalCheck
    (mul hConstantLowerRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hConstantLowerDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hConstantLowerNumerator) hConstantLowerRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hConstantLower. -/
def hConstantLowerCode : RationalCode Source.domain (fun z => Source.constant z.1 z.2 (-1)) :=
  (hConstantLowerRaw.congr hConstantLowerIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hConstantLowerNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hConstantLowerDenominator)
    hConstantLowerDenNonzero hConstantLowerCross

end
end polyak.Certificates.Startup.Codes
