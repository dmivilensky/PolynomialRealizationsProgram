import polyak.Numerics.KernelDecide
import polyak.Numerics.BivariateAlgebra
import polyak.Numerics.PositiveCoefficients
import polyak.Realization.ExplicitSpiral.Source

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: proposed exact numerator for hG. -/
def hGNumerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1]]
/-- Article: proposed positive denominator for hG. -/
def hGDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGRaw : RationalCode Source.domain (fun z => (((((1/2) : ℚ) : ℝ)*z.1)+((((1/2) : ℚ) : ℝ)*(z.1)⁻¹))) :=
  (((RationalCode.constant Source.domain (1/2)).mul (RationalCode.first Source.domain)).add ((RationalCode.constant Source.domain (1/2)).mul ((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))))
private theorem hGIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((1/2) : ℚ) : ℝ)*z.1)+((((1/2) : ℚ) : ℝ)*(z.1)⁻¹))=Source.hyperbolic z.1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.hyperbolic]; ring
private theorem hGDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGDenominator=true := by kernel_decide
private theorem hGDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGDenominator hGDenCheck hz.1 hz.2).ne'
private theorem hGCross : equalCheck
    (mul hGRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGNumerator) hGRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hG. -/
def hGCode : RationalCode Source.domain (fun z => Source.hyperbolic z.1) :=
  (hGRaw.congr hGIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGDenominator)
    hGDenNonzero hGCross

/-- Article: proposed exact numerator for hGap. -/
def hGapNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,2,-2,2]]
/-- Article: proposed positive denominator for hGap. -/
def hGapDenominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGapRaw : RationalCode Source.domain (fun z => (((2 : ℚ) : ℝ)*z.1*(((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹)^2*(((1 : ℚ) : ℝ)+(z.1)^2+((((-1) : ℚ) : ℝ)*z.1)))) :=
  ((((RationalCode.constant Source.domain 2).mul (RationalCode.first Source.domain)).mul ((((RationalCode.constant Source.domain 1).add ((RationalCode.first Source.domain).pow 2)).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity)).pow 2)).mul (((RationalCode.constant Source.domain 1).add ((RationalCode.first Source.domain).pow 2)).add ((RationalCode.constant Source.domain (-1)).mul (RationalCode.first Source.domain))))
private theorem hGapIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((2 : ℚ) : ℝ)*z.1*(((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹)^2*(((1 : ℚ) : ℝ)+(z.1)^2+((((-1) : ℚ) : ℝ)*z.1)))=Source.gap z.1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gap]; field_simp; ring
private theorem hGapDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGapDenominator=true := by kernel_decide
private theorem hGapDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGapDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGapDenominator hGapDenCheck hz.1 hz.2).ne'
private theorem hGapCross : equalCheck
    (mul hGapRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGapDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGapNumerator) hGapRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGap. -/
def hGapCode : RationalCode Source.domain (fun z => Source.gap z.1) :=
  (hGapRaw.congr hGapIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGapNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGapDenominator)
    hGapDenNonzero hGapCross

/-- Article: proposed exact numerator for hReal. -/
def hRealNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1]]
/-- Article: proposed positive denominator for hReal. -/
def hRealDenominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hRealRaw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(z.1)^2*((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹)) :=
  (((RationalCode.constant Source.domain (-1)).mul ((RationalCode.first Source.domain).pow 2)).mul (((RationalCode.constant Source.domain 1).add ((RationalCode.first Source.domain).pow 2)).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity)))
private theorem hRealIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((-1) : ℚ) : ℝ)*(z.1)^2*((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹)=Source.lambdaReal z.1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.lambdaReal]; ring
private theorem hRealDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hRealDenominator=true := by kernel_decide
private theorem hRealDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hRealDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hRealDenominator hRealDenCheck hz.1 hz.2).ne'
private theorem hRealCross : equalCheck
    (mul hRealRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hRealDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hRealNumerator) hRealRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hReal. -/
def hRealCode : RationalCode Source.domain (fun z => Source.lambdaReal z.1) :=
  (hRealRaw.congr hRealIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hRealNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hRealDenominator)
    hRealDenNonzero hRealCross

/-- Article: proposed exact numerator for hImSq. -/
def hImSqNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,1,0,1]]
/-- Article: proposed positive denominator for hImSq. -/
def hImSqDenominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hImSqRaw : RationalCode Source.domain (fun z => ((z.1)^2+((((-1) : ℚ) : ℝ)*((Source.lambdaReal z.1))^2))) :=
  (((RationalCode.first Source.domain).pow 2).add ((RationalCode.constant Source.domain (-1)).mul (hRealCode.pow 2)))
private theorem hImSqIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((z.1)^2+((((-1) : ℚ) : ℝ)*((Source.lambdaReal z.1))^2))=Source.imaginarySquare z.1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.imaginarySquare]; ring
private theorem hImSqDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hImSqDenominator=true := by kernel_decide
private theorem hImSqDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hImSqDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hImSqDenominator hImSqDenCheck hz.1 hz.2).ne'
private theorem hImSqCross : equalCheck
    (mul hImSqRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hImSqDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hImSqNumerator) hImSqRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hImSq. -/
def hImSqCode : RationalCode Source.domain (fun z => Source.imaginarySquare z.1) :=
  (hImSqRaw.congr hImSqIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hImSqNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hImSqDenominator)
    hImSqDenNonzero hImSqCross

/-- Article: proposed exact numerator for hCos. -/
def hCosNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,-1]]
/-- Article: proposed positive denominator for hCos. -/
def hCosDenominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hCosRaw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*z.1*((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹)) :=
  (((RationalCode.constant Source.domain (-1)).mul (RationalCode.first Source.domain)).mul (((RationalCode.constant Source.domain 1).add ((RationalCode.first Source.domain).pow 2)).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity)))
private theorem hCosIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((-1) : ℚ) : ℝ)*z.1*((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹)=radialCosine z.1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [radialCosine]; ring
private theorem hCosDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hCosDenominator=true := by kernel_decide
private theorem hCosDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hCosDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hCosDenominator hCosDenCheck hz.1 hz.2).ne'
private theorem hCosCross : equalCheck
    (mul hCosRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hCosDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hCosNumerator) hCosRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hCos. -/
def hCosCode : RationalCode Source.domain (fun z => radialCosine z.1) :=
  (hCosRaw.congr hCosIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hCosNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hCosDenominator)
    hCosDenNonzero hCosCross

/-- Article: proposed exact numerator for hSReal. -/
def hSRealNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1],[0],[-1]]
/-- Article: proposed positive denominator for hSReal. -/
def hSRealDenominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hSRealRaw : RationalCode Source.domain (fun z => ((((1/2) : ℚ) : ℝ)*(z.2)⁻¹*((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹*(((((-1) : ℚ) : ℝ)*(z.2)^2)+((((-1) : ℚ) : ℝ)*(z.1)^2)))) :=
  ((((RationalCode.constant Source.domain (1/2)).mul ((RationalCode.second Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))).mul (((RationalCode.constant Source.domain 1).add ((RationalCode.first Source.domain).pow 2)).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))).mul (((RationalCode.constant Source.domain (-1)).mul ((RationalCode.second Source.domain).pow 2)).add ((RationalCode.constant Source.domain (-1)).mul ((RationalCode.first Source.domain).pow 2))))
private theorem hSRealIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((1/2) : ℚ) : ℝ)*(z.2)⁻¹*((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹*(((((-1) : ℚ) : ℝ)*(z.2)^2)+((((-1) : ℚ) : ℝ)*(z.1)^2)))=Source.multiplierReal z.1 z.2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.multiplierReal]; field_simp; ring
private theorem hSRealDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hSRealDenominator=true := by kernel_decide
private theorem hSRealDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hSRealDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hSRealDenominator hSRealDenCheck hz.1 hz.2).ne'
private theorem hSRealCross : equalCheck
    (mul hSRealRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hSRealDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hSRealNumerator) hSRealRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hSReal. -/
def hSRealCode : RationalCode Source.domain (fun z => Source.multiplierReal z.1 z.2) :=
  (hSRealRaw.congr hSRealIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hSRealNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hSRealDenominator)
    hSRealDenNonzero hSRealCross

/-- Article: proposed exact numerator for hSImag. -/
def hSImagNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1],[0],[-1]]
/-- Article: proposed positive denominator for hSImag. -/
def hSImagDenominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hSImagRaw : RationalCode Source.domain (fun z => ((((1/2) : ℚ) : ℝ)*(z.2)⁻¹*((z.1)⁻¹)^2*((z.1)^2+((((-1) : ℚ) : ℝ)*(z.2)^2)))) :=
  ((((RationalCode.constant Source.domain (1/2)).mul ((RationalCode.second Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))).mul (((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity)).pow 2)).mul (((RationalCode.first Source.domain).pow 2).add ((RationalCode.constant Source.domain (-1)).mul ((RationalCode.second Source.domain).pow 2))))
private theorem hSImagIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((1/2) : ℚ) : ℝ)*(z.2)⁻¹*((z.1)⁻¹)^2*((z.1)^2+((((-1) : ℚ) : ℝ)*(z.2)^2)))=Source.multiplierImag z.1 z.2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.multiplierImag]; ring
private theorem hSImagDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hSImagDenominator=true := by kernel_decide
private theorem hSImagDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hSImagDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hSImagDenominator hSImagDenCheck hz.1 hz.2).ne'
private theorem hSImagCross : equalCheck
    (mul hSImagRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hSImagDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hSImagNumerator) hSImagRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hSImag. -/
def hSImagCode : RationalCode Source.domain (fun z => Source.multiplierImag z.1 z.2) :=
  (hSImagRaw.congr hSImagIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hSImagNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hSImagDenominator)
    hSImagDenNonzero hSImagCross

/-- Article: proposed exact numerator for hDReal. -/
def hDRealNumerator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,1]]
/-- Article: proposed positive denominator for hDReal. -/
def hDRealDenominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDRealRaw : RationalCode Source.domain (fun z => (z.2*((((2 : ℚ) : ℝ)+(((2 : ℚ) : ℝ)*(z.1)^2)))⁻¹*(((2 : ℚ) : ℝ)+(z.1)^2))) :=
  (((RationalCode.second Source.domain).mul (((RationalCode.constant Source.domain 2).add ((RationalCode.constant Source.domain 2).mul ((RationalCode.first Source.domain).pow 2))).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))).mul ((RationalCode.constant Source.domain 2).add ((RationalCode.first Source.domain).pow 2)))
private theorem hDRealIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (z.2*((((2 : ℚ) : ℝ)+(((2 : ℚ) : ℝ)*(z.1)^2)))⁻¹*(((2 : ℚ) : ℝ)+(z.1)^2))=Source.defectReal z.1 z.2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.defectReal]; ring
private theorem hDRealDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDRealDenominator=true := by kernel_decide
private theorem hDRealDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDRealDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDRealDenominator hDRealDenCheck hz.1 hz.2).ne'
private theorem hDRealCross : equalCheck
    (mul hDRealRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDRealDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDRealNumerator) hDRealRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDReal. -/
def hDRealCode : RationalCode Source.domain (fun z => Source.defectReal z.1 z.2) :=
  (hDRealRaw.congr hDRealIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDRealNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDRealDenominator)
    hDRealDenNonzero hDRealCross

/-- Article: proposed exact numerator for hDImag. -/
def hDImagNumerator : polyak.Numerics.IntegerBivariate.Source := [[0],[1]]
/-- Article: proposed positive denominator for hDImag. -/
def hDImagDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDImagRaw : RationalCode Source.domain (fun z => ((((1/2) : ℚ) : ℝ)*z.2*((z.1)⁻¹)^2)) :=
  (((RationalCode.constant Source.domain (1/2)).mul (RationalCode.second Source.domain)).mul (((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity)).pow 2))
private theorem hDImagIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((1/2) : ℚ) : ℝ)*z.2*((z.1)⁻¹)^2)=Source.defectImag z.1 z.2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.defectImag]; ring
private theorem hDImagDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDImagDenominator=true := by kernel_decide
private theorem hDImagDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDImagDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDImagDenominator hDImagDenCheck hz.1 hz.2).ne'
private theorem hDImagCross : equalCheck
    (mul hDImagRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDImagDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDImagNumerator) hDImagRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDImag. -/
def hDImagCode : RationalCode Source.domain (fun z => Source.defectImag z.1 z.2) :=
  (hDImagRaw.congr hDImagIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDImagNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDImagDenominator)
    hDImagDenNonzero hDImagCross

/-- Article: proposed exact numerator for hDNorm. -/
def hDNormNumerator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[1,0,4,0,1]]
/-- Article: proposed positive denominator for hDNorm. -/
def hDNormDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,4,0,4]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDNormRaw : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2))^2+((Source.imaginarySquare z.1)*((Source.defectImag z.1 z.2))^2))) :=
  ((hDRealCode.pow 2).add (hImSqCode.mul (hDImagCode.pow 2)))
private theorem hDNormIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.defectReal z.1 z.2))^2+((Source.imaginarySquare z.1)*((Source.defectImag z.1 z.2))^2))=Source.defectNorm z.1 z.2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem hDNormDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDNormDenominator=true := by kernel_decide
private theorem hDNormDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDNormDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDNormDenominator hDNormDenCheck hz.1 hz.2).ne'
private theorem hDNormCross : equalCheck
    (mul hDNormRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDNormDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDNormNumerator) hDNormRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDNorm. -/
def hDNormCode : RationalCode Source.domain (fun z => Source.defectNorm z.1 z.2) :=
  (hDNormRaw.congr hDNormIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDNormNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDNormDenominator)
    hDNormDenNonzero hDNormCross

end
end polyak.Certificates.Startup.Codes
