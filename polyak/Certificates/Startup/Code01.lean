import polyak.Certificates.Startup.Code00

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: proposed exact numerator for hReserve. -/
def hReserveNumerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[0],[0],[-2],[0],[0],[0],[1]]
/-- Article: proposed positive denominator for hReserve. -/
def hReserveDenominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hReserveRaw : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2) :=
  (((RationalCode.constant Source.domain 1).add ((RationalCode.constant Source.domain (-1)).mul ((RationalCode.second Source.domain).pow 4))).pow 2)
private theorem hReserveIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2=Source.reserve z.2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.reserve]; ring
private theorem hReserveDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hReserveDenominator=true := by kernel_decide
private theorem hReserveDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hReserveDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hReserveDenominator hReserveDenCheck hz.1 hz.2).ne'
private theorem hReserveCross : equalCheck
    (mul hReserveRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hReserveDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hReserveNumerator) hReserveRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hReserve. -/
def hReserveCode : RationalCode Source.domain (fun z => Source.reserve z.2) :=
  (hReserveRaw.congr hReserveIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hReserveNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hReserveDenominator)
    hReserveDenNonzero hReserveCross

/-- Article: proposed exact numerator for hEpsilon. -/
def hEpsilonNumerator : polyak.Numerics.IntegerBivariate.Source := [[-3,-6,0,6,3]]
/-- Article: proposed positive denominator for hEpsilon. -/
def hEpsilonDenominator : polyak.Numerics.IntegerBivariate.Source := [[0,40,0,40]]
/-- Article: composition of proved source-preserving rational operations. -/
def hEpsilonRaw : RationalCode Source.domain (fun z => ((z.1)⁻¹*((((1 : ℚ) : ℝ)+z.1))^2*((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹*((((-3/40) : ℚ) : ℝ)+((((3/40) : ℚ) : ℝ)*(z.1)^2)))) :=
  (((((RationalCode.first Source.domain).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity)).mul (((RationalCode.constant Source.domain 1).add (RationalCode.first Source.domain)).pow 2)).mul (((RationalCode.constant Source.domain 1).add ((RationalCode.first Source.domain).pow 2)).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))).mul ((RationalCode.constant Source.domain (-3/40)).add ((RationalCode.constant Source.domain (3/40)).mul ((RationalCode.first Source.domain).pow 2))))
private theorem hEpsilonIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((z.1)⁻¹*((((1 : ℚ) : ℝ)+z.1))^2*((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹*((((-3/40) : ℚ) : ℝ)+((((3/40) : ℚ) : ℝ)*(z.1)^2)))=phaseBudget z.1 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [phaseBudget]; field_simp; ring
private theorem hEpsilonDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hEpsilonDenominator=true := by kernel_decide
private theorem hEpsilonDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hEpsilonDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hEpsilonDenominator hEpsilonDenCheck hz.1 hz.2).ne'
private theorem hEpsilonCross : equalCheck
    (mul hEpsilonRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hEpsilonDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hEpsilonNumerator) hEpsilonRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hEpsilon. -/
def hEpsilonCode : RationalCode Source.domain (fun z => phaseBudget z.1) :=
  (hEpsilonRaw.congr hEpsilonIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hEpsilonNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hEpsilonDenominator)
    hEpsilonDenNonzero hEpsilonCross

/-- Article: proposed exact numerator for hValue. -/
def hValueNumerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-2,0,-1],[0,-2,2,0,-2,2],[-1,0,-2,0,-1]]
/-- Article: proposed positive denominator for hValue. -/
def hValueDenominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: composition of proved source-preserving rational operations. -/
def hValueRaw : RationalCode Source.domain (fun z => (((((1/2) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))+((((1/4) : ℚ) : ℝ)*(Source.gap z.1)*((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹*((((-1) : ℚ) : ℝ)+(z.1)^2)))) :=
  (((RationalCode.constant Source.domain (1/2)).mul hSRealCode).add ((((RationalCode.constant Source.domain (1/4)).mul hGapCode).mul (((RationalCode.constant Source.domain 1).add ((RationalCode.first Source.domain).pow 2)).invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      
      positivity))).mul ((RationalCode.constant Source.domain (-1)).add ((RationalCode.first Source.domain).pow 2))))
private theorem hValueIdentity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((1/2) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))+((((1/4) : ℚ) : ℝ)*(Source.gap z.1)*((((1 : ℚ) : ℝ)+(z.1)^2))⁻¹*((((-1) : ℚ) : ℝ)+(z.1)^2)))=Source.valueConstant z.1 z.2 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.valueConstant]; field_simp; ring
private theorem hValueDenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hValueDenominator=true := by kernel_decide
private theorem hValueDenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hValueDenominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hValueDenominator hValueDenCheck hz.1 hz.2).ne'
private theorem hValueCross : equalCheck
    (mul hValueRaw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hValueDenominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hValueNumerator) hValueRaw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hValue. -/
def hValueCode : RationalCode Source.domain (fun z => Source.valueConstant z.1 z.2) :=
  (hValueRaw.congr hValueIdentity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hValueNumerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hValueDenominator)
    hValueDenNonzero hValueCross

/-- Article: proposed exact numerator for hT0. -/
def hT0Numerator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: proposed positive denominator for hT0. -/
def hT0Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hT0Raw : RationalCode Source.domain (fun _ => ((1 : ℚ) : ℝ)) :=
  (RationalCode.constant Source.domain 1)
private theorem hT0Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((1 : ℚ) : ℝ)=polyak.Spectral.chebT 0 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    norm_num [polyak.Spectral.chebT]
private theorem hT0DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hT0Denominator=true := by kernel_decide
private theorem hT0DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hT0Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hT0Denominator hT0DenCheck hz.1 hz.2).ne'
private theorem hT0Cross : equalCheck
    (mul hT0Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hT0Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hT0Numerator) hT0Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hT0. -/
def hT0Code : RationalCode Source.domain (fun z => polyak.Spectral.chebT 0 (radialCosine z.1)) :=
  (hT0Raw.congr hT0Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hT0Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hT0Denominator)
    hT0DenNonzero hT0Cross

/-- Article: proposed exact numerator for hT1. -/
def hT1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-1]]
/-- Article: proposed positive denominator for hT1. -/
def hT1Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hT1Raw : RationalCode Source.domain (fun z => (radialCosine z.1)) :=
  hCosCode
private theorem hT1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (radialCosine z.1)=polyak.Spectral.chebT 1 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    norm_num [polyak.Spectral.chebT]
private theorem hT1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hT1Denominator=true := by kernel_decide
private theorem hT1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hT1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hT1Denominator hT1DenCheck hz.1 hz.2).ne'
private theorem hT1Cross : equalCheck
    (mul hT1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hT1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hT1Numerator) hT1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hT1. -/
def hT1Code : RationalCode Source.domain (fun z => polyak.Spectral.chebT 1 (radialCosine z.1)) :=
  (hT1Raw.congr hT1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hT1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hT1Denominator)
    hT1DenNonzero hT1Cross

/-- Article: proposed exact numerator for hT2. -/
def hT2Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,0,0,-1]]
/-- Article: proposed positive denominator for hT2. -/
def hT2Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hT2Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 0 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 1 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hT0Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hT1Code))
private theorem hT2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 0 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 1 (radialCosine z.1))))=polyak.Spectral.chebT 2 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebT_rec 0]; ring
private theorem hT2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hT2Denominator=true := by kernel_decide
private theorem hT2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hT2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hT2Denominator hT2DenCheck hz.1 hz.2).ne'
private theorem hT2Cross : equalCheck
    (mul hT2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hT2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hT2Numerator) hT2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hT2. -/
def hT2Code : RationalCode Source.domain (fun z => polyak.Spectral.chebT 2 (radialCosine z.1)) :=
  (hT2Raw.congr hT2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hT2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hT2Denominator)
    hT2DenNonzero hT2Cross

/-- Article: proposed exact numerator for hT3. -/
def hT3Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,3,0,2,0,3]]
/-- Article: proposed positive denominator for hT3. -/
def hT3Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hT3Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 1 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 2 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hT1Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hT2Code))
private theorem hT3Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 1 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 2 (radialCosine z.1))))=polyak.Spectral.chebT 3 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebT_rec 1]; ring
private theorem hT3DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hT3Denominator=true := by kernel_decide
private theorem hT3DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hT3Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hT3Denominator hT3DenCheck hz.1 hz.2).ne'
private theorem hT3Cross : equalCheck
    (mul hT3Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hT3Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hT3Numerator) hT3Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hT3. -/
def hT3Code : RationalCode Source.domain (fun z => polyak.Spectral.chebT 3 (radialCosine z.1)) :=
  (hT3Raw.congr hT3Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hT3Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hT3Denominator)
    hT3DenNonzero hT3Cross

/-- Article: proposed exact numerator for hT4. -/
def hT4Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,-4,0,-2,0,-4,0,1]]
/-- Article: proposed positive denominator for hT4. -/
def hT4Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hT4Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 2 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 3 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hT2Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hT3Code))
private theorem hT4Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 2 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 3 (radialCosine z.1))))=polyak.Spectral.chebT 4 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebT_rec 2]; ring
private theorem hT4DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hT4Denominator=true := by kernel_decide
private theorem hT4DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hT4Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hT4Denominator hT4DenCheck hz.1 hz.2).ne'
private theorem hT4Cross : equalCheck
    (mul hT4Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hT4Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hT4Numerator) hT4Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hT4. -/
def hT4Code : RationalCode Source.domain (fun z => polyak.Spectral.chebT 4 (radialCosine z.1)) :=
  (hT4Raw.congr hT4Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hT4Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hT4Denominator)
    hT4DenNonzero hT4Cross

/-- Article: proposed exact numerator for hT5. -/
def hT5Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-5,0,0,0,-6,0,0,0,-5]]
/-- Article: proposed positive denominator for hT5. -/
def hT5Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hT5Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 3 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 4 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hT3Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hT4Code))
private theorem hT5Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 3 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 4 (radialCosine z.1))))=polyak.Spectral.chebT 5 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebT_rec 3]; ring
private theorem hT5DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hT5Denominator=true := by kernel_decide
private theorem hT5DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hT5Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hT5Denominator hT5DenCheck hz.1 hz.2).ne'
private theorem hT5Cross : equalCheck
    (mul hT5Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hT5Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hT5Numerator) hT5Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hT5. -/
def hT5Code : RationalCode Source.domain (fun z => polyak.Spectral.chebT 5 (radialCosine z.1)) :=
  (hT5Raw.congr hT5Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hT5Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hT5Denominator)
    hT5DenNonzero hT5Cross

/-- Article: proposed exact numerator for hT6. -/
def hT6Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,12,0,9,0,24,0,9,0,12,0,-1]]
/-- Article: proposed positive denominator for hT6. -/
def hT6Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hT6Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 4 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 5 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hT4Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hT5Code))
private theorem hT6Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 4 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 5 (radialCosine z.1))))=polyak.Spectral.chebT 6 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebT_rec 4]; ring
private theorem hT6DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hT6Denominator=true := by kernel_decide
private theorem hT6DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hT6Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hT6Denominator hT6DenCheck hz.1 hz.2).ne'
private theorem hT6Cross : equalCheck
    (mul hT6Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hT6Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hT6Numerator) hT6Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hT6. -/
def hT6Code : RationalCode Source.domain (fun z => polyak.Spectral.chebT 6 (radialCosine z.1)) :=
  (hT6Raw.congr hT6Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hT6Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hT6Denominator)
    hT6DenNonzero hT6Cross

end
end polyak.Certificates.Startup.Codes
