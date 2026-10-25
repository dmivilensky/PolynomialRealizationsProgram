import polyak.Certificates.Startup.Code01

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: proposed exact numerator for hT7. -/
def hT7Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,7,0,-14,0,-7,0,-36,0,-7,0,-14,0,7]]
/-- Article: proposed positive denominator for hT7. -/
def hT7Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hT7Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 5 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 6 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hT5Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hT6Code))
private theorem hT7Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 5 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 6 (radialCosine z.1))))=polyak.Spectral.chebT 7 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebT_rec 5]; ring
private theorem hT7DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hT7Denominator=true := by kernel_decide
private theorem hT7DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hT7Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hT7Denominator hT7DenCheck hz.1 hz.2).ne'
private theorem hT7Cross : equalCheck
    (mul hT7Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hT7Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hT7Numerator) hT7Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hT7. -/
def hT7Code : RationalCode Source.domain (fun z => polyak.Spectral.chebT 7 (radialCosine z.1)) :=
  (hT7Raw.congr hT7Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hT7Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hT7Denominator)
    hT7DenNonzero hT7Cross

/-- Article: proposed exact numerator for hT8. -/
def hT8Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,-24,0,-4,0,-40,0,6,0,-40,0,-4,0,-24,0,1]]
/-- Article: proposed positive denominator for hT8. -/
def hT8Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hT8Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 6 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 7 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hT6Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hT7Code))
private theorem hT8Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 6 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 7 (radialCosine z.1))))=polyak.Spectral.chebT 8 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebT_rec 6]; ring
private theorem hT8DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hT8Denominator=true := by kernel_decide
private theorem hT8DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hT8Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hT8Denominator hT8DenCheck hz.1 hz.2).ne'
private theorem hT8Cross : equalCheck
    (mul hT8Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hT8Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hT8Numerator) hT8Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hT8. -/
def hT8Code : RationalCode Source.domain (fun z => polyak.Spectral.chebT 8 (radialCosine z.1)) :=
  (hT8Raw.congr hT8Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hT8Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hT8Denominator)
    hT8DenNonzero hT8Cross

/-- Article: proposed exact numerator for hT9. -/
def hT9Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-9,0,48,0,36,0,144,0,74,0,144,0,36,0,48,0,-9]]
/-- Article: proposed positive denominator for hT9. -/
def hT9Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hT9Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 7 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 8 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hT7Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hT8Code))
private theorem hT9Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebT 7 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebT 8 (radialCosine z.1))))=polyak.Spectral.chebT 9 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebT_rec 7]; ring
private theorem hT9DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hT9Denominator=true := by kernel_decide
private theorem hT9DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hT9Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hT9Denominator hT9DenCheck hz.1 hz.2).ne'
private theorem hT9Cross : equalCheck
    (mul hT9Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hT9Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hT9Numerator) hT9Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hT9. -/
def hT9Code : RationalCode Source.domain (fun z => polyak.Spectral.chebT 9 (radialCosine z.1)) :=
  (hT9Raw.congr hT9Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hT9Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hT9Denominator)
    hT9DenNonzero hT9Cross

/-- Article: proposed exact numerator for hU0. -/
def hU0Numerator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: proposed positive denominator for hU0. -/
def hU0Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hU0Raw : RationalCode Source.domain (fun _ => ((1 : ℚ) : ℝ)) :=
  (RationalCode.constant Source.domain 1)
private theorem hU0Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((1 : ℚ) : ℝ)=polyak.Spectral.chebU 0 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    norm_num [polyak.Spectral.chebU]
private theorem hU0DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hU0Denominator=true := by kernel_decide
private theorem hU0DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hU0Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hU0Denominator hU0DenCheck hz.1 hz.2).ne'
private theorem hU0Cross : equalCheck
    (mul hU0Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hU0Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hU0Numerator) hU0Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hU0. -/
def hU0Code : RationalCode Source.domain (fun z => polyak.Spectral.chebU 0 (radialCosine z.1)) :=
  (hU0Raw.congr hU0Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hU0Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hU0Denominator)
    hU0DenNonzero hU0Cross

/-- Article: proposed exact numerator for hU1. -/
def hU1Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-2]]
/-- Article: proposed positive denominator for hU1. -/
def hU1Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hU1Raw : RationalCode Source.domain (fun z => (((2 : ℚ) : ℝ)*(radialCosine z.1))) :=
  ((RationalCode.constant Source.domain 2).mul hCosCode)
private theorem hU1Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((2 : ℚ) : ℝ)*(radialCosine z.1))=polyak.Spectral.chebU 1 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    norm_num [polyak.Spectral.chebU]
private theorem hU1DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hU1Denominator=true := by kernel_decide
private theorem hU1DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hU1Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hU1Denominator hU1DenCheck hz.1 hz.2).ne'
private theorem hU1Cross : equalCheck
    (mul hU1Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hU1Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hU1Numerator) hU1Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hU1. -/
def hU1Code : RationalCode Source.domain (fun z => polyak.Spectral.chebU 1 (radialCosine z.1)) :=
  (hU1Raw.congr hU1Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hU1Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hU1Denominator)
    hU1DenNonzero hU1Cross

/-- Article: proposed exact numerator for hU2. -/
def hU2Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,2,0,-1]]
/-- Article: proposed positive denominator for hU2. -/
def hU2Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hU2Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 0 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 1 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hU0Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hU1Code))
private theorem hU2Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 0 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 1 (radialCosine z.1))))=polyak.Spectral.chebU 2 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebU_rec 0]; ring
private theorem hU2DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hU2Denominator=true := by kernel_decide
private theorem hU2DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hU2Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hU2Denominator hU2DenCheck hz.1 hz.2).ne'
private theorem hU2Cross : equalCheck
    (mul hU2Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hU2Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hU2Numerator) hU2Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hU2. -/
def hU2Code : RationalCode Source.domain (fun z => polyak.Spectral.chebU 2 (radialCosine z.1)) :=
  (hU2Raw.congr hU2Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hU2Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hU2Denominator)
    hU2DenNonzero hU2Cross

/-- Article: proposed exact numerator for hU3. -/
def hU3Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,4,0,0,0,4]]
/-- Article: proposed positive denominator for hU3. -/
def hU3Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hU3Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 1 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 2 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hU1Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hU2Code))
private theorem hU3Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 1 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 2 (radialCosine z.1))))=polyak.Spectral.chebU 3 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebU_rec 1]; ring
private theorem hU3DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hU3Denominator=true := by kernel_decide
private theorem hU3DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hU3Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hU3Denominator hU3DenCheck hz.1 hz.2).ne'
private theorem hU3Cross : equalCheck
    (mul hU3Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hU3Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hU3Numerator) hU3Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hU3. -/
def hU3Code : RationalCode Source.domain (fun z => polyak.Spectral.chebU 3 (radialCosine z.1)) :=
  (hU3Raw.congr hU3Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hU3Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hU3Denominator)
    hU3DenNonzero hU3Cross

/-- Article: proposed exact numerator for hU4. -/
def hU4Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,-8,0,-2,0,-8,0,1]]
/-- Article: proposed positive denominator for hU4. -/
def hU4Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hU4Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 2 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 3 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hU2Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hU3Code))
private theorem hU4Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 2 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 3 (radialCosine z.1))))=polyak.Spectral.chebU 4 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebU_rec 2]; ring
private theorem hU4DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hU4Denominator=true := by kernel_decide
private theorem hU4DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hU4Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hU4Denominator hU4DenCheck hz.1 hz.2).ne'
private theorem hU4Cross : equalCheck
    (mul hU4Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hU4Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hU4Numerator) hU4Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hU4. -/
def hU4Code : RationalCode Source.domain (fun z => polyak.Spectral.chebU 4 (radialCosine z.1)) :=
  (hU4Raw.congr hU4Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hU4Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hU4Denominator)
    hU4DenNonzero hU4Cross

/-- Article: proposed exact numerator for hU5. -/
def hU5Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-6,0,8,0,-4,0,8,0,-6]]
/-- Article: proposed positive denominator for hU5. -/
def hU5Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hU5Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 3 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 4 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hU3Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hU4Code))
private theorem hU5Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 3 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 4 (radialCosine z.1))))=polyak.Spectral.chebU 5 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebU_rec 3]; ring
private theorem hU5DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hU5Denominator=true := by kernel_decide
private theorem hU5DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hU5Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hU5Denominator hU5DenCheck hz.1 hz.2).ne'
private theorem hU5Cross : equalCheck
    (mul hU5Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hU5Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hU5Numerator) hU5Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hU5. -/
def hU5Code : RationalCode Source.domain (fun z => polyak.Spectral.chebU 5 (radialCosine z.1)) :=
  (hU5Raw.congr hU5Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hU5Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hU5Denominator)
    hU5DenNonzero hU5Cross

/-- Article: proposed exact numerator for hU6. -/
def hU6Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,18,0,1,0,28,0,1,0,18,0,-1]]
/-- Article: proposed positive denominator for hU6. -/
def hU6Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hU6Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 4 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 5 (radialCosine z.1))))) :=
  (((RationalCode.constant Source.domain (-1)).mul hU4Code).add (((RationalCode.constant Source.domain 2).mul hCosCode).mul hU5Code))
private theorem hU6Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(polyak.Spectral.chebU 4 (radialCosine z.1)))+(((2 : ℚ) : ℝ)*(radialCosine z.1)*(polyak.Spectral.chebU 5 (radialCosine z.1))))=polyak.Spectral.chebU 6 (radialCosine z.1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.chebU_rec 4]; ring
private theorem hU6DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hU6Denominator=true := by kernel_decide
private theorem hU6DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hU6Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hU6Denominator hU6DenCheck hz.1 hz.2).ne'
private theorem hU6Cross : equalCheck
    (mul hU6Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hU6Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hU6Numerator) hU6Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hU6. -/
def hU6Code : RationalCode Source.domain (fun z => polyak.Spectral.chebU 6 (radialCosine z.1)) :=
  (hU6Raw.congr hU6Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hU6Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hU6Denominator)
    hU6DenNonzero hU6Cross

end
end polyak.Certificates.Startup.Codes
