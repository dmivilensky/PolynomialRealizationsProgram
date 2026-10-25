import polyak.Certificates.Startup.Code06

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: canonical numerator for one arithmetic source node. -/
def hAst098Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,2,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst098Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst098Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 2 (radialCosine z.1))*(z.1)^2)) :=
  (hU2Code.mul hAst031Code)
private theorem hAst098DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst098Denominator=true := by kernel_decide
private theorem hAst098DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst098Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst098Denominator hAst098DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst098Cross : equalCheck
    (mul hAst098Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst098Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst098Numerator) hAst098Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst098Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 2 (radialCosine z.1))*(z.1)^2)) :=
  hAst098Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst098Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst098Denominator)
    hAst098DenNonzero hAst098Cross

/-- Article: proposed exact numerator for hPowerImag3. -/
def hPowerImag3Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,2,0,-1]]
/-- Article: proposed positive denominator for hPowerImag3. -/
def hPowerImag3Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,2,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerImag3Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 2 (radialCosine z.1))*(z.1)^2)) :=
  (hAst098Code.congr (by
    intro z hz
    ring))
private theorem hPowerImag3Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebU 2 (radialCosine z.1))*(z.1)^2)=Source.powerImag z.1 3 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.powerImag,ite_eq_right (by decide)]; ring
private theorem hPowerImag3DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerImag3Denominator=true := by kernel_decide
private theorem hPowerImag3DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag3Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerImag3Denominator hPowerImag3DenCheck hz.1 hz.2).ne'
private theorem hPowerImag3Cross : equalCheck
    (mul hPowerImag3Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag3Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag3Numerator) hPowerImag3Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerImag3. -/
def hPowerImag3Code : RationalCode Source.domain (fun z => Source.powerImag z.1 3) :=
  (hPowerImag3Raw.congr hPowerImag3Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag3Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag3Denominator)
    hPowerImag3DenNonzero hPowerImag3Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst099Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-3,0,-2,0,-3],[0],[0,0,0,0,-3,0,-2,0,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst099Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst099Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 3)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerReal3Code.mul hSRealCode)
private theorem hAst099DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst099Denominator=true := by kernel_decide
private theorem hAst099DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst099Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst099Denominator hAst099DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst099Cross : equalCheck
    (mul hAst099Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst099Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst099Numerator) hAst099Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst099Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 3)*(Source.multiplierReal z.1 z.2))) :=
  hAst099Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst099Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst099Denominator)
    hAst099DenNonzero hAst099Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst100Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-1,0,0,0,-1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst100Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst100Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))) :=
  (hAst002Code.mul hPowerImag3Code)
private theorem hAst100DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst100Denominator=true := by kernel_decide
private theorem hAst100DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst100Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst100Denominator hAst100DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst100Cross : equalCheck
    (mul hAst100Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst100Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst100Numerator) hAst100Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst100Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))) :=
  hAst100Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst100Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst100Denominator)
    hAst100DenNonzero hAst100Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst101Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-1,0,0,0,-1,0,1],[0],[0,0,-1,0,1,0,0,0,1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst101Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst101Raw : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))*(Source.multiplierImag z.1 z.2))) :=
  (hAst100Code.mul hSImagCode)
private theorem hAst101DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst101Denominator=true := by kernel_decide
private theorem hAst101DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst101Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst101Denominator hAst101DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst101Cross : equalCheck
    (mul hAst101Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst101Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst101Numerator) hAst101Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst101Code : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))*(Source.multiplierImag z.1 z.2))) :=
  hAst101Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst101Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst101Denominator)
    hAst101DenNonzero hAst101Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst102Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-4,0,-2,0,-4,0,1],[0],[0,0,-1,0,-2,0,-2,0,-2,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst102Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst102Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 3)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))*(Source.multiplierImag z.1 z.2)))) :=
  (hAst099Code.add hAst101Code)
private theorem hAst102DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst102Denominator=true := by kernel_decide
private theorem hAst102DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst102Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst102Denominator hAst102DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst102Cross : equalCheck
    (mul hAst102Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst102Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst102Numerator) hAst102Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst102Code : RationalCode Source.domain (fun z => (((Source.powerReal z.1 3)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))*(Source.multiplierImag z.1 z.2)))) :=
  hAst102Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst102Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst102Denominator)
    hAst102DenNonzero hAst102Cross

/-- Article: proposed exact numerator for hGradientReal3. -/
def hGradientReal3Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-4,0,-2,0,-4,0,1],[0],[0,0,-1,0,-2,0,-2,0,-2,0,-1]]
/-- Article: proposed positive denominator for hGradientReal3. -/
def hGradientReal3Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientReal3Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 3)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 3)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst102Code.congr (by
    intro z hz
    ring))
private theorem hGradientReal3Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerReal z.1 3)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 3)*(Source.multiplierImag z.1 z.2)))=Source.gradientReal z.1 z.2 3 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientReal]; ring
private theorem hGradientReal3DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientReal3Denominator=true := by kernel_decide
private theorem hGradientReal3DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal3Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientReal3Denominator hGradientReal3DenCheck hz.1 hz.2).ne'
private theorem hGradientReal3Cross : equalCheck
    (mul hGradientReal3Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal3Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal3Numerator) hGradientReal3Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientReal3. -/
def hGradientReal3Code : RationalCode Source.domain (fun z => Source.gradientReal z.1 z.2 3) :=
  (hGradientReal3Raw.congr hGradientReal3Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal3Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal3Denominator)
    hGradientReal3DenNonzero hGradientReal3Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst103Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-2,0,1],[0],[0,0,1,0,-2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst103Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst103Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 3)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerImag3Code.mul hSRealCode)
private theorem hAst103DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst103Denominator=true := by kernel_decide
private theorem hAst103DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst103Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst103Denominator hAst103DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst103Cross : equalCheck
    (mul hAst103Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst103Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst103Numerator) hAst103Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst103Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 3)*(Source.multiplierReal z.1 z.2))) :=
  hAst103Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst103Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst103Denominator)
    hAst103DenNonzero hAst103Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst104Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,3,0,2,0,3],[0],[0,0,-3,0,-2,0,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst104Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst104Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 3)*(Source.multiplierImag z.1 z.2))) :=
  (hPowerReal3Code.mul hSImagCode)
private theorem hAst104DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst104Denominator=true := by kernel_decide
private theorem hAst104DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst104Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst104Denominator hAst104DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst104Cross : equalCheck
    (mul hAst104Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst104Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst104Numerator) hAst104Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst104Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 3)*(Source.multiplierImag z.1 z.2))) :=
  hAst104Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst104Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst104Denominator)
    hAst104DenNonzero hAst104Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst105Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,2,0,0,0,2],[0],[0,0,-1,0,-2,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst105Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst105Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 3)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 3)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst103Code.add hAst104Code)
private theorem hAst105DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst105Denominator=true := by kernel_decide
private theorem hAst105DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst105Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst105Denominator hAst105DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst105Cross : equalCheck
    (mul hAst105Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst105Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst105Numerator) hAst105Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst105Code : RationalCode Source.domain (fun z => (((Source.powerImag z.1 3)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 3)*(Source.multiplierImag z.1 z.2)))) :=
  hAst105Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst105Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst105Denominator)
    hAst105DenNonzero hAst105Cross

/-- Article: proposed exact numerator for hGradientImag3. -/
def hGradientImag3Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,2,0,0,0,2],[0],[0,0,-1,0,-2,0,-1]]
/-- Article: proposed positive denominator for hGradientImag3. -/
def hGradientImag3Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,3,0,3,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientImag3Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 3)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 3)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst105Code.congr (by
    intro z hz
    ring))
private theorem hGradientImag3Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerImag z.1 3)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 3)*(Source.multiplierImag z.1 z.2)))=Source.gradientImag z.1 z.2 3 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientImag]; ring
private theorem hGradientImag3DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientImag3Denominator=true := by kernel_decide
private theorem hGradientImag3DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag3Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientImag3Denominator hGradientImag3DenCheck hz.1 hz.2).ne'
private theorem hGradientImag3Cross : equalCheck
    (mul hGradientImag3Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag3Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag3Numerator) hGradientImag3Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientImag3. -/
def hGradientImag3Code : RationalCode Source.domain (fun z => Source.gradientImag z.1 z.2 3) :=
  (hGradientImag3Raw.congr hGradientImag3Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag3Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag3Denominator)
    hGradientImag3DenNonzero hGradientImag3Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst106Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-4,0,-2,0,-4,0,1],[0],[-2,0,-8,0,-11,0,-7,0,-3,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst106Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst106Raw : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  (hGradientReal3Code.add hAst009Code)
private theorem hAst106DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst106Denominator=true := by kernel_decide
private theorem hAst106DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst106Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst106Denominator hAst106DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst106Cross : equalCheck
    (mul hAst106Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst106Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst106Numerator) hAst106Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst106Code : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  hAst106Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst106Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst106Denominator)
    hAst106DenNonzero hAst106Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst107Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,4,0,-1,0,-1,0,-4,0,1],[0],[-1,0,-5,0,-8,0,-6,0,-3,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst107Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst107Raw : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  (hAst106Code.add hAst010Code)
private theorem hAst107DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst107Denominator=true := by kernel_decide
private theorem hAst107DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst107Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst107Denominator hAst107DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst107Cross : equalCheck
    (mul hAst107Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst107Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst107Numerator) hAst107Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst107Code : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  hAst107Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst107Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst107Denominator)
    hAst107DenNonzero hAst107Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst108Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,8,0,14,0,-10,0,-15,0,-28,0,17,0,6,0,14,0,-8,0,1],[0],[0,0,-2,0,-18,0,-54,0,-64,0,-20,0,40,0,64,0,40,0,14,0,2,0,-2],[0],[1,0,10,0,41,0,92,0,130,0,128,0,94,0,52,0,21,0,6,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst108Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,32,0,112,0,224,0,280,0,224,0,112,0,32,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst108Raw : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  (hAst107Code.pow 2)
private theorem hAst108DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst108Denominator=true := by kernel_decide
private theorem hAst108DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst108Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst108Denominator hAst108DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst108Cross : equalCheck
    (mul hAst108Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst108Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst108Numerator) hAst108Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst108Code : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  hAst108Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst108Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst108Denominator)
    hAst108DenNonzero hAst108Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst109Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-8,0,-14,0,10,0,15,0,28,0,-17,0,-6,0,-14,0,8,0,-1],[0],[0,0,2,0,18,0,54,0,64,0,20,0,-40,0,-64,0,-40,0,-14,0,-2,0,2],[0],[-1,0,-10,0,-41,0,-92,0,-130,0,-128,0,-94,0,-52,0,-21,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst109Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst109Raw : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  ((RationalCode.constant Source.domain (-1/4)).mul hAst108Code)
private theorem hAst109DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst109Denominator=true := by kernel_decide
private theorem hAst109DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst109Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst109Denominator hAst109DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst109Cross : equalCheck
    (mul hAst109Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst109Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst109Numerator) hAst109Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst109Code : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  hAst109Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst109Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst109Denominator)
    hAst109DenNonzero hAst109Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst110Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-3,0,0,0,1,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst110Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst110Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3))) :=
  ((RationalCode.constant Source.domain (-1)).add hPowerReal3Code)
private theorem hAst110DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst110Denominator=true := by kernel_decide
private theorem hAst110DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst110Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst110Denominator hAst110DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst110Cross : equalCheck
    (mul hAst110Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst110Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst110Numerator) hAst110Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst110Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3))) :=
  hAst110Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst110Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst110Denominator)
    hAst110DenNonzero hAst110Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst111Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,9,0,-2,0,-12,0,-18,0,1,0,6,0,9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst111Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst111Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2) :=
  (hAst110Code.pow 2)
private theorem hAst111DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst111Denominator=true := by kernel_decide
private theorem hAst111DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst111Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst111Denominator hAst111DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst111Cross : equalCheck
    (mul hAst111Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst111Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst111Numerator) hAst111Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst111Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2) :=
  hAst111Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst111Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst111Denominator)
    hAst111DenNonzero hAst111Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst112Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,9,0,-2,0,-12,0,-18,0,1,0,6,0,9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst112Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,24,0,60,0,80,0,60,0,24,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst112Raw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2)) :=
  ((RationalCode.constant Source.domain (1/4)).mul hAst111Code)
private theorem hAst112DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst112Denominator=true := by kernel_decide
private theorem hAst112DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst112Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst112Denominator hAst112DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst112Cross : equalCheck
    (mul hAst112Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst112Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst112Numerator) hAst112Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst112Code : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2)) :=
  hAst112Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst112Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst112Denominator)
    hAst112DenNonzero hAst112Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst113Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,4,0,0,0,4],[0],[-1,0,-3,0,-5,0,-5,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst113Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst113Raw : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  (hGradientImag3Code.add hAst018Code)
private theorem hAst113DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst113Denominator=true := by kernel_decide
private theorem hAst113DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst113Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst113Denominator hAst113DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst113Cross : equalCheck
    (mul hAst113Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst113Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst113Numerator) hAst113Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst113Code : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  hAst113Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst113Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst113Denominator)
    hAst113DenNonzero hAst113Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst114Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-3,0,1,0,-1,0,4],[0],[0,0,-2,0,-4,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst114Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst114Raw : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst113Code.add hAst019Code)
private theorem hAst114DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst114Denominator=true := by kernel_decide
private theorem hAst114DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst114Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst114Denominator hAst114DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst114Cross : equalCheck
    (mul hAst114Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst114Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst114Numerator) hAst114Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst114Code : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  hAst114Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst114Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst114Denominator)
    hAst114DenNonzero hAst114Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst115Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,7,0,-4,0,-1,0,-26,0,9,0,-8,0,16],[0],[0,0,4,0,20,0,24,0,8,0,-12,0,-28,0,-16],[0],[0,0,0,0,4,0,16,0,24,0,16,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst115Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,24,0,60,0,80,0,60,0,24,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst115Raw : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  (hAst114Code.pow 2)
private theorem hAst115DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst115Denominator=true := by kernel_decide
private theorem hAst115DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst115Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst115Denominator hAst115DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst115Cross : equalCheck
    (mul hAst115Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst115Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst115Numerator) hAst115Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst115Code : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  hAst115Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst115Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst115Denominator)
    hAst115DenNonzero hAst115Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst116Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-14,0,-9,0,-2,0,31,0,18,0,25,0,-17,0,-8,0,-16],[0],[0,0,0,0,-4,0,-24,0,-48,0,-52,0,-20,0,32,0,56,0,44,0,16],[0],[0,0,0,0,0,0,-4,0,-20,0,-44,0,-56,0,-44,0,-20,0,-4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst116Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst116Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  (hAst023Code.mul hAst115Code)
private theorem hAst116DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst116Denominator=true := by kernel_decide
private theorem hAst116DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst116Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst116Denominator hAst116DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst116Cross : equalCheck
    (mul hAst116Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst116Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst116Numerator) hAst116Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst116Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  hAst116Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst116Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst116Denominator)
    hAst116DenNonzero hAst116Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst117Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-4,0,6,0,-4,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst117Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst117Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 3))^2) :=
  (hPowerImag3Code.pow 2)
private theorem hAst117DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst117Denominator=true := by kernel_decide
private theorem hAst117DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst117Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst117Denominator hAst117DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst117Cross : equalCheck
    (mul hAst117Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst117Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst117Numerator) hAst117Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst117Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 3))^2) :=
  hAst117Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst117Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst117Denominator)
    hAst117DenNonzero hAst117Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst118Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,1,0,-3,0,3,0,-2,0,3,0,-3,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst118Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,24,0,60,0,80,0,60,0,24,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst118Raw : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 3))^2)) :=
  (hAst026Code.mul hAst117Code)
private theorem hAst118DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst118Denominator=true := by kernel_decide
private theorem hAst118DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst118Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst118Denominator hAst118DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst118Cross : equalCheck
    (mul hAst118Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst118Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst118Numerator) hAst118Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst118Code : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 3))^2)) :=
  hAst118Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst118Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst118Denominator)
    hAst118DenNonzero hAst118Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst119Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-8,0,-14,0,10,0,15,0,28,0,-17,0,-6,0,-14,0,8,0,-1],[0],[4,0,34,0,106,0,142,0,36,0,-156,0,-228,0,-104,0,48,0,82,0,34,0,2],[0],[-1,0,-10,0,-41,0,-92,0,-130,0,-128,0,-94,0,-52,0,-21,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst119Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst119Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2))) :=
  (hAst109Code.add hAst112Code)
private theorem hAst119DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst119Denominator=true := by kernel_decide
private theorem hAst119DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst119Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst119Denominator hAst119DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst119Cross : equalCheck
    (mul hAst119Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst119Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst119Numerator) hAst119Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst119Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2))) :=
  hAst119Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst119Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst119Denominator)
    hAst119DenNonzero hAst119Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst120Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-9,0,1,0,15,0,15,0,1,0,-9,0,-6,0,-1],[0],[4,0,26,0,46,0,0,0,-58,0,-92,0,-6,0,32,0,46,0,2],[0],[-1,0,-8,0,-24,0,-40,0,-46,0,-40,0,-24,0,-8,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst120Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst120Raw : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  (hAst119Code.add hAst116Code)
private theorem hAst120DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst120Denominator=true := by kernel_decide
private theorem hAst120DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst120Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst120Denominator hAst120DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst120Cross : equalCheck
    (mul hAst120Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst120Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst120Numerator) hAst120Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst120Code : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  hAst120Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst120Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst120Denominator)
    hAst120DenNonzero hAst120Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst121Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,0,0,5,0,5,0,0,0,-4,0,-1],[0],[4,0,18,0,6,0,-26,0,-24,0,-6,0,22,0,6],[0],[-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst121Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst121Raw : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 3))^2))) :=
  (hAst120Code.add hAst118Code)
private theorem hAst121DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst121Denominator=true := by kernel_decide
private theorem hAst121DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst121Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst121Denominator hAst121DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst121Cross : equalCheck
    (mul hAst121Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst121Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst121Numerator) hAst121Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst121Code : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 3))^2))) :=
  hAst121Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst121Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst121Denominator)
    hAst121DenNonzero hAst121Cross

/-- Article: proposed exact numerator for hRadius3. -/
def hRadius3Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,0,0,5,0,5,0,0,0,-4,0,-1],[0],[4,0,18,0,6,0,-26,0,-24,0,-6,0,22,0,6],[0],[-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1]]
/-- Article: proposed positive denominator for hRadius3. -/
def hRadius3Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hRadius3Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 3))^2))) :=
  (hAst121Code.congr (by
    intro z hz
    ring))
private theorem hRadius3Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 3)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 3))^2))=Source.radius z.1 z.2 3 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.radius]; ring
private theorem hRadius3DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hRadius3Denominator=true := by kernel_decide
private theorem hRadius3DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hRadius3Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hRadius3Denominator hRadius3DenCheck hz.1 hz.2).ne'
private theorem hRadius3Cross : equalCheck
    (mul hRadius3Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hRadius3Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hRadius3Numerator) hRadius3Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hRadius3. -/
def hRadius3Code : RationalCode Source.domain (fun z => Source.radius z.1 z.2 3) :=
  (hRadius3Raw.congr hRadius3Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius3Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius3Denominator)
    hRadius3DenNonzero hRadius3Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst122Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst122Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst122Raw : RationalCode Source.domain (fun z => (z.1)^6) :=
  ((RationalCode.first Source.domain).pow 6)
private theorem hAst122DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst122Denominator=true := by kernel_decide
private theorem hAst122DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst122Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst122Denominator hAst122DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst122Cross : equalCheck
    (mul hAst122Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst122Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst122Numerator) hAst122Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst122Code : RationalCode Source.domain (fun z => (z.1)^6) :=
  hAst122Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst122Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst122Denominator)
    hAst122DenNonzero hAst122Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst123Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst123Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst123Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^6)) :=
  ((RationalCode.constant Source.domain (-1)).add hAst122Code)
private theorem hAst123DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst123Denominator=true := by kernel_decide
private theorem hAst123DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst123Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst123Denominator hAst123DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst123Cross : equalCheck
    (mul hAst123Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst123Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst123Numerator) hAst123Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst123Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^6)) :=
  hAst123Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst123Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst123Denominator)
    hAst123DenNonzero hAst123Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst124Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,2,0,1,0,-1,0,-2,0,-1],[0,2,-2,0,2,-2,0,-2,2,0,-2,2],[1,0,2,0,1,0,-1,0,-2,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst124Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst124Raw : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^6))) :=
  (hValueCode.mul hAst123Code)
private theorem hAst124DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst124Denominator=true := by kernel_decide
private theorem hAst124DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst124Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst124Denominator hAst124DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst124Cross : equalCheck
    (mul hAst124Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst124Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst124Numerator) hAst124Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst124Code : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^6))) :=
  hAst124Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst124Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst124Denominator)
    hAst124DenNonzero hAst124Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst125Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-4,0,-2,0,-4,0,1],[0],[2,0,6,0,7,0,3,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst125Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst125Raw : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3))) :=
  (hDRealCode.add hGradientReal3Code)
private theorem hAst125DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst125Denominator=true := by kernel_decide
private theorem hAst125DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst125Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst125Denominator hAst125DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst125Cross : equalCheck
    (mul hAst125Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst125Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst125Numerator) hAst125Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst125Code : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3))) :=
  hAst125Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst125Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst125Denominator)
    hAst125DenNonzero hAst125Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst126Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-2,0,-7,0,-3,0,-4,0,1],[0],[1,0,3,0,4,0,2,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst126Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst126Raw : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3))+(Source.multiplierReal z.1 z.2))) :=
  (hAst125Code.add hSRealCode)
private theorem hAst126DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst126Denominator=true := by kernel_decide
private theorem hAst126DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst126Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst126Denominator hAst126DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst126Cross : equalCheck
    (mul hAst126Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst126Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst126Numerator) hAst126Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst126Code : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3))+(Source.multiplierReal z.1 z.2))) :=
  hAst126Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst126Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst126Denominator)
    hAst126DenNonzero hAst126Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst127Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,0,0,-1,0,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst127Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst127Raw : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))) :=
  ((RationalCode.constant Source.domain (-1/2)).mul hAst110Code)
private theorem hAst127DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst127Denominator=true := by kernel_decide
private theorem hAst127DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst127Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst127Denominator hAst127DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst127Cross : equalCheck
    (mul hAst127Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst127Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst127Numerator) hAst127Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst127Code : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))) :=
  hAst127Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst127Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst127Denominator)
    hAst127DenNonzero hAst127Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst128Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-13,0,-23,0,-8,0,2,0,27,0,13,0,11,0,-3],[0],[1,0,6,0,13,0,13,0,-1,0,-17,0,-17,0,-5,0,4,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst128Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,28,0,84,0,140,0,140,0,84,0,28,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst128Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3))+(Source.multiplierReal z.1 z.2)))) :=
  (hAst127Code.mul hAst126Code)
private theorem hAst128DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst128Denominator=true := by kernel_decide
private theorem hAst128DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst128Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst128Denominator hAst128DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst128Cross : equalCheck
    (mul hAst128Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst128Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst128Numerator) hAst128Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst128Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3))+(Source.multiplierReal z.1 z.2)))) :=
  hAst128Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst128Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst128Denominator)
    hAst128DenNonzero hAst128Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst129Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,4,0,0,0,4],[0],[1,0,3,0,1,0,-3,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst129Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst129Raw : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 3))) :=
  (hDImagCode.add hGradientImag3Code)
private theorem hAst129DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst129Denominator=true := by kernel_decide
private theorem hAst129DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst129Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst129Denominator hAst129DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst129Cross : equalCheck
    (mul hAst129Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst129Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst129Numerator) hAst129Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst129Code : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 3))) :=
  hAst129Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst129Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst129Denominator)
    hAst129DenNonzero hAst129Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst130Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,7,0,1,0,4],[0],[0,0,-2,0,-4,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst130Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,6,0,6,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst130Raw : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 3))+(Source.multiplierImag z.1 z.2))) :=
  (hAst129Code.add hSImagCode)
private theorem hAst130DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst130Denominator=true := by kernel_decide
private theorem hAst130DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst130Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst130Denominator hAst130DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst130Cross : equalCheck
    (mul hAst130Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst130Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst130Numerator) hAst130Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst130Code : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 3))+(Source.multiplierImag z.1 z.2))) :=
  hAst130Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst130Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst130Denominator)
    hAst130DenNonzero hAst130Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst131Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-1,0,0,0,-1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst131Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst131Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))) :=
  (hAst040Code.mul hPowerImag3Code)
private theorem hAst131DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst131Denominator=true := by kernel_decide
private theorem hAst131DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst131Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst131Denominator hAst131DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst131Cross : equalCheck
    (mul hAst131Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst131Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst131Numerator) hAst131Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst131Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))) :=
  hAst131Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst131Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst131Denominator)
    hAst131DenNonzero hAst131Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst132Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,2,0,4,0,-7,0,1,0,-8,0,6,0,-3,0,4],[0],[0,0,0,0,0,0,-2,0,-2,0,2,0,4,0,2,0,-2,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst132Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,28,0,84,0,140,0,140,0,84,0,28,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst132Raw : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 3))+(Source.multiplierImag z.1 z.2)))) :=
  (hAst131Code.mul hAst130Code)
private theorem hAst132DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst132Denominator=true := by kernel_decide
private theorem hAst132DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst132Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst132Denominator hAst132DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst132Cross : equalCheck
    (mul hAst132Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst132Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst132Numerator) hAst132Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst132Code : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 3))+(Source.multiplierImag z.1 z.2)))) :=
  hAst132Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst132Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst132Denominator)
    hAst132DenNonzero hAst132Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst133Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,2,0,-4,0,1,0,-7,0,8,0,-2,0,5,0,-4],[0,2,-2,8,-6,10,-4,-2,6,-18,12,-18,6,-2,-4,10,-6,8,-2,2],[2,0,12,0,28,0,32,0,8,0,-26,0,-36,0,-20,0,-2,0,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst133Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,28,0,84,0,140,0,140,0,84,0,28,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst133Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^6))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3))+(Source.multiplierReal z.1 z.2))))) :=
  (hAst124Code.add hAst128Code)
private theorem hAst133DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst133Denominator=true := by kernel_decide
private theorem hAst133DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst133Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst133Denominator hAst133DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst133Cross : equalCheck
    (mul hAst133Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst133Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst133Numerator) hAst133Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst133Code : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^6))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3))+(Source.multiplierReal z.1 z.2))))) :=
  hAst133Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst133Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst133Denominator)
    hAst133DenNonzero hAst133Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst134Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-1,0,0,0,-1,0,1],[0,1,-1,1,0,-1,1,-2,1,-1,0,1,-1,1],[1,0,3,0,2,0,-1,0,-3,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst134Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst134Raw : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^6))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 3))+(Source.multiplierImag z.1 z.2))))) :=
  (hAst133Code.add hAst132Code)
private theorem hAst134DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst134Denominator=true := by kernel_decide
private theorem hAst134DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst134Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst134Denominator hAst134DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst134Cross : equalCheck
    (mul hAst134Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst134Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst134Numerator) hAst134Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst134Code : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^6))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 3))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 3))+(Source.multiplierImag z.1 z.2))))) :=
  hAst134Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst134Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst134Denominator)
    hAst134DenNonzero hAst134Cross

/-- Article: proposed exact numerator for hDiscrepancy3. -/
def hDiscrepancy3Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-1,0,0,0,-1,0,1],[0,1,-1,1,0,-1,1,-2,1,-1,0,1,-1,1],[1,0,3,0,2,0,-1,0,-3,0,-2]]
/-- Article: proposed positive denominator for hDiscrepancy3. -/
def hDiscrepancy3Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDiscrepancy3Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^6))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 3)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 3)+(Source.multiplierImag z.1 z.2))))) :=
  (hAst134Code.congr (by
    intro z hz
    ring))
private theorem hDiscrepancy3Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^6))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 3))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 3)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 3)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 3)+(Source.multiplierImag z.1 z.2))))=Source.discrepancy z.1 z.2 3 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.discrepancy]; ring
private theorem hDiscrepancy3DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDiscrepancy3Denominator=true := by kernel_decide
private theorem hDiscrepancy3DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy3Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDiscrepancy3Denominator hDiscrepancy3DenCheck hz.1 hz.2).ne'
private theorem hDiscrepancy3Cross : equalCheck
    (mul hDiscrepancy3Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy3Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy3Numerator) hDiscrepancy3Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDiscrepancy3. -/
def hDiscrepancy3Code : RationalCode Source.domain (fun z => Source.discrepancy z.1 z.2 3) :=
  (hDiscrepancy3Raw.congr hDiscrepancy3Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy3Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy3Denominator)
    hDiscrepancy3DenNonzero hDiscrepancy3Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst135Numerator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst135Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst135Raw : RationalCode Source.domain (fun z => (z.2)^4) :=
  ((RationalCode.second Source.domain).pow 4)
private theorem hAst135DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst135Denominator=true := by kernel_decide
private theorem hAst135DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst135Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst135Denominator hAst135DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst135Cross : equalCheck
    (mul hAst135Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst135Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst135Numerator) hAst135Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst135Code : RationalCode Source.domain (fun z => (z.2)^4) :=
  hAst135Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst135Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst135Denominator)
    hAst135DenNonzero hAst135Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst136Numerator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[0],[0],[-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst136Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst136Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(z.2)^4)) :=
  ((RationalCode.constant Source.domain (-1)).mul hAst135Code)
private theorem hAst136DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst136Denominator=true := by kernel_decide
private theorem hAst136DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst136Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst136Denominator hAst136DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst136Cross : equalCheck
    (mul hAst136Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst136Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst136Numerator) hAst136Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst136Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(z.2)^4)) :=
  hAst136Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst136Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst136Denominator)
    hAst136DenNonzero hAst136Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst137Numerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[0],[0],[-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst137Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst137Raw : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4))) :=
  ((RationalCode.constant Source.domain 1).add hAst136Code)
private theorem hAst137DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst137Denominator=true := by kernel_decide
private theorem hAst137DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst137Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst137Denominator hAst137DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst137Cross : equalCheck
    (mul hAst137Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst137Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst137Numerator) hAst137Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst137Code : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4))) :=
  hAst137Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst137Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst137Denominator)
    hAst137DenNonzero hAst137Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst138Numerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[0],[0],[-2],[0],[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst138Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst138Raw : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2) :=
  (hAst137Code.pow 2)
private theorem hAst138DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst138Denominator=true := by kernel_decide
private theorem hAst138DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst138Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst138Denominator hAst138DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst138Cross : equalCheck
    (mul hAst138Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst138Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst138Numerator) hAst138Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst138Code : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2) :=
  hAst138Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst138Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst138Denominator)
    hAst138DenNonzero hAst138Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst139Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,1,0,0,0,1,0,-1],[0,-1,1,-1,0,1,-1,2,-1,1,0,-1,1,-1],[-1,0,-3,0,-2,0,1,0,3,0,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst139Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst139Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 3))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDiscrepancy3Code)
private theorem hAst139DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst139Denominator=true := by kernel_decide
private theorem hAst139DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst139Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst139Denominator hAst139DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst139Cross : equalCheck
    (mul hAst139Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst139Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst139Numerator) hAst139Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst139Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 3))) :=
  hAst139Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst139Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst139Denominator)
    hAst139DenNonzero hAst139Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst140Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,0,0,5,0,5,0,0,0,-4,0,-1],[0],[20,0,82,0,102,0,38,0,-8,0,-6,0,22,0,6],[0],[-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1],[0],[-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst140Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst140Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 3)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)) :=
  (hRadius3Code.add hAst138Code)
private theorem hAst140DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst140Denominator=true := by kernel_decide
private theorem hAst140DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst140Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst140Denominator hAst140DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst140Cross : equalCheck
    (mul hAst140Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst140Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst140Numerator) hAst140Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst140Code : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 3)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)) :=
  hAst140Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst140Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst140Denominator)
    hAst140DenNonzero hAst140Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst141Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,0,0,5,0,5,0,0,0,-4,0,-1],[0,0,0,0,-8,0,8,0,0,0,8,0,-8],[20,-8,90,-8,102,8,30,16,-16,8,-6,-8,30,-8,6],[-8,0,-24,0,-16,0,8,0,24,0,16],[-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1],[0],[-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst141Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst141Raw : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 3)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 3)))) :=
  (hAst140Code.add hAst139Code)
private theorem hAst141DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst141Denominator=true := by kernel_decide
private theorem hAst141DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst141Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst141Denominator hAst141DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst141Cross : equalCheck
    (mul hAst141Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst141Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst141Numerator) hAst141Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst141Code : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 3)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 3)))) :=
  hAst141Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst141Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst141Denominator)
    hAst141DenNonzero hAst141Cross

/-- Article: proposed exact numerator for hPairLower3. -/
def hPairLower3Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,0,0,5,0,5,0,0,0,-4,0,-1],[0,0,0,0,-8,0,8,0,0,0,8,0,-8],[20,-8,90,-8,102,8,30,16,-16,8,-6,-8,30,-8,6],[-8,0,-24,0,-16,0,8,0,24,0,16],[-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1],[0],[-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: proposed positive denominator for hPairLower3. -/
def hPairLower3Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairLower3Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 3)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 3)))) :=
  (hAst141Code.congr (by
    intro z hz
    ring))
private theorem hPairLower3Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.radius z.1 z.2 3)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 3)))=Source.pairSlack z.1 z.2 (-1) 3 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairLower3DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairLower3Denominator=true := by kernel_decide
private theorem hPairLower3DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairLower3Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairLower3Denominator hPairLower3DenCheck hz.1 hz.2).ne'
private theorem hPairLower3Cross : equalCheck
    (mul hPairLower3Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairLower3Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairLower3Numerator) hPairLower3Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairLower3. -/
def hPairLower3Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (-1) 3) :=
  (hPairLower3Raw.congr hPairLower3Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower3Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower3Denominator)
    hPairLower3DenNonzero hPairLower3Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst142Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,0,0,5,0,5,0,0,0,-4,0,-1],[0,0,0,0,8,0,-8,0,0,0,-8,0,8],[4,8,10,8,6,-8,-18,-16,-16,-8,-6,8,14,8,6],[8,0,24,0,16,0,-8,0,-24,0,-16],[-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst142Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst142Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 3)+(Source.radius z.1 z.2 3))) :=
  (hDiscrepancy3Code.add hRadius3Code)
private theorem hAst142DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst142Denominator=true := by kernel_decide
private theorem hAst142DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst142Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst142Denominator hAst142DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst142Cross : equalCheck
    (mul hAst142Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst142Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst142Numerator) hAst142Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst142Code : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 3)+(Source.radius z.1 z.2 3))) :=
  hAst142Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst142Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst142Denominator)
    hAst142DenNonzero hAst142Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst143Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,0,0,5,0,5,0,0,0,-4,0,-1],[0,0,0,0,8,0,-8,0,0,0,-8,0,8],[20,8,74,8,102,-8,46,-16,0,-8,-6,8,14,8,6],[8,0,24,0,16,0,-8,0,-24,0,-16],[-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1],[0],[-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst143Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst143Raw : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 3)+(Source.radius z.1 z.2 3))+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)) :=
  (hAst142Code.add hAst138Code)
private theorem hAst143DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst143Denominator=true := by kernel_decide
private theorem hAst143DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst143Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst143Denominator hAst143DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst143Cross : equalCheck
    (mul hAst143Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst143Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst143Numerator) hAst143Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst143Code : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 3)+(Source.radius z.1 z.2 3))+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)) :=
  hAst143Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst143Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst143Denominator)
    hAst143DenNonzero hAst143Cross

/-- Article: proposed exact numerator for hPairUpper3. -/
def hPairUpper3Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,0,0,5,0,5,0,0,0,-4,0,-1],[0,0,0,0,8,0,-8,0,0,0,-8,0,8],[20,8,74,8,102,-8,46,-16,0,-8,-6,8,14,8,6],[8,0,24,0,16,0,-8,0,-24,0,-16],[-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1],[0],[-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: proposed positive denominator for hPairUpper3. -/
def hPairUpper3Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairUpper3Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 3)+(Source.radius z.1 z.2 3)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)) :=
  (hAst143Code.congr (by
    intro z hz
    ring))
private theorem hPairUpper3Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.discrepancy z.1 z.2 3)+(Source.radius z.1 z.2 3)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)=Source.pairSlack z.1 z.2 (1) 3 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairUpper3DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairUpper3Denominator=true := by kernel_decide
private theorem hPairUpper3DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper3Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairUpper3Denominator hPairUpper3DenCheck hz.1 hz.2).ne'
private theorem hPairUpper3Cross : equalCheck
    (mul hPairUpper3Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper3Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper3Numerator) hPairUpper3Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairUpper3. -/
def hPairUpper3Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (1) 3) :=
  (hPairUpper3Raw.congr hPairUpper3Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper3Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper3Denominator)
    hPairUpper3DenNonzero hPairUpper3Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst144Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-4,0,-2,0,-4,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst144Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst144Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 4 (radialCosine z.1))*(z.1)^4)) :=
  (hT4Code.mul hAst078Code)
private theorem hAst144DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst144Denominator=true := by kernel_decide
private theorem hAst144DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst144Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst144Denominator hAst144DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst144Cross : equalCheck
    (mul hAst144Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst144Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst144Numerator) hAst144Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst144Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 4 (radialCosine z.1))*(z.1)^4)) :=
  hAst144Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst144Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst144Denominator)
    hAst144DenNonzero hAst144Cross

/-- Article: proposed exact numerator for hPowerReal4. -/
def hPowerReal4Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-4,0,-2,0,-4,0,1]]
/-- Article: proposed positive denominator for hPowerReal4. -/
def hPowerReal4Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerReal4Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 4 (radialCosine z.1))*(z.1)^4)) :=
  (hAst144Code.congr (by
    intro z hz
    ring))
private theorem hPowerReal4Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebT 4 (radialCosine z.1))*(z.1)^4)=Source.powerReal z.1 4 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.powerReal]; ring
private theorem hPowerReal4DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerReal4Denominator=true := by kernel_decide
private theorem hPowerReal4DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal4Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerReal4Denominator hPowerReal4DenCheck hz.1 hz.2).ne'
private theorem hPowerReal4Cross : equalCheck
    (mul hPowerReal4Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal4Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal4Numerator) hPowerReal4Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerReal4. -/
def hPowerReal4Code : RationalCode Source.domain (fun z => Source.powerReal z.1 4) :=
  (hPowerReal4Raw.congr hPowerReal4Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal4Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal4Denominator)
    hPowerReal4DenNonzero hPowerReal4Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst145Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,4,0,0,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst145Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst145Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 3 (radialCosine z.1))*(z.1)^3)) :=
  (hU3Code.mul hAst096Code)
private theorem hAst145DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst145Denominator=true := by kernel_decide
private theorem hAst145DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst145Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst145Denominator hAst145DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst145Cross : equalCheck
    (mul hAst145Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst145Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst145Numerator) hAst145Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst145Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 3 (radialCosine z.1))*(z.1)^3)) :=
  hAst145Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst145Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst145Denominator)
    hAst145DenNonzero hAst145Cross

/-- Article: proposed exact numerator for hPowerImag4. -/
def hPowerImag4Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,4,0,0,0,4]]
/-- Article: proposed positive denominator for hPowerImag4. -/
def hPowerImag4Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerImag4Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 3 (radialCosine z.1))*(z.1)^3)) :=
  (hAst145Code.congr (by
    intro z hz
    ring))
private theorem hPowerImag4Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebU 3 (radialCosine z.1))*(z.1)^3)=Source.powerImag z.1 4 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.powerImag,ite_eq_right (by decide)]; ring
private theorem hPowerImag4DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerImag4Denominator=true := by kernel_decide
private theorem hPowerImag4DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag4Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerImag4Denominator hPowerImag4DenCheck hz.1 hz.2).ne'
private theorem hPowerImag4Cross : equalCheck
    (mul hPowerImag4Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag4Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag4Numerator) hPowerImag4Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerImag4. -/
def hPowerImag4Code : RationalCode Source.domain (fun z => Source.powerImag z.1 4) :=
  (hPowerImag4Raw.congr hPowerImag4Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag4Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag4Denominator)
    hPowerImag4DenNonzero hPowerImag4Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst146Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,4,0,2,0,4,0,-1],[0],[0,0,0,0,-1,0,4,0,2,0,4,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst146Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst146Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 4)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerReal4Code.mul hSRealCode)
private theorem hAst146DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst146Denominator=true := by kernel_decide
private theorem hAst146DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst146Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst146Denominator hAst146DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst146Cross : equalCheck
    (mul hAst146Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst146Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst146Numerator) hAst146Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst146Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 4)*(Source.multiplierReal z.1 z.2))) :=
  hAst146Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst146Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst146Denominator)
    hAst146DenNonzero hAst146Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst147Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-4,0,-4,0,-8,0,-4,0,-4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst147Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst147Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))) :=
  (hAst002Code.mul hPowerImag4Code)
private theorem hAst147DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst147Denominator=true := by kernel_decide
private theorem hAst147DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst147Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst147Denominator hAst147DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst147Cross : equalCheck
    (mul hAst147Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst147Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst147Numerator) hAst147Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst147Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))) :=
  hAst147Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst147Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst147Denominator)
    hAst147DenNonzero hAst147Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst148Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-2,0,-2,0,-4,0,-2,0,-2],[0],[0,0,0,0,2,0,2,0,4,0,2,0,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst148Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst148Raw : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))*(Source.multiplierImag z.1 z.2))) :=
  (hAst147Code.mul hSImagCode)
private theorem hAst148DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst148Denominator=true := by kernel_decide
private theorem hAst148DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst148Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst148Denominator hAst148DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst148Cross : equalCheck
    (mul hAst148Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst148Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst148Numerator) hAst148Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst148Code : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))*(Source.multiplierImag z.1 z.2))) :=
  hAst148Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst148Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst148Denominator)
    hAst148DenNonzero hAst148Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst149Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-5,0,0,0,-6,0,0,0,-5],[0],[0,0,0,0,3,0,8,0,10,0,8,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst149Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst149Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 4)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))*(Source.multiplierImag z.1 z.2)))) :=
  (hAst146Code.add hAst148Code)
private theorem hAst149DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst149Denominator=true := by kernel_decide
private theorem hAst149DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst149Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst149Denominator hAst149DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst149Cross : equalCheck
    (mul hAst149Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst149Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst149Numerator) hAst149Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst149Code : RationalCode Source.domain (fun z => (((Source.powerReal z.1 4)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))*(Source.multiplierImag z.1 z.2)))) :=
  hAst149Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst149Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst149Denominator)
    hAst149DenNonzero hAst149Cross

/-- Article: proposed exact numerator for hGradientReal4. -/
def hGradientReal4Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-5,0,0,0,-6,0,0,0,-5],[0],[0,0,0,0,3,0,8,0,10,0,8,0,3]]
/-- Article: proposed positive denominator for hGradientReal4. -/
def hGradientReal4Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientReal4Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 4)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 4)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst149Code.congr (by
    intro z hz
    ring))
private theorem hGradientReal4Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerReal z.1 4)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 4)*(Source.multiplierImag z.1 z.2)))=Source.gradientReal z.1 z.2 4 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientReal]; ring
private theorem hGradientReal4DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientReal4Denominator=true := by kernel_decide
private theorem hGradientReal4DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal4Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientReal4Denominator hGradientReal4DenCheck hz.1 hz.2).ne'
private theorem hGradientReal4Cross : equalCheck
    (mul hGradientReal4Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal4Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal4Numerator) hGradientReal4Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientReal4. -/
def hGradientReal4Code : RationalCode Source.domain (fun z => Source.gradientReal z.1 z.2 4) :=
  (hGradientReal4Raw.congr hGradientReal4Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal4Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal4Denominator)
    hGradientReal4DenNonzero hGradientReal4Cross

end
end polyak.Certificates.Startup.Codes
