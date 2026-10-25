import polyak.Certificates.Startup.Code10

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: canonical numerator for one arithmetic source node. -/
def hAst326Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,8,0,-32,0,-8,0,-64,0,-8,0,-32,0,8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst326Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst326Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 7 (radialCosine z.1))*(z.1)^7)) :=
  (hU7Code.mul hAst277Code)
private theorem hAst326DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst326Denominator=true := by kernel_decide
private theorem hAst326DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst326Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst326Denominator hAst326DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst326Cross : equalCheck
    (mul hAst326Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst326Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst326Numerator) hAst326Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst326Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 7 (radialCosine z.1))*(z.1)^7)) :=
  hAst326Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst326Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst326Denominator)
    hAst326DenNonzero hAst326Cross

/-- Article: proposed exact numerator for hPowerImag8. -/
def hPowerImag8Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,8,0,-32,0,-8,0,-64,0,-8,0,-32,0,8]]
/-- Article: proposed positive denominator for hPowerImag8. -/
def hPowerImag8Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerImag8Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 7 (radialCosine z.1))*(z.1)^7)) :=
  (hAst326Code.congr (by
    intro z hz
    ring))
private theorem hPowerImag8Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebU 7 (radialCosine z.1))*(z.1)^7)=Source.powerImag z.1 8 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.powerImag,ite_eq_right (by decide)]; ring
private theorem hPowerImag8DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerImag8Denominator=true := by kernel_decide
private theorem hPowerImag8DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag8Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerImag8Denominator hPowerImag8DenCheck hz.1 hz.2).ne'
private theorem hPowerImag8Cross : equalCheck
    (mul hPowerImag8Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag8Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag8Numerator) hPowerImag8Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerImag8. -/
def hPowerImag8Code : RationalCode Source.domain (fun z => Source.powerImag z.1 8) :=
  (hPowerImag8Raw.congr hPowerImag8Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag8Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag8Denominator)
    hPowerImag8DenNonzero hPowerImag8Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst327Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,24,0,4,0,40,0,-6,0,40,0,4,0,24,0,-1],[0],[0,0,0,0,0,0,0,0,-1,0,24,0,4,0,40,0,-6,0,40,0,4,0,24,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst327Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst327Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 8)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerReal8Code.mul hSRealCode)
private theorem hAst327DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst327Denominator=true := by kernel_decide
private theorem hAst327DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst327Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst327Denominator hAst327DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst327Cross : equalCheck
    (mul hAst327Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst327Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst327Numerator) hAst327Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst327Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 8)*(Source.multiplierReal z.1 z.2))) :=
  hAst327Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst327Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst327Denominator)
    hAst327DenNonzero hAst327Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst328Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-8,0,24,0,32,0,104,0,80,0,104,0,32,0,24,0,-8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst328Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst328Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))) :=
  (hAst002Code.mul hPowerImag8Code)
private theorem hAst328DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst328Denominator=true := by kernel_decide
private theorem hAst328DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst328Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst328Denominator hAst328DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst328Cross : equalCheck
    (mul hAst328Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst328Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst328Numerator) hAst328Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst328Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))) :=
  hAst328Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst328Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst328Denominator)
    hAst328DenNonzero hAst328Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst329Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-4,0,12,0,16,0,52,0,40,0,52,0,16,0,12,0,-4],[0],[0,0,0,0,0,0,0,0,4,0,-12,0,-16,0,-52,0,-40,0,-52,0,-16,0,-12,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst329Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst329Raw : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))*(Source.multiplierImag z.1 z.2))) :=
  (hAst328Code.mul hSImagCode)
private theorem hAst329DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst329Denominator=true := by kernel_decide
private theorem hAst329DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst329Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst329Denominator hAst329DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst329Cross : equalCheck
    (mul hAst329Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst329Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst329Numerator) hAst329Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst329Code : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))*(Source.multiplierImag z.1 z.2))) :=
  hAst329Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst329Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst329Denominator)
    hAst329DenNonzero hAst329Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst330Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-9,0,48,0,36,0,144,0,74,0,144,0,36,0,48,0,-9],[0],[0,0,0,0,0,0,0,0,7,0,0,0,-28,0,-64,0,-86,0,-64,0,-28,0,0,0,7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst330Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst330Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 8)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))*(Source.multiplierImag z.1 z.2)))) :=
  (hAst327Code.add hAst329Code)
private theorem hAst330DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst330Denominator=true := by kernel_decide
private theorem hAst330DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst330Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst330Denominator hAst330DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst330Cross : equalCheck
    (mul hAst330Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst330Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst330Numerator) hAst330Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst330Code : RationalCode Source.domain (fun z => (((Source.powerReal z.1 8)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))*(Source.multiplierImag z.1 z.2)))) :=
  hAst330Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst330Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst330Denominator)
    hAst330DenNonzero hAst330Cross

/-- Article: proposed exact numerator for hGradientReal8. -/
def hGradientReal8Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-9,0,48,0,36,0,144,0,74,0,144,0,36,0,48,0,-9],[0],[0,0,0,0,0,0,0,0,7,0,0,0,-28,0,-64,0,-86,0,-64,0,-28,0,0,0,7]]
/-- Article: proposed positive denominator for hGradientReal8. -/
def hGradientReal8Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientReal8Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 8)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 8)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst330Code.congr (by
    intro z hz
    ring))
private theorem hGradientReal8Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerReal z.1 8)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 8)*(Source.multiplierImag z.1 z.2)))=Source.gradientReal z.1 z.2 8 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientReal]; ring
private theorem hGradientReal8DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientReal8Denominator=true := by kernel_decide
private theorem hGradientReal8DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal8Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientReal8Denominator hGradientReal8DenCheck hz.1 hz.2).ne'
private theorem hGradientReal8Cross : equalCheck
    (mul hGradientReal8Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal8Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal8Numerator) hGradientReal8Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientReal8. -/
def hGradientReal8Code : RationalCode Source.domain (fun z => Source.gradientReal z.1 z.2 8) :=
  (hGradientReal8Raw.congr hGradientReal8Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal8Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal8Denominator)
    hGradientReal8DenNonzero hGradientReal8Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst331Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-4,0,16,0,4,0,32,0,4,0,16,0,-4],[0],[0,0,0,0,0,0,0,0,-4,0,16,0,4,0,32,0,4,0,16,0,-4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst331Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst331Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 8)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerImag8Code.mul hSRealCode)
private theorem hAst331DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst331Denominator=true := by kernel_decide
private theorem hAst331DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst331Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst331Denominator hAst331DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst331Cross : equalCheck
    (mul hAst331Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst331Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst331Numerator) hAst331Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst331Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 8)*(Source.multiplierReal z.1 z.2))) :=
  hAst331Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst331Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst331Denominator)
    hAst331DenNonzero hAst331Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst332Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-24,0,-4,0,-40,0,6,0,-40,0,-4,0,-24,0,1],[0],[0,0,0,0,0,0,-1,0,24,0,4,0,40,0,-6,0,40,0,4,0,24,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst332Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst332Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 8)*(Source.multiplierImag z.1 z.2))) :=
  (hPowerReal8Code.mul hSImagCode)
private theorem hAst332DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst332Denominator=true := by kernel_decide
private theorem hAst332DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst332Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst332Denominator hAst332DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst332Cross : equalCheck
    (mul hAst332Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst332Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst332Numerator) hAst332Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst332Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 8)*(Source.multiplierImag z.1 z.2))) :=
  hAst332Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst332Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst332Denominator)
    hAst332DenNonzero hAst332Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst333Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-32,0,28,0,-32,0,70,0,-32,0,28,0,-32,0,1],[0],[0,0,0,0,0,0,-1,0,16,0,36,0,48,0,58,0,48,0,36,0,16,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst333Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst333Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 8)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 8)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst331Code.add hAst332Code)
private theorem hAst333DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst333Denominator=true := by kernel_decide
private theorem hAst333DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst333Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst333Denominator hAst333DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst333Cross : equalCheck
    (mul hAst333Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst333Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst333Numerator) hAst333Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst333Code : RationalCode Source.domain (fun z => (((Source.powerImag z.1 8)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 8)*(Source.multiplierImag z.1 z.2)))) :=
  hAst333Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst333Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst333Denominator)
    hAst333DenNonzero hAst333Cross

/-- Article: proposed exact numerator for hGradientImag8. -/
def hGradientImag8Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-32,0,28,0,-32,0,70,0,-32,0,28,0,-32,0,1],[0],[0,0,0,0,0,0,-1,0,16,0,36,0,48,0,58,0,48,0,36,0,16,0,-1]]
/-- Article: proposed positive denominator for hGradientImag8. -/
def hGradientImag8Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientImag8Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 8)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 8)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst333Code.congr (by
    intro z hz
    ring))
private theorem hGradientImag8Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerImag z.1 8)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 8)*(Source.multiplierImag z.1 z.2)))=Source.gradientImag z.1 z.2 8 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientImag]; ring
private theorem hGradientImag8DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientImag8Denominator=true := by kernel_decide
private theorem hGradientImag8DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag8Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientImag8Denominator hGradientImag8DenCheck hz.1 hz.2).ne'
private theorem hGradientImag8Cross : equalCheck
    (mul hGradientImag8Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag8Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag8Numerator) hGradientImag8Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientImag8. -/
def hGradientImag8Code : RationalCode Source.domain (fun z => Source.gradientImag z.1 z.2 8) :=
  (hGradientImag8Raw.congr hGradientImag8Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag8Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag8Denominator)
    hGradientImag8DenNonzero hGradientImag8Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst334Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-9,0,48,0,36,0,144,0,74,0,144,0,36,0,48,0,-9],[0],[-2,0,-17,0,-64,0,-140,0,-189,0,-182,0,-140,0,-108,0,-96,0,-65,0,-28,0,0,0,7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst334Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst334Raw : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  (hGradientReal8Code.add hAst009Code)
private theorem hAst334DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst334Denominator=true := by kernel_decide
private theorem hAst334DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst334Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst334Denominator hAst334DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst334Cross : equalCheck
    (mul hAst334Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst334Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst334Numerator) hAst334Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst334Code : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  hAst334Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst334Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst334Denominator)
    hAst334DenNonzero hAst334Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst335Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,8,0,28,0,56,0,61,0,104,0,64,0,152,0,75,0,144,0,36,0,48,0,-9],[0],[-1,0,-9,0,-36,0,-84,0,-119,0,-126,0,-112,0,-100,0,-95,0,-65,0,-28,0,0,0,7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst335Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst335Raw : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  (hAst334Code.add hAst010Code)
private theorem hAst335DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst335Denominator=true := by kernel_decide
private theorem hAst335DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst335Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst335Denominator hAst335DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst335Cross : equalCheck
    (mul hAst335Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst335Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst335Numerator) hAst335Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst335Code : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  hAst335Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst335Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst335Denominator)
    hAst335DenNonzero hAst335Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst336Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,16,0,120,0,560,0,1802,0,4320,0,8344,0,13984,0,21535,0,29856,0,42224,0,48992,0,63756,0,59200,0,71920,0,53568,0,62895,0,36816,0,39576,0,14832,0,13770,0,864,0,1656,0,-864,0,81],[0],[0,0,-2,0,-34,0,-272,0,-1360,0,-4728,0,-12198,0,-24704,0,-41568,0,-61658,0,-83252,0,-106320,0,-126240,0,-139344,0,-140076,0,-128176,0,-108480,0,-83558,0,-59850,0,-36448,0,-17936,0,-5496,0,498,0,1008,0,672,0,-126],[0],[1,0,18,0,153,0,816,0,3046,0,8442,0,18116,0,31280,0,45383,0,57844,0,67398,0,73168,0,73276,0,66388,0,53820,0,39440,0,26631,0,16186,0,7977,0,2240,0,-546,0,-910,0,-392,0,0,0,49]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst336Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,72,0,612,0,3264,0,12240,0,34272,0,74256,0,127296,0,175032,0,194480,0,175032,0,127296,0,74256,0,34272,0,12240,0,3264,0,612,0,72,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst336Raw : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  (hAst335Code.pow 2)
private theorem hAst336DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst336Denominator=true := by kernel_decide
private theorem hAst336DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst336Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst336Denominator hAst336DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst336Cross : equalCheck
    (mul hAst336Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst336Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst336Numerator) hAst336Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst336Code : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  hAst336Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst336Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst336Denominator)
    hAst336DenNonzero hAst336Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst337Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-16,0,-120,0,-560,0,-1802,0,-4320,0,-8344,0,-13984,0,-21535,0,-29856,0,-42224,0,-48992,0,-63756,0,-59200,0,-71920,0,-53568,0,-62895,0,-36816,0,-39576,0,-14832,0,-13770,0,-864,0,-1656,0,864,0,-81],[0],[0,0,2,0,34,0,272,0,1360,0,4728,0,12198,0,24704,0,41568,0,61658,0,83252,0,106320,0,126240,0,139344,0,140076,0,128176,0,108480,0,83558,0,59850,0,36448,0,17936,0,5496,0,-498,0,-1008,0,-672,0,126],[0],[-1,0,-18,0,-153,0,-816,0,-3046,0,-8442,0,-18116,0,-31280,0,-45383,0,-57844,0,-67398,0,-73168,0,-73276,0,-66388,0,-53820,0,-39440,0,-26631,0,-16186,0,-7977,0,-2240,0,546,0,910,0,392,0,0,0,-49]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst337Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,288,0,2448,0,13056,0,48960,0,137088,0,297024,0,509184,0,700128,0,777920,0,700128,0,509184,0,297024,0,137088,0,48960,0,13056,0,2448,0,288,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst337Raw : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  ((RationalCode.constant Source.domain (-1/4)).mul hAst336Code)
private theorem hAst337DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst337Denominator=true := by kernel_decide
private theorem hAst337DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst337Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst337Denominator hAst337DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst337Cross : equalCheck
    (mul hAst337Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst337Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst337Numerator) hAst337Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst337Code : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  hAst337Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst337Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst337Denominator)
    hAst337DenNonzero hAst337Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst338Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-8,0,-28,0,-56,0,-69,0,-80,0,-32,0,-48,0,5,0,-40,0,-4,0,-24,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst338Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst338Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8))) :=
  ((RationalCode.constant Source.domain (-1)).add hPowerReal8Code)
private theorem hAst338DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst338Denominator=true := by kernel_decide
private theorem hAst338DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst338Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst338Denominator hAst338DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst338Cross : equalCheck
    (mul hAst338Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst338Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst338Numerator) hAst338Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst338Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8))) :=
  hAst338Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst338Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst338Denominator)
    hAst338DenNonzero hAst338Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst339Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,16,0,120,0,560,0,1818,0,4400,0,8344,0,12816,0,16271,0,17312,0,16560,0,13536,0,13100,0,9568,0,11568,0,5920,0,7823,0,1360,0,3800,0,-16,0,1946,0,112,0,568,0,-48,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst339Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,16,0,120,0,560,0,1820,0,4368,0,8008,0,11440,0,12870,0,11440,0,8008,0,4368,0,1820,0,560,0,120,0,16,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst339Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2) :=
  (hAst338Code.pow 2)
private theorem hAst339DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst339Denominator=true := by kernel_decide
private theorem hAst339DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst339Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst339Denominator hAst339DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst339Cross : equalCheck
    (mul hAst339Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst339Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst339Numerator) hAst339Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst339Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2) :=
  hAst339Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst339Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst339Denominator)
    hAst339DenNonzero hAst339Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst340Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,16,0,120,0,560,0,1818,0,4400,0,8344,0,12816,0,16271,0,17312,0,16560,0,13536,0,13100,0,9568,0,11568,0,5920,0,7823,0,1360,0,3800,0,-16,0,1946,0,112,0,568,0,-48,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst340Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,64,0,480,0,2240,0,7280,0,17472,0,32032,0,45760,0,51480,0,45760,0,32032,0,17472,0,7280,0,2240,0,480,0,64,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst340Raw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2)) :=
  ((RationalCode.constant Source.domain (1/4)).mul hAst339Code)
private theorem hAst340DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst340Denominator=true := by kernel_decide
private theorem hAst340DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst340Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst340Denominator hAst340DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst340Cross : equalCheck
    (mul hAst340Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst340Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst340Numerator) hAst340Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst340Code : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2)) :=
  hAst340Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst340Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst340Denominator)
    hAst340DenNonzero hAst340Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst341Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,1,0,-32,0,28,0,-32,0,70,0,-32,0,28,0,-32,0,1],[0],[-1,0,-8,0,-28,0,-56,0,-71,0,-40,0,8,0,40,0,57,0,48,0,36,0,16,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst341Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst341Raw : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  (hGradientImag8Code.add hAst018Code)
private theorem hAst341DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst341Denominator=true := by kernel_decide
private theorem hAst341DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst341Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst341Denominator hAst341DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst341Cross : equalCheck
    (mul hAst341Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst341Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst341Numerator) hAst341Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst341Code : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  hAst341Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst341Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst341Denominator)
    hAst341DenNonzero hAst341Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst342Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-8,0,-28,0,-56,0,-69,0,-88,0,0,0,-40,0,69,0,-32,0,28,0,-32,0,1],[0],[0,0,0,0,0,0,-1,0,16,0,36,0,48,0,58,0,48,0,36,0,16,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst342Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst342Raw : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst341Code.add hAst019Code)
private theorem hAst342DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst342Denominator=true := by kernel_decide
private theorem hAst342DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst342Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst342Denominator hAst342DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst342Cross : equalCheck
    (mul hAst342Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst342Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst342Numerator) hAst342Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst342Code : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  hAst342Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst342Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst342Denominator)
    hAst342DenNonzero hAst342Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst343Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,16,0,120,0,560,0,1818,0,4416,0,8408,0,12736,0,15119,0,13344,0,8816,0,-800,0,44,0,-9088,0,6896,0,-6144,0,12815,0,-6832,0,7448,0,-6288,0,2970,0,-1856,0,1080,0,-64,0,1],[0],[0,0,0,0,0,0,2,0,-16,0,-272,0,-1456,0,-4554,0,-9776,0,-17248,0,-22672,0,-25516,0,-22352,0,-15104,0,-7792,0,-596,0,624,0,864,0,-944,0,-2102,0,-1248,0,-1008,0,96,0,-2],[0],[0,0,0,0,0,0,0,0,0,0,0,0,1,0,-32,0,184,0,1056,0,2716,0,5216,0,7944,0,10144,0,11078,0,10144,0,7944,0,5216,0,2716,0,1056,0,184,0,-32,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst343Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,64,0,480,0,2240,0,7280,0,17472,0,32032,0,45760,0,51480,0,45760,0,32032,0,17472,0,7280,0,2240,0,480,0,64,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst343Raw : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  (hAst342Code.pow 2)
private theorem hAst343DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst343Denominator=true := by kernel_decide
private theorem hAst343DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst343Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst343Denominator hAst343DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst343Cross : equalCheck
    (mul hAst343Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst343Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst343Numerator) hAst343Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst343Code : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  hAst343Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst343Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst343Denominator)
    hAst343DenNonzero hAst343Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst344Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-17,0,-137,0,-696,0,-2498,0,-6794,0,-14642,0,-25560,0,-36263,0,-41199,0,-37279,0,-21360,0,-8060,0,9844,0,2148,0,8336,0,-13567,0,161,0,-13431,0,5672,0,-4130,0,5174,0,-2194,0,840,0,-1017,0,63,0,-1],[0],[0,0,0,0,0,0,0,0,-2,0,14,0,286,0,1744,0,6282,0,15786,0,31578,0,49696,0,65436,0,70540,0,62972,0,45248,0,23492,0,7764,0,-892,0,-544,0,2182,0,4294,0,4358,0,2160,0,914,0,-94,0,2],[0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,31,0,-153,0,-1208,0,-3956,0,-8988,0,-15876,0,-23304,0,-29166,0,-31366,0,-29166,0,-23304,0,-15876,0,-8988,0,-3956,0,-1208,0,-153,0,31,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst344Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,288,0,2448,0,13056,0,48960,0,137088,0,297024,0,509184,0,700128,0,777920,0,700128,0,509184,0,297024,0,137088,0,48960,0,13056,0,2448,0,288,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst344Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  (hAst023Code.mul hAst343Code)
private theorem hAst344DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst344Denominator=true := by kernel_decide
private theorem hAst344DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst344Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst344Denominator hAst344DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst344Cross : equalCheck
    (mul hAst344Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst344Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst344Numerator) hAst344Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst344Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  hAst344Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst344Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst344Denominator)
    hAst344DenNonzero hAst344Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst345Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,-512,0,896,0,-512,0,4032,0,1024,0,6400,0,1024,0,4032,0,-512,0,896,0,-512,0,64]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst345Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,14,0,91,0,364,0,1001,0,2002,0,3003,0,3432,0,3003,0,2002,0,1001,0,364,0,91,0,14,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst345Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 8))^2) :=
  (hPowerImag8Code.pow 2)
private theorem hAst345DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst345Denominator=true := by kernel_decide
private theorem hAst345DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst345Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst345Denominator hAst345DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst345Cross : equalCheck
    (mul hAst345Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst345Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst345Numerator) hAst345Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst345Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 8))^2) :=
  hAst345Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst345Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst345Denominator)
    hAst345DenNonzero hAst345Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst346Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,-112,0,112,0,-32,0,1104,0,1136,0,2864,0,2112,0,2864,0,1136,0,1104,0,-32,0,112,0,-112,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst346Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,16,0,120,0,560,0,1820,0,4368,0,8008,0,11440,0,12870,0,11440,0,8008,0,4368,0,1820,0,560,0,120,0,16,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst346Raw : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 8))^2)) :=
  (hAst026Code.mul hAst345Code)
private theorem hAst346DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst346Denominator=true := by kernel_decide
private theorem hAst346DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst346Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst346Denominator hAst346DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst346Cross : equalCheck
    (mul hAst346Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst346Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst346Numerator) hAst346Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst346Code : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 8))^2)) :=
  hAst346Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst346Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst346Denominator)
    hAst346DenNonzero hAst346Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst347Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-16,0,-120,0,-560,0,-1802,0,-4320,0,-8344,0,-13984,0,-21535,0,-29856,0,-42224,0,-48992,0,-63756,0,-59200,0,-71920,0,-53568,0,-62895,0,-36816,0,-39576,0,-14832,0,-13770,0,-864,0,-1656,0,864,0,-81],[0],[4,0,74,0,646,0,3536,0,13592,0,39112,0,88046,0,160320,0,242556,0,312338,0,353072,0,362192,0,353168,0,336560,0,315292,0,282672,0,233404,0,175262,0,117222,0,72224,0,40792,0,21448,0,10454,0,3792,0,1220,0,-58,0,4],[0],[-1,0,-18,0,-153,0,-816,0,-3046,0,-8442,0,-18116,0,-31280,0,-45383,0,-57844,0,-67398,0,-73168,0,-73276,0,-66388,0,-53820,0,-39440,0,-26631,0,-16186,0,-7977,0,-2240,0,546,0,910,0,392,0,0,0,-49]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst347Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,288,0,2448,0,13056,0,48960,0,137088,0,297024,0,509184,0,700128,0,777920,0,700128,0,509184,0,297024,0,137088,0,48960,0,13056,0,2448,0,288,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst347Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2))) :=
  (hAst337Code.add hAst340Code)
private theorem hAst347DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst347Denominator=true := by kernel_decide
private theorem hAst347DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst347Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst347Denominator hAst347DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst347Cross : equalCheck
    (mul hAst347Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst347Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst347Numerator) hAst347Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst347Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2))) :=
  hAst347Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst347Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst347Denominator)
    hAst347DenNonzero hAst347Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst348Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-16,0,-120,0,-560,0,-1818,0,-4400,0,-8344,0,-12816,0,-16271,0,-17376,0,-16112,0,-13984,0,-12972,0,-13984,0,-16112,0,-17376,0,-16271,0,-12816,0,-8344,0,-4400,0,-1818,0,-560,0,-120,0,-16,0,-1],[0],[4,0,66,0,510,0,2450,0,8180,0,20316,0,39520,0,62708,0,83902,0,97612,0,105524,0,103228,0,106624,0,90624,0,90392,0,56512,0,53480,0,19554,0,23742,0,4642,0,9948,0,1204,0,2456,0,-164,0,6],[0],[-1,0,-16,0,-120,0,-560,0,-1806,0,-4270,0,-7770,0,-11471,0,-14640,0,-17246,0,-19474,0,-20930,0,-20930,0,-19474,0,-17246,0,-14640,0,-11471,0,-7770,0,-4270,0,-1806,0,-560,0,-120,0,-16,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst348Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,256,0,1920,0,8960,0,29120,0,69888,0,128128,0,183040,0,205920,0,183040,0,128128,0,69888,0,29120,0,8960,0,1920,0,256,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst348Raw : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  (hAst347Code.add hAst344Code)
private theorem hAst348DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst348Denominator=true := by kernel_decide
private theorem hAst348DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst348Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst348Denominator hAst348DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst348Cross : equalCheck
    (mul hAst348Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst348Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst348Numerator) hAst348Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst348Code : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  hAst348Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst348Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst348Denominator)
    hAst348DenNonzero hAst348Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst349Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0],[4,0,38,0,160,0,392,0,606,0,828,0,852,0,796,0,858,0,716,0,1000,0,800,0,914,0,588,0,420,0,188,0,50,0,6],[0],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst349Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst349Raw : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 8))^2))) :=
  (hAst348Code.add hAst346Code)
private theorem hAst349DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst349Denominator=true := by kernel_decide
private theorem hAst349DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst349Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst349Denominator hAst349DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst349Cross : equalCheck
    (mul hAst349Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst349Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst349Numerator) hAst349Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst349Code : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 8))^2))) :=
  hAst349Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst349Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst349Denominator)
    hAst349DenNonzero hAst349Cross

/-- Article: proposed exact numerator for hRadius8. -/
def hRadius8Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0],[4,0,38,0,160,0,392,0,606,0,828,0,852,0,796,0,858,0,716,0,1000,0,800,0,914,0,588,0,420,0,188,0,50,0,6],[0],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1]]
/-- Article: proposed positive denominator for hRadius8. -/
def hRadius8Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hRadius8Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 8))^2))) :=
  (hAst349Code.congr (by
    intro z hz
    ring))
private theorem hRadius8Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 8)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 8))^2))=Source.radius z.1 z.2 8 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.radius]; ring
private theorem hRadius8DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hRadius8Denominator=true := by kernel_decide
private theorem hRadius8DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hRadius8Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hRadius8Denominator hRadius8DenCheck hz.1 hz.2).ne'
private theorem hRadius8Cross : equalCheck
    (mul hRadius8Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hRadius8Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hRadius8Numerator) hRadius8Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hRadius8. -/
def hRadius8Code : RationalCode Source.domain (fun z => Source.radius z.1 z.2 8) :=
  (hRadius8Raw.congr hRadius8Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius8Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius8Denominator)
    hRadius8DenNonzero hRadius8Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst350Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst350Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst350Raw : RationalCode Source.domain (fun z => (z.1)^16) :=
  ((RationalCode.first Source.domain).pow 16)
private theorem hAst350DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst350Denominator=true := by kernel_decide
private theorem hAst350DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst350Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst350Denominator hAst350DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst350Cross : equalCheck
    (mul hAst350Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst350Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst350Numerator) hAst350Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst350Code : RationalCode Source.domain (fun z => (z.1)^16) :=
  hAst350Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst350Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst350Denominator)
    hAst350DenNonzero hAst350Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst351Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst351Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst351Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^16)) :=
  ((RationalCode.constant Source.domain (-1)).add hAst350Code)
private theorem hAst351DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst351Denominator=true := by kernel_decide
private theorem hAst351DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst351Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst351Denominator hAst351DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst351Cross : equalCheck
    (mul hAst351Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst351Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst351Numerator) hAst351Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst351Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^16)) :=
  hAst351Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst351Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst351Denominator)
    hAst351DenNonzero hAst351Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst352Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,-1],[0,2,-2,-2,4,0,-4,0,4,0,-4,0,4,0,-4,0,4,-2,-2,2],[1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst352Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,8,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst352Raw : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^16))) :=
  (hValueCode.mul hAst351Code)
private theorem hAst352DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst352Denominator=true := by kernel_decide
private theorem hAst352DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst352Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst352Denominator hAst352DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst352Cross : equalCheck
    (mul hAst352Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst352Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst352Numerator) hAst352Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst352Code : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^16))) :=
  hAst352Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst352Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst352Denominator)
    hAst352DenNonzero hAst352Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst353Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-9,0,48,0,36,0,144,0,74,0,144,0,36,0,48,0,-9],[0],[2,0,17,0,64,0,140,0,203,0,182,0,84,0,-20,0,-76,0,-63,0,-28,0,0,0,7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst353Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst353Raw : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8))) :=
  (hDRealCode.add hGradientReal8Code)
private theorem hAst353DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst353Denominator=true := by kernel_decide
private theorem hAst353DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst353Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst353Denominator hAst353DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst353Cross : equalCheck
    (mul hAst353Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst353Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst353Numerator) hAst353Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst353Code : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8))) :=
  hAst353Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst353Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst353Denominator)
    hAst353DenNonzero hAst353Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst354Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-79,0,-8,0,8,0,136,0,73,0,144,0,36,0,48,0,-9],[0],[1,0,9,0,36,0,84,0,133,0,126,0,56,0,-28,0,-77,0,-63,0,-28,0,0,0,7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst354Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst354Raw : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8))+(Source.multiplierReal z.1 z.2))) :=
  (hAst353Code.add hSRealCode)
private theorem hAst354DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst354Denominator=true := by kernel_decide
private theorem hAst354DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst354Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst354Denominator hAst354DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst354Cross : equalCheck
    (mul hAst354Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst354Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst354Numerator) hAst354Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst354Code : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8))+(Source.multiplierReal z.1 z.2))) :=
  hAst354Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst354Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst354Denominator)
    hAst354DenNonzero hAst354Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst355Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,69,0,80,0,32,0,48,0,-5,0,40,0,4,0,24,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst355Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst355Raw : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))) :=
  ((RationalCode.constant Source.domain (-1/2)).mul hAst338Code)
private theorem hAst355DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst355Denominator=true := by kernel_decide
private theorem hAst355DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst355Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst355Denominator hAst355DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst355Cross : equalCheck
    (mul hAst355Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst355Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst355Numerator) hAst355Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst355Code : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))) :=
  hAst355Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst355Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst355Denominator)
    hAst355DenNonzero hAst355Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst356Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-16,0,-120,0,-560,0,-1828,0,-4408,0,-8008,0,-10856,0,-10269,0,-5024,0,5360,0,13536,0,23088,0,19792,0,23312,0,11568,0,16277,0,5488,0,11144,0,2960,0,5492,0,552,0,1080,0,-264,0,9],[0],[1,0,17,0,136,0,680,0,2386,0,6259,0,12728,0,20408,0,25799,0,25418,0,18160,0,7744,0,-964,0,-4346,0,-3312,0,-1568,0,-1057,0,-2443,0,-3192,0,-2856,0,-1582,0,-329,0,56,0,168,0,-7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst356Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,68,0,544,0,2720,0,9520,0,24752,0,49504,0,77792,0,97240,0,97240,0,77792,0,49504,0,24752,0,9520,0,2720,0,544,0,68,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst356Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8))+(Source.multiplierReal z.1 z.2)))) :=
  (hAst355Code.mul hAst354Code)
private theorem hAst356DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst356Denominator=true := by kernel_decide
private theorem hAst356DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst356Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst356Denominator hAst356DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst356Cross : equalCheck
    (mul hAst356Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst356Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst356Numerator) hAst356Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst356Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8))+(Source.multiplierReal z.1 z.2)))) :=
  hAst356Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst356Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst356Denominator)
    hAst356DenNonzero hAst356Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst357Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,1,0,-32,0,28,0,-32,0,70,0,-32,0,28,0,-32,0,1],[0],[1,0,8,0,28,0,56,0,69,0,72,0,64,0,56,0,59,0,48,0,36,0,16,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst357Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst357Raw : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 8))) :=
  (hDImagCode.add hGradientImag8Code)
private theorem hAst357DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst357Denominator=true := by kernel_decide
private theorem hAst357DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst357Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst357Denominator hAst357DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst357Cross : equalCheck
    (mul hAst357Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst357Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst357Numerator) hAst357Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst357Code : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 8))) :=
  hAst357Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst357Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst357Denominator)
    hAst357DenNonzero hAst357Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst358Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,71,0,24,0,56,0,-24,0,71,0,-32,0,28,0,-32,0,1],[0],[0,0,0,0,0,0,-1,0,16,0,36,0,48,0,58,0,48,0,36,0,16,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst358Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst358Raw : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 8))+(Source.multiplierImag z.1 z.2))) :=
  (hAst357Code.add hSImagCode)
private theorem hAst358DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst358Denominator=true := by kernel_decide
private theorem hAst358DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst358Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst358Denominator hAst358DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst358Cross : equalCheck
    (mul hAst358Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst358Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst358Numerator) hAst358Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst358Code : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 8))+(Source.multiplierImag z.1 z.2))) :=
  hAst358Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst358Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst358Denominator)
    hAst358DenNonzero hAst358Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst359Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-4,0,12,0,16,0,52,0,40,0,52,0,16,0,12,0,-4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst359Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst359Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))) :=
  (hAst040Code.mul hPowerImag8Code)
private theorem hAst359DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst359Denominator=true := by kernel_decide
private theorem hAst359DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst359Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst359Denominator hAst359DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst359Cross : equalCheck
    (mul hAst359Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst359Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst359Numerator) hAst359Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst359Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))) :=
  hAst359Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst359Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst359Denominator)
    hAst359DenNonzero hAst359Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst360Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-2,0,-10,0,0,0,146,0,646,0,1740,0,2832,0,4340,0,3932,0,4680,0,2288,0,3304,0,444,0,1780,0,-784,0,332,0,-922,0,2,0,-240,0,70,0,-2],[0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,-38,0,16,0,222,0,856,0,1866,0,3056,0,4094,0,4428,0,4094,0,3056,0,1866,0,856,0,222,0,16,0,-38,0,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst360Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,17,0,136,0,680,0,2380,0,6188,0,12376,0,19448,0,24310,0,24310,0,19448,0,12376,0,6188,0,2380,0,680,0,136,0,17,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst360Raw : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 8))+(Source.multiplierImag z.1 z.2)))) :=
  (hAst359Code.mul hAst358Code)
private theorem hAst360DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst360Denominator=true := by kernel_decide
private theorem hAst360DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst360Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst360Denominator hAst360DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst360Cross : equalCheck
    (mul hAst360Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst360Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst360Numerator) hAst360Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst360Code : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 8))+(Source.multiplierImag z.1 z.2)))) :=
  hAst360Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst360Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst360Denominator)
    hAst360DenNonzero hAst360Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst361Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-8,0,-40,0,0,0,584,0,2600,0,6400,0,13248,0,17344,0,23088,0,15984,0,15424,0,144,0,3408,0,-5952,0,3136,0,-1408,0,3672,0,-8,0,960,0,-280,0,8],[0,2,-2,28,-26,180,-154,700,-546,1820,-1274,3276,-2002,4004,-2002,2860,-858,-2,860,-2888,2028,-4184,2156,-3976,1820,-3640,1820,-3976,2156,-4184,2028,-2888,860,-2,-858,2860,-2002,4004,-2002,3276,-1274,1820,-546,700,-154,180,-26,28,-2,2],[2,0,33,0,256,0,1240,0,4206,0,10627,0,20736,0,31848,0,38668,0,36842,0,26048,0,11552,0,-964,0,-8154,0,-11200,0,-12992,0,-13926,0,-13883,0,-11200,0,-7224,0,-3402,0,-889,0,-64,0,152,0,-8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst361Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,68,0,544,0,2720,0,9520,0,24752,0,49504,0,77792,0,97240,0,97240,0,77792,0,49504,0,24752,0,9520,0,2720,0,544,0,68,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst361Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^16))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8))+(Source.multiplierReal z.1 z.2))))) :=
  (hAst352Code.add hAst356Code)
private theorem hAst361DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst361Denominator=true := by kernel_decide
private theorem hAst361DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst361Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst361Denominator hAst361DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst361Cross : equalCheck
    (mul hAst361Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst361Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst361Numerator) hAst361Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst361Code : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^16))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8))+(Source.multiplierReal z.1 z.2))))) :=
  hAst361Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst361Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst361Denominator)
    hAst361DenNonzero hAst361Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst362Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-16,0,48,0,64,0,208,0,160,0,208,0,64,0,48,0,-16],[0,2,-2,12,-10,28,-18,28,-10,0,10,-28,18,-28,10,-12,2,-4,2,-12,10,-28,18,-28,10,0,-10,28,-18,28,-10,12,-2,2],[2,0,17,0,64,0,140,0,202,0,205,0,112,0,24,0,-42,0,-29,0,16,0,28,0,30,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst362Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,36,0,144,0,336,0,504,0,504,0,336,0,144,0,36,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst362Raw : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^16))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 8))+(Source.multiplierImag z.1 z.2))))) :=
  (hAst361Code.add hAst360Code)
private theorem hAst362DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst362Denominator=true := by kernel_decide
private theorem hAst362DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst362Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst362Denominator hAst362DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst362Cross : equalCheck
    (mul hAst362Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst362Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst362Numerator) hAst362Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst362Code : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^16))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 8))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 8))+(Source.multiplierImag z.1 z.2))))) :=
  hAst362Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst362Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst362Denominator)
    hAst362DenNonzero hAst362Cross

/-- Article: proposed exact numerator for hDiscrepancy8. -/
def hDiscrepancy8Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-16,0,48,0,64,0,208,0,160,0,208,0,64,0,48,0,-16],[0,2,-2,12,-10,28,-18,28,-10,0,10,-28,18,-28,10,-12,2,-4,2,-12,10,-28,18,-28,10,0,-10,28,-18,28,-10,12,-2,2],[2,0,17,0,64,0,140,0,202,0,205,0,112,0,24,0,-42,0,-29,0,16,0,28,0,30,0,-1]]
/-- Article: proposed positive denominator for hDiscrepancy8. -/
def hDiscrepancy8Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,36,0,144,0,336,0,504,0,504,0,336,0,144,0,36,0,4]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDiscrepancy8Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^16))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 8)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 8)+(Source.multiplierImag z.1 z.2))))) :=
  (hAst362Code.congr (by
    intro z hz
    ring))
private theorem hDiscrepancy8Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^16))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 8))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 8)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 8)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 8)+(Source.multiplierImag z.1 z.2))))=Source.discrepancy z.1 z.2 8 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.discrepancy]; ring
private theorem hDiscrepancy8DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDiscrepancy8Denominator=true := by kernel_decide
private theorem hDiscrepancy8DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy8Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDiscrepancy8Denominator hDiscrepancy8DenCheck hz.1 hz.2).ne'
private theorem hDiscrepancy8Cross : equalCheck
    (mul hDiscrepancy8Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy8Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy8Numerator) hDiscrepancy8Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDiscrepancy8. -/
def hDiscrepancy8Code : RationalCode Source.domain (fun z => Source.discrepancy z.1 z.2 8) :=
  (hDiscrepancy8Raw.congr hDiscrepancy8Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy8Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy8Denominator)
    hDiscrepancy8DenNonzero hDiscrepancy8Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst363Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,16,0,-48,0,-64,0,-208,0,-160,0,-208,0,-64,0,-48,0,16],[0,-2,2,-12,10,-28,18,-28,10,0,-10,28,-18,28,-10,12,-2,4,-2,12,-10,28,-18,28,-10,0,10,-28,18,-28,10,-12,2,-2],[-2,0,-17,0,-64,0,-140,0,-202,0,-205,0,-112,0,-24,0,42,0,29,0,-16,0,-28,0,-30,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst363Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,36,0,144,0,336,0,504,0,504,0,336,0,144,0,36,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst363Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 8))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDiscrepancy8Code)
private theorem hAst363DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst363Denominator=true := by kernel_decide
private theorem hAst363DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst363Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst363Denominator hAst363DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst363Cross : equalCheck
    (mul hAst363Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst363Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst363Numerator) hAst363Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst363Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 8))) :=
  hAst363Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst363Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst363Denominator)
    hAst363DenNonzero hAst363Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst364Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0],[20,0,182,0,736,0,1736,0,2622,0,2844,0,2196,0,1372,0,1002,0,732,0,1000,0,800,0,914,0,588,0,420,0,188,0,50,0,6],[0],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1],[0],[0],[0],[0],[0],[-32,0,-288,0,-1152,0,-2688,0,-4032,0,-4032,0,-2688,0,-1152,0,-288,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst364Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst364Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 8)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)) :=
  (hRadius8Code.add hAst319Code)
private theorem hAst364DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst364Denominator=true := by kernel_decide
private theorem hAst364DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst364Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst364Denominator hAst364DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst364Cross : equalCheck
    (mul hAst364Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst364Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst364Numerator) hAst364Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst364Code : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 8)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)) :=
  hAst364Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst364Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst364Denominator)
    hAst364DenNonzero hAst364Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst365Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0,0,0,0,0,0,0,0,0,0,64,0,-192,0,-256,0,-832,0,-640,0,-832,0,-256,0,-192,0,64],[20,-8,190,-48,776,-112,1808,-112,2662,0,2804,112,2124,112,1332,48,994,16,724,48,960,112,728,112,874,0,628,-112,492,-112,228,-48,58,-8,6],[-8,0,-68,0,-256,0,-560,0,-808,0,-820,0,-448,0,-96,0,168,0,116,0,-64,0,-112,0,-120,0,4],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1],[0],[0],[0],[0],[0],[-32,0,-288,0,-1152,0,-2688,0,-4032,0,-4032,0,-2688,0,-1152,0,-288,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst365Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst365Raw : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 8)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 8)))) :=
  (hAst364Code.add hAst363Code)
private theorem hAst365DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst365Denominator=true := by kernel_decide
private theorem hAst365DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst365Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst365Denominator hAst365DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst365Cross : equalCheck
    (mul hAst365Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst365Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst365Numerator) hAst365Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst365Code : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 8)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 8)))) :=
  hAst365Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst365Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst365Denominator)
    hAst365DenNonzero hAst365Cross

/-- Article: proposed exact numerator for hPairLower8. -/
def hPairLower8Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0,0,0,0,0,0,0,0,0,0,64,0,-192,0,-256,0,-832,0,-640,0,-832,0,-256,0,-192,0,64],[20,-8,190,-48,776,-112,1808,-112,2662,0,2804,112,2124,112,1332,48,994,16,724,48,960,112,728,112,874,0,628,-112,492,-112,228,-48,58,-8,6],[-8,0,-68,0,-256,0,-560,0,-808,0,-820,0,-448,0,-96,0,168,0,116,0,-64,0,-112,0,-120,0,4],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1],[0],[0],[0],[0],[0],[-32,0,-288,0,-1152,0,-2688,0,-4032,0,-4032,0,-2688,0,-1152,0,-288,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: proposed positive denominator for hPairLower8. -/
def hPairLower8Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairLower8Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 8)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 8)))) :=
  (hAst365Code.congr (by
    intro z hz
    ring))
private theorem hPairLower8Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.radius z.1 z.2 8)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 8)))=Source.pairSlack z.1 z.2 (-1) 8 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairLower8DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairLower8Denominator=true := by kernel_decide
private theorem hPairLower8DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairLower8Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairLower8Denominator hPairLower8DenCheck hz.1 hz.2).ne'
private theorem hPairLower8Cross : equalCheck
    (mul hPairLower8Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairLower8Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairLower8Numerator) hPairLower8Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairLower8. -/
def hPairLower8Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (-1) 8) :=
  (hPairLower8Raw.congr hPairLower8Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower8Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower8Denominator)
    hPairLower8DenNonzero hPairLower8Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst366Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0,0,0,0,0,0,0,0,0,0,-64,0,192,0,256,0,832,0,640,0,832,0,256,0,192,0,-64],[4,8,30,48,120,112,320,112,566,0,868,-112,924,-112,836,-48,866,-16,724,-48,1040,-112,872,-112,954,0,548,112,348,112,148,48,42,8,6],[8,0,68,0,256,0,560,0,808,0,820,0,448,0,96,0,-168,0,-116,0,64,0,112,0,120,0,-4],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst366Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst366Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 8)+(Source.radius z.1 z.2 8))) :=
  (hDiscrepancy8Code.add hRadius8Code)
private theorem hAst366DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst366Denominator=true := by kernel_decide
private theorem hAst366DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst366Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst366Denominator hAst366DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst366Cross : equalCheck
    (mul hAst366Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst366Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst366Numerator) hAst366Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst366Code : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 8)+(Source.radius z.1 z.2 8))) :=
  hAst366Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst366Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst366Denominator)
    hAst366DenNonzero hAst366Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst367Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0,0,0,0,0,0,0,0,0,0,-64,0,192,0,256,0,832,0,640,0,832,0,256,0,192,0,-64],[20,8,174,48,696,112,1664,112,2582,0,2884,-112,2268,-112,1412,-48,1010,-16,740,-48,1040,-112,872,-112,954,0,548,112,348,112,148,48,42,8,6],[8,0,68,0,256,0,560,0,808,0,820,0,448,0,96,0,-168,0,-116,0,64,0,112,0,120,0,-4],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1],[0],[0],[0],[0],[0],[-32,0,-288,0,-1152,0,-2688,0,-4032,0,-4032,0,-2688,0,-1152,0,-288,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst367Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst367Raw : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 8)+(Source.radius z.1 z.2 8))+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)) :=
  (hAst366Code.add hAst319Code)
private theorem hAst367DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst367Denominator=true := by kernel_decide
private theorem hAst367DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst367Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst367Denominator hAst367DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst367Cross : equalCheck
    (mul hAst367Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst367Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst367Numerator) hAst367Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst367Code : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 8)+(Source.radius z.1 z.2 8))+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)) :=
  hAst367Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst367Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst367Denominator)
    hAst367DenNonzero hAst367Cross

/-- Article: proposed exact numerator for hPairUpper8. -/
def hPairUpper8Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0,0,0,0,0,0,0,0,0,0,-64,0,192,0,256,0,832,0,640,0,832,0,256,0,192,0,-64],[20,8,174,48,696,112,1664,112,2582,0,2884,-112,2268,-112,1412,-48,1010,-16,740,-48,1040,-112,872,-112,954,0,548,112,348,112,148,48,42,8,6],[8,0,68,0,256,0,560,0,808,0,820,0,448,0,96,0,-168,0,-116,0,64,0,112,0,120,0,-4],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1],[0],[0],[0],[0],[0],[-32,0,-288,0,-1152,0,-2688,0,-4032,0,-4032,0,-2688,0,-1152,0,-288,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: proposed positive denominator for hPairUpper8. -/
def hPairUpper8Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairUpper8Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 8)+(Source.radius z.1 z.2 8)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)) :=
  (hAst367Code.congr (by
    intro z hz
    ring))
private theorem hPairUpper8Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.discrepancy z.1 z.2 8)+(Source.radius z.1 z.2 8)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)=Source.pairSlack z.1 z.2 (1) 8 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairUpper8DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairUpper8Denominator=true := by kernel_decide
private theorem hPairUpper8DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper8Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairUpper8Denominator hPairUpper8DenCheck hz.1 hz.2).ne'
private theorem hPairUpper8Cross : equalCheck
    (mul hPairUpper8Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper8Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper8Numerator) hPairUpper8Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairUpper8. -/
def hPairUpper8Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (1) 8) :=
  (hPairUpper8Raw.congr hPairUpper8Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper8Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper8Denominator)
    hPairUpper8DenNonzero hPairUpper8Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst368Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst368Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst368Raw : RationalCode Source.domain (fun z => (z.1)^9) :=
  ((RationalCode.first Source.domain).pow 9)
private theorem hAst368DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst368Denominator=true := by kernel_decide
private theorem hAst368DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst368Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst368Denominator hAst368DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst368Cross : equalCheck
    (mul hAst368Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst368Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst368Numerator) hAst368Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst368Code : RationalCode Source.domain (fun z => (z.1)^9) :=
  hAst368Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst368Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst368Denominator)
    hAst368DenNonzero hAst368Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst369Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-9,0,48,0,36,0,144,0,74,0,144,0,36,0,48,0,-9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst369Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst369Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 9 (radialCosine z.1))*(z.1)^9)) :=
  (hT9Code.mul hAst368Code)
private theorem hAst369DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst369Denominator=true := by kernel_decide
private theorem hAst369DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst369Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst369Denominator hAst369DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst369Cross : equalCheck
    (mul hAst369Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst369Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst369Numerator) hAst369Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst369Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 9 (radialCosine z.1))*(z.1)^9)) :=
  hAst369Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst369Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst369Denominator)
    hAst369DenNonzero hAst369Cross

/-- Article: proposed exact numerator for hPowerReal9. -/
def hPowerReal9Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-9,0,48,0,36,0,144,0,74,0,144,0,36,0,48,0,-9]]
/-- Article: proposed positive denominator for hPowerReal9. -/
def hPowerReal9Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerReal9Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 9 (radialCosine z.1))*(z.1)^9)) :=
  (hAst369Code.congr (by
    intro z hz
    ring))
private theorem hPowerReal9Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebT 9 (radialCosine z.1))*(z.1)^9)=Source.powerReal z.1 9 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.powerReal]; ring
private theorem hPowerReal9DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerReal9Denominator=true := by kernel_decide
private theorem hPowerReal9DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal9Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerReal9Denominator hPowerReal9DenCheck hz.1 hz.2).ne'
private theorem hPowerReal9Cross : equalCheck
    (mul hPowerReal9Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal9Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal9Numerator) hPowerReal9Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerReal9. -/
def hPowerReal9Code : RationalCode Source.domain (fun z => Source.powerReal z.1 9) :=
  (hPowerReal9Raw.congr hPowerReal9Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal9Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal9Denominator)
    hPowerReal9DenNonzero hPowerReal9Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst370Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-32,0,28,0,-32,0,70,0,-32,0,28,0,-32,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst370Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst370Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 8 (radialCosine z.1))*(z.1)^8)) :=
  (hU8Code.mul hAst169Code)
private theorem hAst370DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst370Denominator=true := by kernel_decide
private theorem hAst370DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst370Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst370Denominator hAst370DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst370Cross : equalCheck
    (mul hAst370Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst370Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst370Numerator) hAst370Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst370Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 8 (radialCosine z.1))*(z.1)^8)) :=
  hAst370Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst370Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst370Denominator)
    hAst370DenNonzero hAst370Cross

/-- Article: proposed exact numerator for hPowerImag9. -/
def hPowerImag9Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-32,0,28,0,-32,0,70,0,-32,0,28,0,-32,0,1]]
/-- Article: proposed positive denominator for hPowerImag9. -/
def hPowerImag9Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerImag9Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 8 (radialCosine z.1))*(z.1)^8)) :=
  (hAst370Code.congr (by
    intro z hz
    ring))
private theorem hPowerImag9Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebU 8 (radialCosine z.1))*(z.1)^8)=Source.powerImag z.1 9 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.powerImag,ite_eq_right (by decide)]; ring
private theorem hPowerImag9DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerImag9Denominator=true := by kernel_decide
private theorem hPowerImag9DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag9Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerImag9Denominator hPowerImag9DenCheck hz.1 hz.2).ne'
private theorem hPowerImag9Cross : equalCheck
    (mul hPowerImag9Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag9Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag9Numerator) hPowerImag9Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerImag9. -/
def hPowerImag9Code : RationalCode Source.domain (fun z => Source.powerImag z.1 9) :=
  (hPowerImag9Raw.congr hPowerImag9Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag9Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag9Denominator)
    hPowerImag9DenNonzero hPowerImag9Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst371Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,9,0,-48,0,-36,0,-144,0,-74,0,-144,0,-36,0,-48,0,9],[0],[0,0,0,0,0,0,0,0,0,0,9,0,-48,0,-36,0,-144,0,-74,0,-144,0,-36,0,-48,0,9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst371Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,20,0,90,0,240,0,420,0,504,0,420,0,240,0,90,0,20,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst371Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 9)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerReal9Code.mul hSRealCode)
private theorem hAst371DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst371Denominator=true := by kernel_decide
private theorem hAst371DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst371Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst371Denominator hAst371DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst371Cross : equalCheck
    (mul hAst371Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst371Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst371Numerator) hAst371Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst371Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 9)*(Source.multiplierReal z.1 z.2))) :=
  hAst371Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst371Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst371Denominator)
    hAst371DenNonzero hAst371Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst372Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,31,0,3,0,36,0,-66,0,-6,0,-66,0,36,0,3,0,31,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst372Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,10,0,45,0,120,0,210,0,252,0,210,0,120,0,45,0,10,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst372Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))) :=
  (hAst002Code.mul hPowerImag9Code)
private theorem hAst372DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst372Denominator=true := by kernel_decide
private theorem hAst372DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst372Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst372Denominator hAst372DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst372Cross : equalCheck
    (mul hAst372Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst372Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst372Numerator) hAst372Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst372Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))) :=
  hAst372Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst372Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst372Denominator)
    hAst372DenNonzero hAst372Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst373Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,31,0,3,0,36,0,-66,0,-6,0,-66,0,36,0,3,0,31,0,-1],[0],[0,0,0,0,0,0,0,0,1,0,-31,0,-3,0,-36,0,66,0,6,0,66,0,-36,0,-3,0,-31,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst373Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,20,0,90,0,240,0,420,0,504,0,420,0,240,0,90,0,20,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst373Raw : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))*(Source.multiplierImag z.1 z.2))) :=
  (hAst372Code.mul hSImagCode)
private theorem hAst373DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst373Denominator=true := by kernel_decide
private theorem hAst373DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst373Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst373Denominator hAst373DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst373Cross : equalCheck
    (mul hAst373Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst373Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst373Numerator) hAst373Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst373Code : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))*(Source.multiplierImag z.1 z.2))) :=
  hAst373Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst373Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst373Denominator)
    hAst373DenNonzero hAst373Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst374Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,40,0,-45,0,0,0,-210,0,-80,0,-210,0,0,0,-45,0,40,0,-1],[0],[0,0,0,0,0,0,0,0,1,0,-22,0,-51,0,-72,0,-78,0,-68,0,-78,0,-72,0,-51,0,-22,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst374Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,20,0,90,0,240,0,420,0,504,0,420,0,240,0,90,0,20,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst374Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 9)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))*(Source.multiplierImag z.1 z.2)))) :=
  (hAst371Code.add hAst373Code)
private theorem hAst374DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst374Denominator=true := by kernel_decide
private theorem hAst374DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst374Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst374Denominator hAst374DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst374Cross : equalCheck
    (mul hAst374Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst374Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst374Numerator) hAst374Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst374Code : RationalCode Source.domain (fun z => (((Source.powerReal z.1 9)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))*(Source.multiplierImag z.1 z.2)))) :=
  hAst374Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst374Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst374Denominator)
    hAst374DenNonzero hAst374Cross

/-- Article: proposed exact numerator for hGradientReal9. -/
def hGradientReal9Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,40,0,-45,0,0,0,-210,0,-80,0,-210,0,0,0,-45,0,40,0,-1],[0],[0,0,0,0,0,0,0,0,1,0,-22,0,-51,0,-72,0,-78,0,-68,0,-78,0,-72,0,-51,0,-22,0,1]]
/-- Article: proposed positive denominator for hGradientReal9. -/
def hGradientReal9Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,20,0,90,0,240,0,420,0,504,0,420,0,240,0,90,0,20,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientReal9Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 9)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 9)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst374Code.congr (by
    intro z hz
    ring))
private theorem hGradientReal9Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerReal z.1 9)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 9)*(Source.multiplierImag z.1 z.2)))=Source.gradientReal z.1 z.2 9 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientReal]; ring
private theorem hGradientReal9DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientReal9Denominator=true := by kernel_decide
private theorem hGradientReal9DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal9Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientReal9Denominator hGradientReal9DenCheck hz.1 hz.2).ne'
private theorem hGradientReal9Cross : equalCheck
    (mul hGradientReal9Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal9Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal9Numerator) hGradientReal9Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientReal9. -/
def hGradientReal9Code : RationalCode Source.domain (fun z => Source.gradientReal z.1 z.2 9) :=
  (hGradientReal9Raw.congr hGradientReal9Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal9Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal9Denominator)
    hGradientReal9DenNonzero hGradientReal9Cross

end
end polyak.Certificates.Startup.Codes
