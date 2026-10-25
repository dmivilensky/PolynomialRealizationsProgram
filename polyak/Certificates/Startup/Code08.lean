import polyak.Certificates.Startup.Code07

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: canonical numerator for one arithmetic source node. -/
def hAst150Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-2,0,0,0,-2],[0],[0,0,0,0,-2,0,0,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst150Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,4,0,6,0,4,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst150Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 4)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerImag4Code.mul hSRealCode)
private theorem hAst150DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst150Denominator=true := by kernel_decide
private theorem hAst150DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst150Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst150Denominator hAst150DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst150Cross : equalCheck
    (mul hAst150Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst150Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst150Numerator) hAst150Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst150Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 4)*(Source.multiplierReal z.1 z.2))) :=
  hAst150Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst150Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst150Denominator)
    hAst150DenNonzero hAst150Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst151Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-4,0,-2,0,-4,0,1],[0],[0,0,-1,0,4,0,2,0,4,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst151Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst151Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 4)*(Source.multiplierImag z.1 z.2))) :=
  (hPowerReal4Code.mul hSImagCode)
private theorem hAst151DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst151Denominator=true := by kernel_decide
private theorem hAst151DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst151Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst151Denominator hAst151DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst151Cross : equalCheck
    (mul hAst151Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst151Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst151Numerator) hAst151Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst151Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 4)*(Source.multiplierImag z.1 z.2))) :=
  hAst151Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst151Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst151Denominator)
    hAst151DenNonzero hAst151Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst152Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-8,0,-2,0,-8,0,1],[0],[0,0,-1,0,0,0,2,0,0,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst152Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst152Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 4)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 4)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst150Code.add hAst151Code)
private theorem hAst152DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst152Denominator=true := by kernel_decide
private theorem hAst152DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst152Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst152Denominator hAst152DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst152Cross : equalCheck
    (mul hAst152Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst152Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst152Numerator) hAst152Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst152Code : RationalCode Source.domain (fun z => (((Source.powerImag z.1 4)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 4)*(Source.multiplierImag z.1 z.2)))) :=
  hAst152Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst152Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst152Denominator)
    hAst152DenNonzero hAst152Cross

/-- Article: proposed exact numerator for hGradientImag4. -/
def hGradientImag4Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-8,0,-2,0,-8,0,1],[0],[0,0,-1,0,0,0,2,0,0,0,-1]]
/-- Article: proposed positive denominator for hGradientImag4. -/
def hGradientImag4Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientImag4Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 4)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 4)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst152Code.congr (by
    intro z hz
    ring))
private theorem hGradientImag4Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerImag z.1 4)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 4)*(Source.multiplierImag z.1 z.2)))=Source.gradientImag z.1 z.2 4 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientImag]; ring
private theorem hGradientImag4DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientImag4Denominator=true := by kernel_decide
private theorem hGradientImag4DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag4Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientImag4Denominator hGradientImag4DenCheck hz.1 hz.2).ne'
private theorem hGradientImag4Cross : equalCheck
    (mul hGradientImag4Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag4Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag4Numerator) hGradientImag4Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientImag4. -/
def hGradientImag4Code : RationalCode Source.domain (fun z => Source.gradientImag z.1 z.2 4) :=
  (hGradientImag4Raw.congr hGradientImag4Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag4Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag4Denominator)
    hGradientImag4DenNonzero hGradientImag4Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst153Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-5,0,0,0,-6,0,0,0,-5],[0],[-2,0,-9,0,-13,0,-6,0,4,0,7,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst153Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst153Raw : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  (hGradientReal4Code.add hAst009Code)
private theorem hAst153DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst153Denominator=true := by kernel_decide
private theorem hAst153DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst153Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst153Denominator hAst153DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst153Cross : equalCheck
    (mul hAst153Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst153Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst153Numerator) hAst153Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst153Code : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  hAst153Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst153Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst153Denominator)
    hAst153DenNonzero hAst153Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst154Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,4,0,1,0,4,0,-5,0,0,0,-5],[0],[-1,0,-5,0,-7,0,-2,0,5,0,7,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst154Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst154Raw : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  (hAst153Code.add hAst010Code)
private theorem hAst154DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst154Denominator=true := by kernel_decide
private theorem hAst154DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst154Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst154Denominator hAst154DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst154Cross : equalCheck
    (mul hAst154Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst154Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst154Numerator) hAst154Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst154Code : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  hAst154Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst154Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst154Denominator)
    hAst154DenNonzero hAst154Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst155Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,8,0,18,0,16,0,23,0,-32,0,-4,0,-80,0,15,0,-40,0,50,0,0,0,25],[0],[0,0,-2,0,-18,0,-56,0,-78,0,-50,0,44,0,136,0,148,0,82,0,-26,0,-80,0,-70,0,-30],[0],[1,0,10,0,39,0,74,0,59,0,-36,0,-142,0,-148,0,-45,0,58,0,79,0,42,0,9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst155Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,40,0,180,0,480,0,840,0,1008,0,840,0,480,0,180,0,40,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst155Raw : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  (hAst154Code.pow 2)
private theorem hAst155DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst155Denominator=true := by kernel_decide
private theorem hAst155DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst155Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst155Denominator hAst155DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst155Cross : equalCheck
    (mul hAst155Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst155Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst155Numerator) hAst155Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst155Code : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  hAst155Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst155Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst155Denominator)
    hAst155DenNonzero hAst155Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst156Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-8,0,-18,0,-16,0,-23,0,32,0,4,0,80,0,-15,0,40,0,-50,0,0,0,-25],[0],[0,0,2,0,18,0,56,0,78,0,50,0,-44,0,-136,0,-148,0,-82,0,26,0,80,0,70,0,30],[0],[-1,0,-10,0,-39,0,-74,0,-59,0,36,0,142,0,148,0,45,0,-58,0,-79,0,-42,0,-9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst156Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst156Raw : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  ((RationalCode.constant Source.domain (-1/4)).mul hAst155Code)
private theorem hAst156DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst156Denominator=true := by kernel_decide
private theorem hAst156DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst156Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst156Denominator hAst156DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst156Cross : equalCheck
    (mul hAst156Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst156Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst156Numerator) hAst156Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst156Code : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  hAst156Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst156Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst156Denominator)
    hAst156DenNonzero hAst156Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst157Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-4,0,-5,0,-8,0,-3,0,-4,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst157Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst157Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4))) :=
  ((RationalCode.constant Source.domain (-1)).add hPowerReal4Code)
private theorem hAst157DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst157Denominator=true := by kernel_decide
private theorem hAst157DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst157Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst157Denominator hAst157DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst157Cross : equalCheck
    (mul hAst157Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst157Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst157Numerator) hAst157Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst157Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4))) :=
  hAst157Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst157Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst157Denominator)
    hAst157DenNonzero hAst157Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst158Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,26,0,56,0,95,0,112,0,124,0,80,0,63,0,8,0,10,0,-8,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst158Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst158Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2) :=
  (hAst157Code.pow 2)
private theorem hAst158DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst158Denominator=true := by kernel_decide
private theorem hAst158DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst158Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst158Denominator hAst158DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst158Cross : equalCheck
    (mul hAst158Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst158Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst158Numerator) hAst158Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst158Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2) :=
  hAst158Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst158Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst158Denominator)
    hAst158DenNonzero hAst158Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst159Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,26,0,56,0,95,0,112,0,124,0,80,0,63,0,8,0,10,0,-8,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst159Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,32,0,112,0,224,0,280,0,224,0,112,0,32,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst159Raw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2)) :=
  ((RationalCode.constant Source.domain (1/4)).mul hAst158Code)
private theorem hAst159DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst159Denominator=true := by kernel_decide
private theorem hAst159DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst159Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst159Denominator hAst159DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst159Cross : equalCheck
    (mul hAst159Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst159Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst159Numerator) hAst159Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst159Code : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2)) :=
  hAst159Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst159Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst159Denominator)
    hAst159DenNonzero hAst159Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst160Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,1,0,-8,0,-2,0,-8,0,1],[0],[-1,0,-4,0,-7,0,-4,0,1,0,0,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst160Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst160Raw : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  (hGradientImag4Code.add hAst018Code)
private theorem hAst160DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst160Denominator=true := by kernel_decide
private theorem hAst160DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst160Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst160Denominator hAst160DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst160Cross : equalCheck
    (mul hAst160Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst160Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst160Numerator) hAst160Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst160Code : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  hAst160Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst160Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst160Denominator)
    hAst160DenNonzero hAst160Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst161Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-4,0,-5,0,-12,0,-3,0,-8,0,1],[0],[0,0,-1,0,0,0,2,0,0,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst161Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst161Raw : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst160Code.add hAst019Code)
private theorem hAst161DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst161Denominator=true := by kernel_decide
private theorem hAst161DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst161Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst161Denominator hAst161DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst161Cross : equalCheck
    (mul hAst161Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst161Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst161Numerator) hAst161Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst161Code : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  hAst161Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst161Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst161Denominator)
    hAst161DenNonzero hAst161Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst162Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,26,0,64,0,127,0,160,0,236,0,144,0,191,0,24,0,58,0,-16,0,1],[0],[0,0,2,0,8,0,6,0,8,0,-12,0,-24,0,-4,0,-8,0,10,0,16,0,-2],[0],[0,0,0,0,1,0,0,0,-4,0,0,0,6,0,0,0,-4,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst162Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,32,0,112,0,224,0,280,0,224,0,112,0,32,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst162Raw : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  (hAst161Code.pow 2)
private theorem hAst162DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst162Denominator=true := by kernel_decide
private theorem hAst162DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst162Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst162Denominator hAst162DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst162Cross : equalCheck
    (mul hAst162Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst162Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst162Numerator) hAst162Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst162Code : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  hAst162Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst162Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst162Denominator)
    hAst162DenNonzero hAst162Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst163Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-35,0,-98,0,-217,0,-351,0,-523,0,-540,0,-571,0,-359,0,-273,0,-66,0,-43,0,15,0,-1],[0],[0,0,0,0,-2,0,-10,0,-16,0,-22,0,-2,0,28,0,40,0,36,0,2,0,-18,0,-24,0,-14,0,2],[0],[0,0,0,0,0,0,-1,0,-1,0,3,0,4,0,-2,0,-6,0,-2,0,4,0,3,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst163Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst163Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  (hAst023Code.mul hAst162Code)
private theorem hAst163DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst163Denominator=true := by kernel_decide
private theorem hAst163DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst163Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst163Denominator hAst163DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst163Cross : equalCheck
    (mul hAst163Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst163Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst163Numerator) hAst163Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst163Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  hAst163Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst163Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst163Denominator)
    hAst163DenNonzero hAst163Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst164Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,16,0,0,0,32,0,0,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst164Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst164Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 4))^2) :=
  (hPowerImag4Code.pow 2)
private theorem hAst164DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst164Denominator=true := by kernel_decide
private theorem hAst164DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst164Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst164Denominator hAst164DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst164Cross : equalCheck
    (mul hAst164Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst164Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst164Numerator) hAst164Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst164Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 4))^2) :=
  hAst164Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst164Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst164Denominator)
    hAst164DenNonzero hAst164Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst165Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,4,0,4,0,12,0,8,0,12,0,4,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst165Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst165Raw : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 4))^2)) :=
  (hAst026Code.mul hAst164Code)
private theorem hAst165DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst165Denominator=true := by kernel_decide
private theorem hAst165DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst165Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst165Denominator hAst165DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst165Cross : equalCheck
    (mul hAst165Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst165Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst165Numerator) hAst165Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst165Code : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 4))^2)) :=
  hAst165Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst165Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst165Denominator)
    hAst165DenNonzero hAst165Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst166Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-8,0,-18,0,-16,0,-23,0,32,0,4,0,80,0,-15,0,40,0,-50,0,0,0,-25],[0],[4,0,42,0,190,0,520,0,1010,0,1482,0,1728,0,1624,0,1240,0,774,0,382,0,160,0,50,0,6,0,4],[0],[-1,0,-10,0,-39,0,-74,0,-59,0,36,0,142,0,148,0,45,0,-58,0,-79,0,-42,0,-9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst166Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst166Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2))) :=
  (hAst156Code.add hAst159Code)
private theorem hAst166DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst166Denominator=true := by kernel_decide
private theorem hAst166DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst166Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst166Denominator hAst166DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst166Cross : equalCheck
    (mul hAst166Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst166Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst166Numerator) hAst166Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst166Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2))) :=
  hAst166Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst166Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst166Denominator)
    hAst166DenNonzero hAst166Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst167Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-26,0,-56,0,-95,0,-128,0,-140,0,-128,0,-95,0,-56,0,-26,0,-8,0,-1],[0],[4,0,34,0,116,0,244,0,390,0,436,0,464,0,288,0,240,0,42,0,60,0,-20,0,6],[0],[-1,0,-8,0,-22,0,-23,0,8,0,46,0,46,0,8,0,-23,0,-22,0,-8,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst167Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst167Raw : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  (hAst166Code.add hAst163Code)
private theorem hAst167DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst167Denominator=true := by kernel_decide
private theorem hAst167DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst167Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst167Denominator hAst167DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst167Cross : equalCheck
    (mul hAst167Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst167Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst167Numerator) hAst167Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst167Code : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  hAst167Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst167Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst167Denominator)
    hAst167DenNonzero hAst167Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst168Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0],[4,0,22,0,38,0,60,0,74,0,60,0,66,0,28,0,26,0,6],[0],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst168Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst168Raw : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 4))^2))) :=
  (hAst167Code.add hAst165Code)
private theorem hAst168DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst168Denominator=true := by kernel_decide
private theorem hAst168DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst168Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst168Denominator hAst168DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst168Cross : equalCheck
    (mul hAst168Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst168Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst168Numerator) hAst168Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst168Code : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 4))^2))) :=
  hAst168Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst168Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst168Denominator)
    hAst168DenNonzero hAst168Cross

/-- Article: proposed exact numerator for hRadius4. -/
def hRadius4Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0],[4,0,22,0,38,0,60,0,74,0,60,0,66,0,28,0,26,0,6],[0],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1]]
/-- Article: proposed positive denominator for hRadius4. -/
def hRadius4Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hRadius4Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 4))^2))) :=
  (hAst168Code.congr (by
    intro z hz
    ring))
private theorem hRadius4Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 4)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 4))^2))=Source.radius z.1 z.2 4 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.radius]; ring
private theorem hRadius4DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hRadius4Denominator=true := by kernel_decide
private theorem hRadius4DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hRadius4Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hRadius4Denominator hRadius4DenCheck hz.1 hz.2).ne'
private theorem hRadius4Cross : equalCheck
    (mul hRadius4Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hRadius4Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hRadius4Numerator) hRadius4Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hRadius4. -/
def hRadius4Code : RationalCode Source.domain (fun z => Source.radius z.1 z.2 4) :=
  (hRadius4Raw.congr hRadius4Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius4Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius4Denominator)
    hRadius4DenNonzero hRadius4Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst169Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst169Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst169Raw : RationalCode Source.domain (fun z => (z.1)^8) :=
  ((RationalCode.first Source.domain).pow 8)
private theorem hAst169DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst169Denominator=true := by kernel_decide
private theorem hAst169DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst169Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst169Denominator hAst169DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst169Cross : equalCheck
    (mul hAst169Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst169Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst169Numerator) hAst169Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst169Code : RationalCode Source.domain (fun z => (z.1)^8) :=
  hAst169Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst169Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst169Denominator)
    hAst169DenNonzero hAst169Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst170Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst170Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst170Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^8)) :=
  ((RationalCode.constant Source.domain (-1)).add hAst169Code)
private theorem hAst170DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst170Denominator=true := by kernel_decide
private theorem hAst170DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst170Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst170Denominator hAst170DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst170Cross : equalCheck
    (mul hAst170Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst170Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst170Numerator) hAst170Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst170Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^8)) :=
  hAst170Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst170Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst170Denominator)
    hAst170DenNonzero hAst170Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst171Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,1,0,0,0,0,0,-1,0,-1],[0,2,-2,-2,4,0,-4,0,4,-2,-2,2],[1,0,1,0,0,0,0,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst171Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,8,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst171Raw : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^8))) :=
  (hValueCode.mul hAst170Code)
private theorem hAst171DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst171Denominator=true := by kernel_decide
private theorem hAst171DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst171Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst171Denominator hAst171DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst171Cross : equalCheck
    (mul hAst171Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst171Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst171Numerator) hAst171Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst171Code : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^8))) :=
  hAst171Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst171Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst171Denominator)
    hAst171DenNonzero hAst171Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst172Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-5,0,0,0,-6,0,0,0,-5],[0],[2,0,9,0,19,0,22,0,16,0,9,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst172Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst172Raw : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4))) :=
  (hDRealCode.add hGradientReal4Code)
private theorem hAst172DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst172Denominator=true := by kernel_decide
private theorem hAst172DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst172Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst172Denominator hAst172DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst172Cross : equalCheck
    (mul hAst172Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst172Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst172Numerator) hAst172Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst172Code : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4))) :=
  hAst172Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst172Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst172Denominator)
    hAst172DenNonzero hAst172Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst173Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,-11,0,-4,0,-7,0,0,0,-5],[0],[1,0,5,0,13,0,18,0,15,0,9,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst173Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst173Raw : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4))+(Source.multiplierReal z.1 z.2))) :=
  (hAst172Code.add hSRealCode)
private theorem hAst173DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst173Denominator=true := by kernel_decide
private theorem hAst173DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst173Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst173Denominator hAst173DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst173Cross : equalCheck
    (mul hAst173Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst173Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst173Numerator) hAst173Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst173Code : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4))+(Source.multiplierReal z.1 z.2))) :=
  hAst173Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst173Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst173Denominator)
    hAst173DenNonzero hAst173Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst174Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,5,0,8,0,3,0,4,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst174Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst174Raw : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))) :=
  ((RationalCode.constant Source.domain (-1/2)).mul hAst157Code)
private theorem hAst174DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst174Denominator=true := by kernel_decide
private theorem hAst174DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst174Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst174Denominator hAst174DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst174Cross : equalCheck
    (mul hAst174Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst174Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst174Numerator) hAst174Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst174Code : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))) :=
  hAst174Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst174Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst174Denominator)
    hAst174DenNonzero hAst174Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst175Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-32,0,-76,0,-113,0,-152,0,-120,0,-128,0,-51,0,-64,0,-8,0,-20,0,5],[0],[1,0,9,0,38,0,103,0,195,0,282,0,316,0,278,0,191,0,93,0,30,0,3,0,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst175Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,36,0,144,0,336,0,504,0,504,0,336,0,144,0,36,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst175Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4))+(Source.multiplierReal z.1 z.2)))) :=
  (hAst174Code.mul hAst173Code)
private theorem hAst175DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst175Denominator=true := by kernel_decide
private theorem hAst175DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst175Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst175Denominator hAst175DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst175Cross : equalCheck
    (mul hAst175Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst175Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst175Numerator) hAst175Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst175Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4))+(Source.multiplierReal z.1 z.2)))) :=
  hAst175Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst175Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst175Denominator)
    hAst175DenNonzero hAst175Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst176Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,1,0,-8,0,-2,0,-8,0,1],[0],[1,0,4,0,5,0,4,0,3,0,0,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst176Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst176Raw : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 4))) :=
  (hDImagCode.add hGradientImag4Code)
private theorem hAst176DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst176Denominator=true := by kernel_decide
private theorem hAst176DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst176Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst176Denominator hAst176DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst176Cross : equalCheck
    (mul hAst176Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst176Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst176Numerator) hAst176Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst176Code : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 4))) :=
  hAst176Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst176Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst176Denominator)
    hAst176DenNonzero hAst176Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst177Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,7,0,-4,0,-1,0,-8,0,1],[0],[0,0,-1,0,0,0,2,0,0,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst177Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,8,0,12,0,8,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst177Raw : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 4))+(Source.multiplierImag z.1 z.2))) :=
  (hAst176Code.add hSImagCode)
private theorem hAst177DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst177Denominator=true := by kernel_decide
private theorem hAst177DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst177Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst177Denominator hAst177DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst177Cross : equalCheck
    (mul hAst177Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst177Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst177Numerator) hAst177Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst177Code : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 4))+(Source.multiplierImag z.1 z.2))) :=
  hAst177Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst177Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst177Denominator)
    hAst177DenNonzero hAst177Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst178Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-2,0,-2,0,-4,0,-2,0,-2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst178Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst178Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))) :=
  (hAst040Code.mul hPowerImag4Code)
private theorem hAst178DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst178Denominator=true := by kernel_decide
private theorem hAst178DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst178Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst178Denominator hAst178DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst178Cross : equalCheck
    (mul hAst178Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst178Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst178Numerator) hAst178Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst178Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))) :=
  hAst178Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst178Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst178Denominator)
    hAst178DenNonzero hAst178Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst179Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,-5,0,-13,0,-12,0,-14,0,6,0,6,0,20,0,7,0,7,0,-1],[0],[0,0,0,0,0,0,0,0,1,0,1,0,0,0,-1,0,-2,0,-1,0,0,0,1,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst179Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst179Raw : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 4))+(Source.multiplierImag z.1 z.2)))) :=
  (hAst178Code.mul hAst177Code)
private theorem hAst179DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst179Denominator=true := by kernel_decide
private theorem hAst179DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst179Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst179Denominator hAst179DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst179Cross : equalCheck
    (mul hAst179Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst179Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst179Numerator) hAst179Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst179Code : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 4))+(Source.multiplierImag z.1 z.2)))) :=
  hAst179Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst179Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst179Denominator)
    hAst179DenNonzero hAst179Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst180Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-4,0,-20,0,-44,0,-104,0,-120,0,-176,0,-120,0,-120,0,-36,0,-28,0,4],[0,2,-2,12,-10,28,-18,28,-10,-2,12,-40,28,-56,28,-40,12,-2,-10,28,-18,28,-10,12,-2,2],[2,0,17,0,66,0,159,0,264,0,330,0,316,0,230,0,122,0,37,0,2,0,-5,0,-4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst180Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,36,0,144,0,336,0,504,0,504,0,336,0,144,0,36,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst180Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^8))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4))+(Source.multiplierReal z.1 z.2))))) :=
  (hAst171Code.add hAst175Code)
private theorem hAst180DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst180Denominator=true := by kernel_decide
private theorem hAst180DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst180Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst180Denominator hAst180DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst180Cross : equalCheck
    (mul hAst180Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst180Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst180Numerator) hAst180Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst180Code : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^8))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4))+(Source.multiplierReal z.1 z.2))))) :=
  hAst180Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst180Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst180Denominator)
    hAst180DenNonzero hAst180Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst181Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-8,0,-8,0,-16,0,-8,0,-8],[0,2,-2,4,-2,0,2,-4,2,-4,2,-4,2,0,-2,4,-2,2],[2,0,9,0,18,0,25,0,22,0,15,0,6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst181Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,20,0,40,0,40,0,20,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst181Raw : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^8))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 4))+(Source.multiplierImag z.1 z.2))))) :=
  (hAst180Code.add hAst179Code)
private theorem hAst181DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst181Denominator=true := by kernel_decide
private theorem hAst181DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst181Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst181Denominator hAst181DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst181Cross : equalCheck
    (mul hAst181Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst181Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst181Numerator) hAst181Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst181Code : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^8))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 4))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 4))+(Source.multiplierImag z.1 z.2))))) :=
  hAst181Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst181Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst181Denominator)
    hAst181DenNonzero hAst181Cross

/-- Article: proposed exact numerator for hDiscrepancy4. -/
def hDiscrepancy4Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-8,0,-8,0,-16,0,-8,0,-8],[0,2,-2,4,-2,0,2,-4,2,-4,2,-4,2,0,-2,4,-2,2],[2,0,9,0,18,0,25,0,22,0,15,0,6,0,-1]]
/-- Article: proposed positive denominator for hDiscrepancy4. -/
def hDiscrepancy4Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,20,0,40,0,40,0,20,0,4]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDiscrepancy4Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^8))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 4)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 4)+(Source.multiplierImag z.1 z.2))))) :=
  (hAst181Code.congr (by
    intro z hz
    ring))
private theorem hDiscrepancy4Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^8))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 4))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 4)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 4)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 4)+(Source.multiplierImag z.1 z.2))))=Source.discrepancy z.1 z.2 4 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.discrepancy]; ring
private theorem hDiscrepancy4DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDiscrepancy4Denominator=true := by kernel_decide
private theorem hDiscrepancy4DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy4Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDiscrepancy4Denominator hDiscrepancy4DenCheck hz.1 hz.2).ne'
private theorem hDiscrepancy4Cross : equalCheck
    (mul hDiscrepancy4Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy4Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy4Numerator) hDiscrepancy4Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDiscrepancy4. -/
def hDiscrepancy4Code : RationalCode Source.domain (fun z => Source.discrepancy z.1 z.2 4) :=
  (hDiscrepancy4Raw.congr hDiscrepancy4Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy4Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy4Denominator)
    hDiscrepancy4DenNonzero hDiscrepancy4Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst182Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,8,0,8,0,16,0,8,0,8],[0,-2,2,-4,2,0,-2,4,-2,4,-2,4,-2,0,2,-4,2,-2],[-2,0,-9,0,-18,0,-25,0,-22,0,-15,0,-6,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst182Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,20,0,40,0,40,0,20,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst182Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 4))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDiscrepancy4Code)
private theorem hAst182DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst182Denominator=true := by kernel_decide
private theorem hAst182DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst182Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst182Denominator hAst182DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst182Cross : equalCheck
    (mul hAst182Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst182Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst182Numerator) hAst182Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst182Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 4))) :=
  hAst182Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst182Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst182Denominator)
    hAst182DenNonzero hAst182Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst183Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0],[20,0,102,0,198,0,220,0,154,0,76,0,66,0,28,0,26,0,6],[0],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1],[0],[-32,0,-160,0,-320,0,-320,0,-160,0,-32],[0],[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst183Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst183Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 4)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)) :=
  (hRadius4Code.add hAst138Code)
private theorem hAst183DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst183Denominator=true := by kernel_decide
private theorem hAst183DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst183Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst183Denominator hAst183DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst183Cross : equalCheck
    (mul hAst183Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst183Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst183Numerator) hAst183Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst183Code : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 4)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)) :=
  hAst183Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst183Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst183Denominator)
    hAst183DenNonzero hAst183Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst184Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0,0,0,0,0,0,32,0,32,0,64,0,32,0,32],[20,-8,110,-16,206,0,212,16,146,16,68,16,58,0,36,-16,34,-8,6],[-8,0,-36,0,-72,0,-100,0,-88,0,-60,0,-24,0,4],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1],[0],[-32,0,-160,0,-320,0,-320,0,-160,0,-32],[0],[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst184Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst184Raw : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 4)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 4)))) :=
  (hAst183Code.add hAst182Code)
private theorem hAst184DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst184Denominator=true := by kernel_decide
private theorem hAst184DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst184Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst184Denominator hAst184DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst184Cross : equalCheck
    (mul hAst184Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst184Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst184Numerator) hAst184Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst184Code : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 4)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 4)))) :=
  hAst184Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst184Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst184Denominator)
    hAst184DenNonzero hAst184Cross

/-- Article: proposed exact numerator for hPairLower4. -/
def hPairLower4Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0,0,0,0,0,0,32,0,32,0,64,0,32,0,32],[20,-8,110,-16,206,0,212,16,146,16,68,16,58,0,36,-16,34,-8,6],[-8,0,-36,0,-72,0,-100,0,-88,0,-60,0,-24,0,4],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1],[0],[-32,0,-160,0,-320,0,-320,0,-160,0,-32],[0],[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: proposed positive denominator for hPairLower4. -/
def hPairLower4Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairLower4Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 4)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 4)))) :=
  (hAst184Code.congr (by
    intro z hz
    ring))
private theorem hPairLower4Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.radius z.1 z.2 4)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 4)))=Source.pairSlack z.1 z.2 (-1) 4 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairLower4DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairLower4Denominator=true := by kernel_decide
private theorem hPairLower4DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairLower4Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairLower4Denominator hPairLower4DenCheck hz.1 hz.2).ne'
private theorem hPairLower4Cross : equalCheck
    (mul hPairLower4Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairLower4Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairLower4Numerator) hPairLower4Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairLower4. -/
def hPairLower4Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (-1) 4) :=
  (hPairLower4Raw.congr hPairLower4Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower4Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower4Denominator)
    hPairLower4DenNonzero hPairLower4Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst185Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0,0,0,0,0,0,-32,0,-32,0,-64,0,-32,0,-32],[4,8,14,16,30,0,68,-16,82,-16,68,-16,74,0,20,16,18,8,6],[8,0,36,0,72,0,100,0,88,0,60,0,24,0,-4],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst185Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst185Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 4)+(Source.radius z.1 z.2 4))) :=
  (hDiscrepancy4Code.add hRadius4Code)
private theorem hAst185DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst185Denominator=true := by kernel_decide
private theorem hAst185DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst185Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst185Denominator hAst185DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst185Cross : equalCheck
    (mul hAst185Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst185Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst185Numerator) hAst185Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst185Code : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 4)+(Source.radius z.1 z.2 4))) :=
  hAst185Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst185Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst185Denominator)
    hAst185DenNonzero hAst185Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst186Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0,0,0,0,0,0,-32,0,-32,0,-64,0,-32,0,-32],[20,8,94,16,190,0,228,-16,162,-16,84,-16,74,0,20,16,18,8,6],[8,0,36,0,72,0,100,0,88,0,60,0,24,0,-4],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1],[0],[-32,0,-160,0,-320,0,-320,0,-160,0,-32],[0],[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst186Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst186Raw : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 4)+(Source.radius z.1 z.2 4))+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)) :=
  (hAst185Code.add hAst138Code)
private theorem hAst186DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst186Denominator=true := by kernel_decide
private theorem hAst186DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst186Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst186Denominator hAst186DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst186Cross : equalCheck
    (mul hAst186Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst186Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst186Numerator) hAst186Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst186Code : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 4)+(Source.radius z.1 z.2 4))+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)) :=
  hAst186Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst186Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst186Denominator)
    hAst186DenNonzero hAst186Cross

/-- Article: proposed exact numerator for hPairUpper4. -/
def hPairUpper4Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0,0,0,0,0,0,-32,0,-32,0,-64,0,-32,0,-32],[20,8,94,16,190,0,228,-16,162,-16,84,-16,74,0,20,16,18,8,6],[8,0,36,0,72,0,100,0,88,0,60,0,24,0,-4],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1],[0],[-32,0,-160,0,-320,0,-320,0,-160,0,-32],[0],[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: proposed positive denominator for hPairUpper4. -/
def hPairUpper4Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairUpper4Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 4)+(Source.radius z.1 z.2 4)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)) :=
  (hAst186Code.congr (by
    intro z hz
    ring))
private theorem hPairUpper4Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.discrepancy z.1 z.2 4)+(Source.radius z.1 z.2 4)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^4)))^2)=Source.pairSlack z.1 z.2 (1) 4 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairUpper4DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairUpper4Denominator=true := by kernel_decide
private theorem hPairUpper4DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper4Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairUpper4Denominator hPairUpper4DenCheck hz.1 hz.2).ne'
private theorem hPairUpper4Cross : equalCheck
    (mul hPairUpper4Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper4Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper4Numerator) hPairUpper4Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairUpper4. -/
def hPairUpper4Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (1) 4) :=
  (hPairUpper4Raw.congr hPairUpper4Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper4Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper4Denominator)
    hPairUpper4DenNonzero hPairUpper4Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst187Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst187Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst187Raw : RationalCode Source.domain (fun z => (z.1)^5) :=
  ((RationalCode.first Source.domain).pow 5)
private theorem hAst187DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst187Denominator=true := by kernel_decide
private theorem hAst187DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst187Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst187Denominator hAst187DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst187Cross : equalCheck
    (mul hAst187Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst187Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst187Numerator) hAst187Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst187Code : RationalCode Source.domain (fun z => (z.1)^5) :=
  hAst187Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst187Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst187Denominator)
    hAst187DenNonzero hAst187Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst188Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-5,0,0,0,-6,0,0,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst188Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst188Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 5 (radialCosine z.1))*(z.1)^5)) :=
  (hT5Code.mul hAst187Code)
private theorem hAst188DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst188Denominator=true := by kernel_decide
private theorem hAst188DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst188Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst188Denominator hAst188DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst188Cross : equalCheck
    (mul hAst188Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst188Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst188Numerator) hAst188Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst188Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 5 (radialCosine z.1))*(z.1)^5)) :=
  hAst188Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst188Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst188Denominator)
    hAst188DenNonzero hAst188Cross

/-- Article: proposed exact numerator for hPowerReal5. -/
def hPowerReal5Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-5,0,0,0,-6,0,0,0,-5]]
/-- Article: proposed positive denominator for hPowerReal5. -/
def hPowerReal5Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerReal5Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 5 (radialCosine z.1))*(z.1)^5)) :=
  (hAst188Code.congr (by
    intro z hz
    ring))
private theorem hPowerReal5Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebT 5 (radialCosine z.1))*(z.1)^5)=Source.powerReal z.1 5 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.powerReal]; ring
private theorem hPowerReal5DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerReal5Denominator=true := by kernel_decide
private theorem hPowerReal5DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal5Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerReal5Denominator hPowerReal5DenCheck hz.1 hz.2).ne'
private theorem hPowerReal5Cross : equalCheck
    (mul hPowerReal5Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal5Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal5Numerator) hPowerReal5Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerReal5. -/
def hPowerReal5Code : RationalCode Source.domain (fun z => Source.powerReal z.1 5) :=
  (hPowerReal5Raw.congr hPowerReal5Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal5Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal5Denominator)
    hPowerReal5DenNonzero hPowerReal5Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst189Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-8,0,-2,0,-8,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst189Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst189Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 4 (radialCosine z.1))*(z.1)^4)) :=
  (hU4Code.mul hAst078Code)
private theorem hAst189DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst189Denominator=true := by kernel_decide
private theorem hAst189DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst189Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst189Denominator hAst189DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst189Cross : equalCheck
    (mul hAst189Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst189Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst189Numerator) hAst189Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst189Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 4 (radialCosine z.1))*(z.1)^4)) :=
  hAst189Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst189Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst189Denominator)
    hAst189DenNonzero hAst189Cross

/-- Article: proposed exact numerator for hPowerImag5. -/
def hPowerImag5Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,-8,0,-2,0,-8,0,1]]
/-- Article: proposed positive denominator for hPowerImag5. -/
def hPowerImag5Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,4,0,6,0,4,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerImag5Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 4 (radialCosine z.1))*(z.1)^4)) :=
  (hAst189Code.congr (by
    intro z hz
    ring))
private theorem hPowerImag5Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebU 4 (radialCosine z.1))*(z.1)^4)=Source.powerImag z.1 5 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.powerImag,ite_eq_right (by decide)]; ring
private theorem hPowerImag5DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerImag5Denominator=true := by kernel_decide
private theorem hPowerImag5DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag5Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerImag5Denominator hPowerImag5DenCheck hz.1 hz.2).ne'
private theorem hPowerImag5Cross : equalCheck
    (mul hPowerImag5Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag5Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag5Numerator) hPowerImag5Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerImag5. -/
def hPowerImag5Code : RationalCode Source.domain (fun z => Source.powerImag z.1 5) :=
  (hPowerImag5Raw.congr hPowerImag5Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag5Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag5Denominator)
    hPowerImag5DenNonzero hPowerImag5Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst190Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,5,0,0,0,6,0,0,0,5],[0],[0,0,0,0,0,0,5,0,0,0,6,0,0,0,5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst190Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst190Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 5)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerReal5Code.mul hSRealCode)
private theorem hAst190DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst190Denominator=true := by kernel_decide
private theorem hAst190DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst190Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst190Denominator hAst190DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst190Cross : equalCheck
    (mul hAst190Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst190Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst190Numerator) hAst190Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst190Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 5)*(Source.multiplierReal z.1 z.2))) :=
  hAst190Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst190Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst190Denominator)
    hAst190DenNonzero hAst190Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst191Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,7,0,9,0,18,0,9,0,7,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst191Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst191Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))) :=
  (hAst002Code.mul hPowerImag5Code)
private theorem hAst191DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst191Denominator=true := by kernel_decide
private theorem hAst191DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst191Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst191Denominator hAst191DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst191Cross : equalCheck
    (mul hAst191Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst191Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst191Numerator) hAst191Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst191Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))) :=
  hAst191Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst191Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst191Denominator)
    hAst191DenNonzero hAst191Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst192Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,7,0,9,0,18,0,9,0,7,0,-1],[0],[0,0,0,0,1,0,-7,0,-9,0,-18,0,-9,0,-7,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst192Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst192Raw : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))*(Source.multiplierImag z.1 z.2))) :=
  (hAst191Code.mul hSImagCode)
private theorem hAst192DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst192Denominator=true := by kernel_decide
private theorem hAst192DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst192Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst192Denominator hAst192DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst192Cross : equalCheck
    (mul hAst192Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst192Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst192Numerator) hAst192Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst192Code : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))*(Source.multiplierImag z.1 z.2))) :=
  hAst192Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst192Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst192Denominator)
    hAst192DenNonzero hAst192Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst193Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,12,0,9,0,24,0,9,0,12,0,-1],[0],[0,0,0,0,1,0,-2,0,-9,0,-12,0,-9,0,-2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst193Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst193Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 5)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))*(Source.multiplierImag z.1 z.2)))) :=
  (hAst190Code.add hAst192Code)
private theorem hAst193DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst193Denominator=true := by kernel_decide
private theorem hAst193DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst193Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst193Denominator hAst193DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst193Cross : equalCheck
    (mul hAst193Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst193Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst193Numerator) hAst193Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst193Code : RationalCode Source.domain (fun z => (((Source.powerReal z.1 5)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))*(Source.multiplierImag z.1 z.2)))) :=
  hAst193Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst193Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst193Denominator)
    hAst193DenNonzero hAst193Cross

/-- Article: proposed exact numerator for hGradientReal5. -/
def hGradientReal5Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,12,0,9,0,24,0,9,0,12,0,-1],[0],[0,0,0,0,1,0,-2,0,-9,0,-12,0,-9,0,-2,0,1]]
/-- Article: proposed positive denominator for hGradientReal5. -/
def hGradientReal5Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientReal5Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 5)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 5)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst193Code.congr (by
    intro z hz
    ring))
private theorem hGradientReal5Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerReal z.1 5)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 5)*(Source.multiplierImag z.1 z.2)))=Source.gradientReal z.1 z.2 5 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientReal]; ring
private theorem hGradientReal5DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientReal5Denominator=true := by kernel_decide
private theorem hGradientReal5DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal5Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientReal5Denominator hGradientReal5DenCheck hz.1 hz.2).ne'
private theorem hGradientReal5Cross : equalCheck
    (mul hGradientReal5Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal5Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal5Numerator) hGradientReal5Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientReal5. -/
def hGradientReal5Code : RationalCode Source.domain (fun z => Source.gradientReal z.1 z.2 5) :=
  (hGradientReal5Raw.congr hGradientReal5Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal5Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal5Denominator)
    hGradientReal5DenNonzero hGradientReal5Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst194Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,8,0,2,0,8,0,-1],[0],[0,0,0,0,-1,0,8,0,2,0,8,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst194Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst194Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 5)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerImag5Code.mul hSRealCode)
private theorem hAst194DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst194Denominator=true := by kernel_decide
private theorem hAst194DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst194Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst194Denominator hAst194DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst194Cross : equalCheck
    (mul hAst194Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst194Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst194Numerator) hAst194Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst194Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 5)*(Source.multiplierReal z.1 z.2))) :=
  hAst194Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst194Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst194Denominator)
    hAst194DenNonzero hAst194Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst195Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-5,0,0,0,-6,0,0,0,-5],[0],[0,0,0,0,5,0,0,0,6,0,0,0,5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst195Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst195Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 5)*(Source.multiplierImag z.1 z.2))) :=
  (hPowerReal5Code.mul hSImagCode)
private theorem hAst195DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst195Denominator=true := by kernel_decide
private theorem hAst195DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst195Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst195Denominator hAst195DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst195Cross : equalCheck
    (mul hAst195Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst195Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst195Numerator) hAst195Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst195Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 5)*(Source.multiplierImag z.1 z.2))) :=
  hAst195Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst195Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst195Denominator)
    hAst195DenNonzero hAst195Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst196Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-3,0,4,0,-2,0,4,0,-3],[0],[0,0,0,0,2,0,4,0,4,0,4,0,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst196Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst196Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 5)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 5)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst194Code.add hAst195Code)
private theorem hAst196DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst196Denominator=true := by kernel_decide
private theorem hAst196DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst196Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst196Denominator hAst196DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst196Cross : equalCheck
    (mul hAst196Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst196Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst196Numerator) hAst196Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst196Code : RationalCode Source.domain (fun z => (((Source.powerImag z.1 5)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 5)*(Source.multiplierImag z.1 z.2)))) :=
  hAst196Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst196Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst196Denominator)
    hAst196DenNonzero hAst196Cross

/-- Article: proposed exact numerator for hGradientImag5. -/
def hGradientImag5Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-3,0,4,0,-2,0,4,0,-3],[0],[0,0,0,0,2,0,4,0,4,0,4,0,2]]
/-- Article: proposed positive denominator for hGradientImag5. -/
def hGradientImag5Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientImag5Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 5)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 5)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst196Code.congr (by
    intro z hz
    ring))
private theorem hGradientImag5Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerImag z.1 5)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 5)*(Source.multiplierImag z.1 z.2)))=Source.gradientImag z.1 z.2 5 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientImag]; ring
private theorem hGradientImag5DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientImag5Denominator=true := by kernel_decide
private theorem hGradientImag5DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag5Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientImag5Denominator hGradientImag5DenCheck hz.1 hz.2).ne'
private theorem hGradientImag5Cross : equalCheck
    (mul hGradientImag5Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag5Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag5Numerator) hGradientImag5Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientImag5. -/
def hGradientImag5Code : RationalCode Source.domain (fun z => Source.gradientImag z.1 z.2 5) :=
  (hGradientImag5Raw.congr hGradientImag5Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag5Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag5Denominator)
    hGradientImag5DenNonzero hGradientImag5Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst197Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,12,0,9,0,24,0,9,0,12,0,-1],[0],[-2,0,-11,0,-24,0,-32,0,-29,0,-19,0,-10,0,-2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst197Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst197Raw : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  (hGradientReal5Code.add hAst009Code)
private theorem hAst197DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst197Denominator=true := by kernel_decide
private theorem hAst197DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst197Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst197Denominator hAst197DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst197Cross : equalCheck
    (mul hAst197Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst197Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst197Numerator) hAst197Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst197Code : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  hAst197Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst197Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst197Denominator)
    hAst197DenNonzero hAst197Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst198Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,5,0,9,0,22,0,14,0,25,0,9,0,12,0,-1],[0],[-1,0,-6,0,-14,0,-22,0,-24,0,-18,0,-10,0,-2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst198Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst198Raw : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  (hAst197Code.add hAst010Code)
private theorem hAst198DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst198Denominator=true := by kernel_decide
private theorem hAst198DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst198Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst198Denominator hAst198DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst198Cross : equalCheck
    (mul hAst198Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst198Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst198Numerator) hAst198Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst198Code : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  hAst198Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst198Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst198Denominator)
    hAst198DenNonzero hAst198Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst199Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,10,0,43,0,134,0,329,0,586,0,1004,0,1180,0,1576,0,1302,0,1387,0,742,0,653,0,166,0,126,0,-24,0,1],[0],[0,0,-2,0,-22,0,-106,0,-336,0,-812,0,-1506,0,-2310,0,-2932,0,-3156,0,-2890,0,-2182,0,-1368,0,-636,0,-190,0,-10,0,28,0,-2],[0],[1,0,12,0,64,0,212,0,508,0,940,0,1392,0,1684,0,1670,0,1348,0,864,0,412,0,124,0,4,0,-16,0,-4,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst199Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,48,0,264,0,880,0,1980,0,3168,0,3696,0,3168,0,1980,0,880,0,264,0,48,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst199Raw : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  (hAst198Code.pow 2)
private theorem hAst199DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst199Denominator=true := by kernel_decide
private theorem hAst199DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst199Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst199Denominator hAst199DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst199Cross : equalCheck
    (mul hAst199Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst199Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst199Numerator) hAst199Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst199Code : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  hAst199Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst199Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst199Denominator)
    hAst199DenNonzero hAst199Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst200Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-10,0,-43,0,-134,0,-329,0,-586,0,-1004,0,-1180,0,-1576,0,-1302,0,-1387,0,-742,0,-653,0,-166,0,-126,0,24,0,-1],[0],[0,0,2,0,22,0,106,0,336,0,812,0,1506,0,2310,0,2932,0,3156,0,2890,0,2182,0,1368,0,636,0,190,0,10,0,-28,0,2],[0],[-1,0,-12,0,-64,0,-212,0,-508,0,-940,0,-1392,0,-1684,0,-1670,0,-1348,0,-864,0,-412,0,-124,0,-4,0,16,0,4,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst200Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,192,0,1056,0,3520,0,7920,0,12672,0,14784,0,12672,0,7920,0,3520,0,1056,0,192,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst200Raw : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  ((RationalCode.constant Source.domain (-1/4)).mul hAst199Code)
private theorem hAst200DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst200Denominator=true := by kernel_decide
private theorem hAst200DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst200Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst200Denominator hAst200DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst200Cross : equalCheck
    (mul hAst200Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst200Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst200Numerator) hAst200Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst200Code : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  hAst200Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst200Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst200Denominator)
    hAst200DenNonzero hAst200Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst201Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-5,0,-10,0,-15,0,-5,0,-7,0,0,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst201Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst201Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5))) :=
  ((RationalCode.constant Source.domain (-1)).add hPowerReal5Code)
private theorem hAst201DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst201Denominator=true := by kernel_decide
private theorem hAst201DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst201Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst201Denominator hAst201DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst201Cross : equalCheck
    (mul hAst201Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst201Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst201Numerator) hAst201Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst201Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5))) :=
  hAst201Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst201Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst201Denominator)
    hAst201DenNonzero hAst201Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst202Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,10,0,45,0,130,0,260,0,364,0,395,0,300,0,285,0,170,0,199,0,50,0,70,0,0,0,25]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst202Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,10,0,45,0,120,0,210,0,252,0,210,0,120,0,45,0,10,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst202Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2) :=
  (hAst201Code.pow 2)
private theorem hAst202DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst202Denominator=true := by kernel_decide
private theorem hAst202DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst202Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst202Denominator hAst202DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst202Cross : equalCheck
    (mul hAst202Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst202Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst202Numerator) hAst202Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst202Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2) :=
  hAst202Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst202Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst202Denominator)
    hAst202DenNonzero hAst202Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst203Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,10,0,45,0,130,0,260,0,364,0,395,0,300,0,285,0,170,0,199,0,50,0,70,0,0,0,25]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst203Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,40,0,180,0,480,0,840,0,1008,0,840,0,480,0,180,0,40,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst203Raw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2)) :=
  ((RationalCode.constant Source.domain (1/4)).mul hAst202Code)
private theorem hAst203DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst203Denominator=true := by kernel_decide
private theorem hAst203DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst203Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst203Denominator hAst203DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst203Cross : equalCheck
    (mul hAst203Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst203Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst203Numerator) hAst203Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst203Code : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2)) :=
  hAst203Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst203Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst203Denominator)
    hAst203DenNonzero hAst203Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst204Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,-6,0,8,0,-4,0,8,0,-6],[0],[-1,0,-5,0,-10,0,-6,0,3,0,7,0,8,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst204Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst204Raw : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  (hGradientImag5Code.add hAst018Code)
private theorem hAst204DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst204Denominator=true := by kernel_decide
private theorem hAst204DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst204Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst204Denominator hAst204DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst204Cross : equalCheck
    (mul hAst204Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst204Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst204Numerator) hAst204Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst204Code : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  hAst204Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst204Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst204Denominator)
    hAst204DenNonzero hAst204Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst205Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-5,0,-10,0,-16,0,3,0,-5,0,8,0,-6],[0],[0,0,0,0,4,0,8,0,8,0,8,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst205Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst205Raw : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst204Code.add hAst019Code)
private theorem hAst205DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst205Denominator=true := by kernel_decide
private theorem hAst205DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst205Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst205Denominator hAst205DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst205Cross : equalCheck
    (mul hAst205Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst205Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst205Numerator) hAst205Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst205Code : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  hAst205Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst205Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst205Denominator)
    hAst205DenNonzero hAst205Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst206Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,10,0,45,0,132,0,254,0,300,0,230,0,-64,0,69,0,-166,0,265,0,-116,0,124,0,-96,0,36],[0],[0,0,0,0,-8,0,-56,0,-176,0,-384,0,-480,0,-448,0,-304,0,-80,0,-24,0,-8,0,-32,0,-48],[0],[0,0,0,0,0,0,0,0,16,0,64,0,128,0,192,0,224,0,192,0,128,0,64,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst206Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,40,0,180,0,480,0,840,0,1008,0,840,0,480,0,180,0,40,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst206Raw : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  (hAst205Code.pow 2)
private theorem hAst206DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst206Denominator=true := by kernel_decide
private theorem hAst206DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst206Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst206Denominator hAst206DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst206Cross : equalCheck
    (mul hAst206Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst206Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst206Numerator) hAst206Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst206Code : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  hAst206Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst206Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst206Denominator)
    hAst206DenNonzero hAst206Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst207Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-11,0,-56,0,-187,0,-431,0,-686,0,-784,0,-466,0,-235,0,161,0,-168,0,17,0,-273,0,88,0,-64,0,60,0,-36],[0],[0,0,0,0,0,0,8,0,64,0,240,0,616,0,1040,0,1312,0,1232,0,832,0,408,0,112,0,64,0,88,0,80,0,48],[0],[0,0,0,0,0,0,0,0,0,0,-16,0,-80,0,-208,0,-384,0,-544,0,-608,0,-544,0,-384,0,-208,0,-80,0,-16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst207Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,192,0,1056,0,3520,0,7920,0,12672,0,14784,0,12672,0,7920,0,3520,0,1056,0,192,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst207Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  (hAst023Code.mul hAst206Code)
private theorem hAst207DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst207Denominator=true := by kernel_decide
private theorem hAst207DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst207Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst207Denominator hAst207DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst207Cross : equalCheck
    (mul hAst207Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst207Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst207Numerator) hAst207Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst207Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  hAst207Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst207Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst207Denominator)
    hAst207DenNonzero hAst207Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst208Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-16,0,60,0,16,0,134,0,16,0,60,0,-16,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst208Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst208Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 5))^2) :=
  (hPowerImag5Code.pow 2)
private theorem hAst208DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst208Denominator=true := by kernel_decide
private theorem hAst208DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst208Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst208Denominator hAst208DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst208Cross : equalCheck
    (mul hAst208Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst208Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst208Numerator) hAst208Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst208Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 5))^2) :=
  hAst208Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst208Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst208Denominator)
    hAst208DenNonzero hAst208Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst209Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,1,0,-15,0,45,0,60,0,210,0,166,0,210,0,60,0,45,0,-15,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst209Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,40,0,180,0,480,0,840,0,1008,0,840,0,480,0,180,0,40,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst209Raw : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 5))^2)) :=
  (hAst026Code.mul hAst208Code)
private theorem hAst209DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst209Denominator=true := by kernel_decide
private theorem hAst209DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst209Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst209Denominator hAst209DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst209Cross : equalCheck
    (mul hAst209Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst209Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst209Numerator) hAst209Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst209Code : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 5))^2)) :=
  hAst209Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst209Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst209Denominator)
    hAst209DenNonzero hAst209Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst210Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-10,0,-43,0,-134,0,-329,0,-586,0,-1004,0,-1180,0,-1576,0,-1302,0,-1387,0,-742,0,-653,0,-166,0,-126,0,24,0,-1],[0],[4,0,50,0,286,0,1026,0,2596,0,4868,0,7038,0,8126,0,8052,0,7316,0,6186,0,4654,0,2844,0,1396,0,570,0,210,0,72,0,2],[0],[-1,0,-12,0,-64,0,-212,0,-508,0,-940,0,-1392,0,-1684,0,-1670,0,-1348,0,-864,0,-412,0,-124,0,-4,0,16,0,4,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst210Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,192,0,1056,0,3520,0,7920,0,12672,0,14784,0,12672,0,7920,0,3520,0,1056,0,192,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst210Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2))) :=
  (hAst200Code.add hAst203Code)
private theorem hAst210DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst210Denominator=true := by kernel_decide
private theorem hAst210DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst210Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst210Denominator hAst210DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst210Cross : equalCheck
    (mul hAst210Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst210Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst210Numerator) hAst210Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst210Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2))) :=
  hAst210Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst210Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst210Denominator)
    hAst210DenNonzero hAst210Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst211Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-130,0,-260,0,-365,0,-380,0,-345,0,-345,0,-380,0,-365,0,-260,0,-130,0,-45,0,-10,0,-1],[0],[4,0,42,0,198,0,596,0,1270,0,1972,0,2440,0,2314,0,2296,0,1642,0,1438,0,544,0,430,0,56,0,116,0,2],[0],[-1,0,-10,0,-43,0,-116,0,-233,0,-374,0,-491,0,-536,0,-491,0,-374,0,-233,0,-116,0,-43,0,-10,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst211Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst211Raw : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  (hAst210Code.add hAst207Code)
private theorem hAst211DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst211Denominator=true := by kernel_decide
private theorem hAst211DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst211Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst211Denominator hAst211DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst211Cross : equalCheck
    (mul hAst211Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst211Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst211Numerator) hAst211Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst211Code : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  hAst211Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst211Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst211Denominator)
    hAst211DenNonzero hAst211Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst212Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0],[4,0,26,0,70,0,144,0,166,0,142,0,170,0,154,0,166,0,72,0,32,0,6],[0],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst212Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst212Raw : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 5))^2))) :=
  (hAst211Code.add hAst209Code)
private theorem hAst212DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst212Denominator=true := by kernel_decide
private theorem hAst212DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst212Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst212Denominator hAst212DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst212Cross : equalCheck
    (mul hAst212Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst212Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst212Numerator) hAst212Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst212Code : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 5))^2))) :=
  hAst212Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst212Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst212Denominator)
    hAst212DenNonzero hAst212Cross

/-- Article: proposed exact numerator for hRadius5. -/
def hRadius5Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0],[4,0,26,0,70,0,144,0,166,0,142,0,170,0,154,0,166,0,72,0,32,0,6],[0],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1]]
/-- Article: proposed positive denominator for hRadius5. -/
def hRadius5Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hRadius5Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 5))^2))) :=
  (hAst212Code.congr (by
    intro z hz
    ring))
private theorem hRadius5Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 5)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 5))^2))=Source.radius z.1 z.2 5 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.radius]; ring
private theorem hRadius5DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hRadius5Denominator=true := by kernel_decide
private theorem hRadius5DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hRadius5Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hRadius5Denominator hRadius5DenCheck hz.1 hz.2).ne'
private theorem hRadius5Cross : equalCheck
    (mul hRadius5Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hRadius5Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hRadius5Numerator) hRadius5Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hRadius5. -/
def hRadius5Code : RationalCode Source.domain (fun z => Source.radius z.1 z.2 5) :=
  (hRadius5Raw.congr hRadius5Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius5Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius5Denominator)
    hRadius5DenNonzero hRadius5Cross

end
end polyak.Certificates.Startup.Codes
