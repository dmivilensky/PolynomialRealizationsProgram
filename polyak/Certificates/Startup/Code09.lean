import polyak.Certificates.Startup.Code08

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: canonical numerator for one arithmetic source node. -/
def hAst213Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst213Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst213Raw : RationalCode Source.domain (fun z => (z.1)^10) :=
  ((RationalCode.first Source.domain).pow 10)
private theorem hAst213DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst213Denominator=true := by kernel_decide
private theorem hAst213DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst213Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst213Denominator hAst213DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst213Cross : equalCheck
    (mul hAst213Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst213Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst213Numerator) hAst213Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst213Code : RationalCode Source.domain (fun z => (z.1)^10) :=
  hAst213Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst213Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst213Denominator)
    hAst213DenNonzero hAst213Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst214Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst214Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst214Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^10)) :=
  ((RationalCode.constant Source.domain (-1)).add hAst213Code)
private theorem hAst214DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst214Denominator=true := by kernel_decide
private theorem hAst214DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst214Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst214Denominator hAst214DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst214Cross : equalCheck
    (mul hAst214Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst214Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst214Numerator) hAst214Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst214Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^10)) :=
  hAst214Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst214Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst214Denominator)
    hAst214DenNonzero hAst214Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst215Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,2,0,1,0,0,0,0,0,-1,0,-2,0,-1],[0,2,-2,0,2,-2,0,0,0,0,0,-2,2,0,-2,2],[1,0,2,0,1,0,0,0,0,0,-1,0,-2,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst215Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst215Raw : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^10))) :=
  (hValueCode.mul hAst214Code)
private theorem hAst215DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst215Denominator=true := by kernel_decide
private theorem hAst215DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst215Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst215Denominator hAst215DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst215Cross : equalCheck
    (mul hAst215Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst215Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst215Numerator) hAst215Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst215Code : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^10))) :=
  hAst215Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst215Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst215Denominator)
    hAst215DenNonzero hAst215Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst216Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,12,0,9,0,24,0,9,0,12,0,-1],[0],[2,0,11,0,26,0,28,0,11,0,-5,0,-8,0,-2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst216Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst216Raw : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5))) :=
  (hDRealCode.add hGradientReal5Code)
private theorem hAst216DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst216Denominator=true := by kernel_decide
private theorem hAst216DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst216Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst216Denominator hAst216DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst216Cross : equalCheck
    (mul hAst216Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst216Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst216Numerator) hAst216Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst216Code : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5))) :=
  hAst216Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst216Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst216Denominator)
    hAst216DenNonzero hAst216Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst217Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-11,0,2,0,4,0,23,0,9,0,12,0,-1],[0],[1,0,6,0,16,0,18,0,6,0,-6,0,-8,0,-2,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst217Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst217Raw : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5))+(Source.multiplierReal z.1 z.2))) :=
  (hAst216Code.add hSRealCode)
private theorem hAst217DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst217Denominator=true := by kernel_decide
private theorem hAst217DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst217Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst217Denominator hAst217DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst217Cross : equalCheck
    (mul hAst217Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst217Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst217Numerator) hAst217Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst217Code : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5))+(Source.multiplierReal z.1 z.2))) :=
  hAst217Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst217Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst217Denominator)
    hAst217DenNonzero hAst217Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst218Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,15,0,5,0,7,0,0,0,5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst218Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst218Raw : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))) :=
  ((RationalCode.constant Source.domain (-1/2)).mul hAst201Code)
private theorem hAst218DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst218Denominator=true := by kernel_decide
private theorem hAst218DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst218Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst218Denominator hAst218DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst218Cross : equalCheck
    (mul hAst218Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst218Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst218Numerator) hAst218Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst218Code : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))) :=
  hAst218Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst218Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst218Denominator)
    hAst218DenNonzero hAst218Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst219Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-46,0,-118,0,-176,0,-134,0,104,0,275,0,503,0,338,0,386,0,128,0,194,0,38,0,60,0,-5],[0],[1,0,11,0,56,0,173,0,351,0,481,0,414,0,195,0,7,0,-43,0,-12,0,-21,0,-39,0,-33,0,-10,0,5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst219Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,44,0,220,0,660,0,1320,0,1848,0,1848,0,1320,0,660,0,220,0,44,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst219Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5))+(Source.multiplierReal z.1 z.2)))) :=
  (hAst218Code.mul hAst217Code)
private theorem hAst219DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst219Denominator=true := by kernel_decide
private theorem hAst219DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst219Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst219Denominator hAst219DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst219Cross : equalCheck
    (mul hAst219Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst219Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst219Numerator) hAst219Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst219Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5))+(Source.multiplierReal z.1 z.2)))) :=
  hAst219Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst219Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst219Denominator)
    hAst219DenNonzero hAst219Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst220Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,-6,0,8,0,-4,0,8,0,-6],[0],[1,0,5,0,10,0,14,0,13,0,9,0,8,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst220Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst220Raw : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 5))) :=
  (hDImagCode.add hGradientImag5Code)
private theorem hAst220DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst220Denominator=true := by kernel_decide
private theorem hAst220DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst220Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst220Denominator hAst220DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst220Cross : equalCheck
    (mul hAst220Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst220Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst220Numerator) hAst220Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst220Code : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 5))) :=
  hAst220Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst220Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst220Denominator)
    hAst220DenNonzero hAst220Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst221Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,4,0,13,0,-3,0,8,0,-6],[0],[0,0,0,0,4,0,8,0,8,0,8,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst221Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,10,0,20,0,20,0,10,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst221Raw : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 5))+(Source.multiplierImag z.1 z.2))) :=
  (hAst220Code.add hSImagCode)
private theorem hAst221DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst221Denominator=true := by kernel_decide
private theorem hAst221DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst221Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst221Denominator hAst221DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst221Cross : equalCheck
    (mul hAst221Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst221Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst221Numerator) hAst221Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst221Code : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 5))+(Source.multiplierImag z.1 z.2))) :=
  hAst221Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst221Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst221Denominator)
    hAst221DenNonzero hAst221Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst222Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,7,0,9,0,18,0,9,0,7,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst222Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst222Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))) :=
  (hAst040Code.mul hPowerImag5Code)
private theorem hAst222DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst222Denominator=true := by kernel_decide
private theorem hAst222DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst222Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst222Denominator hAst222DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst222Cross : equalCheck
    (mul hAst222Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst222Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst222Numerator) hAst222Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst222Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))) :=
  hAst222Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst222Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst222Denominator)
    hAst222DenNonzero hAst222Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst223Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,2,0,34,0,129,0,204,0,362,0,284,0,370,0,111,0,150,0,-70,0,5,0,-50,0,6],[0],[0,0,0,0,0,0,0,0,0,0,-4,0,20,0,84,0,192,0,304,0,344,0,304,0,192,0,84,0,20,0,-4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst223Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,44,0,220,0,660,0,1320,0,1848,0,1848,0,1320,0,660,0,220,0,44,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst223Raw : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 5))+(Source.multiplierImag z.1 z.2)))) :=
  (hAst222Code.mul hAst221Code)
private theorem hAst223DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst223Denominator=true := by kernel_decide
private theorem hAst223DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst223Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst223Denominator hAst223DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst223Cross : equalCheck
    (mul hAst223Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst223Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst223Numerator) hAst223Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst223Code : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 5))+(Source.multiplierImag z.1 z.2)))) :=
  hAst223Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst223Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst223Denominator)
    hAst223DenNonzero hAst223Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst224Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,2,0,34,0,117,0,304,0,350,0,428,0,138,0,135,0,-82,0,74,0,-7,0,50,0,-6],[0,2,-2,16,-14,54,-40,96,-56,84,-28,-2,30,-100,70,-150,80,-150,70,-100,30,-2,-28,84,-56,96,-40,54,-14,16,-2,2],[2,0,21,0,101,0,293,0,561,0,732,0,614,0,270,0,-68,0,-243,0,-263,0,-231,0,-159,0,-78,0,-20,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst224Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,44,0,220,0,660,0,1320,0,1848,0,1848,0,1320,0,660,0,220,0,44,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst224Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^10))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5))+(Source.multiplierReal z.1 z.2))))) :=
  (hAst215Code.add hAst219Code)
private theorem hAst224DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst224Denominator=true := by kernel_decide
private theorem hAst224DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst224Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst224Denominator hAst224DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst224Cross : equalCheck
    (mul hAst224Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst224Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst224Numerator) hAst224Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst224Code : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^10))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5))+(Source.multiplierReal z.1 z.2))))) :=
  hAst224Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst224Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst224Denominator)
    hAst224DenNonzero hAst224Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst225Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-2,0,14,0,18,0,36,0,18,0,14,0,-2],[0,2,-2,6,-4,4,0,-4,4,-6,2,-4,2,-6,4,-4,0,4,-4,6,-2,2],[2,0,11,0,26,0,33,0,16,0,1,0,-2,0,3,0,6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst225Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,24,0,60,0,80,0,60,0,24,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst225Raw : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^10))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 5))+(Source.multiplierImag z.1 z.2))))) :=
  (hAst224Code.add hAst223Code)
private theorem hAst225DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst225Denominator=true := by kernel_decide
private theorem hAst225DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst225Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst225Denominator hAst225DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst225Cross : equalCheck
    (mul hAst225Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst225Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst225Numerator) hAst225Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst225Code : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^10))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 5))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 5))+(Source.multiplierImag z.1 z.2))))) :=
  hAst225Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst225Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst225Denominator)
    hAst225DenNonzero hAst225Cross

/-- Article: proposed exact numerator for hDiscrepancy5. -/
def hDiscrepancy5Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-2,0,14,0,18,0,36,0,18,0,14,0,-2],[0,2,-2,6,-4,4,0,-4,4,-6,2,-4,2,-6,4,-4,0,4,-4,6,-2,2],[2,0,11,0,26,0,33,0,16,0,1,0,-2,0,3,0,6]]
/-- Article: proposed positive denominator for hDiscrepancy5. -/
def hDiscrepancy5Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,24,0,60,0,80,0,60,0,24,0,4]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDiscrepancy5Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^10))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 5)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 5)+(Source.multiplierImag z.1 z.2))))) :=
  (hAst225Code.congr (by
    intro z hz
    ring))
private theorem hDiscrepancy5Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^10))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 5))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 5)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 5)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 5)+(Source.multiplierImag z.1 z.2))))=Source.discrepancy z.1 z.2 5 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.discrepancy]; ring
private theorem hDiscrepancy5DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDiscrepancy5Denominator=true := by kernel_decide
private theorem hDiscrepancy5DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy5Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDiscrepancy5Denominator hDiscrepancy5DenCheck hz.1 hz.2).ne'
private theorem hDiscrepancy5Cross : equalCheck
    (mul hDiscrepancy5Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy5Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy5Numerator) hDiscrepancy5Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDiscrepancy5. -/
def hDiscrepancy5Code : RationalCode Source.domain (fun z => Source.discrepancy z.1 z.2 5) :=
  (hDiscrepancy5Raw.congr hDiscrepancy5Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy5Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy5Denominator)
    hDiscrepancy5DenNonzero hDiscrepancy5Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst226Numerator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[0],[0],[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst226Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst226Raw : RationalCode Source.domain (fun z => (z.2)^6) :=
  ((RationalCode.second Source.domain).pow 6)
private theorem hAst226DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst226Denominator=true := by kernel_decide
private theorem hAst226DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst226Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst226Denominator hAst226DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst226Cross : equalCheck
    (mul hAst226Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst226Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst226Numerator) hAst226Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst226Code : RationalCode Source.domain (fun z => (z.2)^6) :=
  hAst226Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst226Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst226Denominator)
    hAst226DenNonzero hAst226Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst227Numerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[0],[0],[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst227Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst227Raw : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+(z.2)^6)) :=
  ((RationalCode.constant Source.domain 1).add hAst226Code)
private theorem hAst227DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst227Denominator=true := by kernel_decide
private theorem hAst227DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst227Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst227Denominator hAst227DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst227Cross : equalCheck
    (mul hAst227Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst227Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst227Numerator) hAst227Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst227Code : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+(z.2)^6)) :=
  hAst227Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst227Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst227Denominator)
    hAst227DenNonzero hAst227Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst228Numerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[0],[0],[0],[0],[2],[0],[0],[0],[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst228Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst228Raw : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+(z.2)^6))^2) :=
  (hAst227Code.pow 2)
private theorem hAst228DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst228Denominator=true := by kernel_decide
private theorem hAst228DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst228Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst228Denominator hAst228DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst228Cross : equalCheck
    (mul hAst228Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst228Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst228Numerator) hAst228Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst228Code : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+(z.2)^6))^2) :=
  hAst228Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst228Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst228Denominator)
    hAst228DenNonzero hAst228Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst229Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,2,0,-14,0,-18,0,-36,0,-18,0,-14,0,2],[0,-2,2,-6,4,-4,0,4,-4,6,-2,4,-2,6,-4,4,0,-4,4,-6,2,-2],[-2,0,-11,0,-26,0,-33,0,-16,0,-1,0,2,0,-3,0,-6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst229Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,24,0,60,0,80,0,60,0,24,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst229Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 5))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDiscrepancy5Code)
private theorem hAst229DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst229Denominator=true := by kernel_decide
private theorem hAst229DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst229Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst229Denominator hAst229DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst229Cross : equalCheck
    (mul hAst229Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst229Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst229Numerator) hAst229Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst229Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 5))) :=
  hAst229Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst229Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst229Denominator)
    hAst229DenNonzero hAst229Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst230Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0],[20,0,122,0,310,0,464,0,406,0,238,0,186,0,154,0,166,0,72,0,32,0,6],[0],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1],[0],[0],[0],[32,0,192,0,480,0,640,0,480,0,192,0,32],[0],[0],[0],[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst230Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst230Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 5)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)) :=
  (hRadius5Code.add hAst228Code)
private theorem hAst230DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst230Denominator=true := by kernel_decide
private theorem hAst230DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst230Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst230Denominator hAst230DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst230Cross : equalCheck
    (mul hAst230Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst230Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst230Numerator) hAst230Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst230Code : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 5)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)) :=
  hAst230Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst230Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst230Denominator)
    hAst230DenNonzero hAst230Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst231Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0,0,0,0,0,0,8,0,-56,0,-72,0,-144,0,-72,0,-56,0,8],[20,-8,130,-24,326,-16,464,16,390,24,230,16,178,24,138,16,166,-16,88,-24,40,-8,6],[-8,0,-44,0,-104,0,-132,0,-64,0,-4,0,8,0,-12,0,-24],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1],[0],[0],[0],[32,0,192,0,480,0,640,0,480,0,192,0,32],[0],[0],[0],[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst231Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst231Raw : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 5)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 5)))) :=
  (hAst230Code.add hAst229Code)
private theorem hAst231DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst231Denominator=true := by kernel_decide
private theorem hAst231DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst231Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst231Denominator hAst231DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst231Cross : equalCheck
    (mul hAst231Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst231Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst231Numerator) hAst231Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst231Code : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 5)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 5)))) :=
  hAst231Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst231Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst231Denominator)
    hAst231DenNonzero hAst231Cross

/-- Article: proposed exact numerator for hPairLower5. -/
def hPairLower5Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0,0,0,0,0,0,8,0,-56,0,-72,0,-144,0,-72,0,-56,0,8],[20,-8,130,-24,326,-16,464,16,390,24,230,16,178,24,138,16,166,-16,88,-24,40,-8,6],[-8,0,-44,0,-104,0,-132,0,-64,0,-4,0,8,0,-12,0,-24],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1],[0],[0],[0],[32,0,192,0,480,0,640,0,480,0,192,0,32],[0],[0],[0],[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: proposed positive denominator for hPairLower5. -/
def hPairLower5Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairLower5Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 5)+((((1 : ℚ) : ℝ)+(z.2)^6))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 5)))) :=
  (hAst231Code.congr (by
    intro z hz
    ring))
private theorem hPairLower5Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.radius z.1 z.2 5)+((((1 : ℚ) : ℝ)+(z.2)^6))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 5)))=Source.pairSlack z.1 z.2 (-1) 5 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairLower5DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairLower5Denominator=true := by kernel_decide
private theorem hPairLower5DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairLower5Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairLower5Denominator hPairLower5DenCheck hz.1 hz.2).ne'
private theorem hPairLower5Cross : equalCheck
    (mul hPairLower5Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairLower5Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairLower5Numerator) hPairLower5Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairLower5. -/
def hPairLower5Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (-1) 5) :=
  (hPairLower5Raw.congr hPairLower5Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower5Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower5Denominator)
    hPairLower5DenNonzero hPairLower5Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst232Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0,0,0,0,0,0,-8,0,56,0,72,0,144,0,72,0,56,0,-8],[4,8,18,24,54,16,144,-16,182,-24,150,-16,178,-24,170,-16,166,16,56,24,24,8,6],[8,0,44,0,104,0,132,0,64,0,4,0,-8,0,12,0,24],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst232Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst232Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 5)+(Source.radius z.1 z.2 5))) :=
  (hDiscrepancy5Code.add hRadius5Code)
private theorem hAst232DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst232Denominator=true := by kernel_decide
private theorem hAst232DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst232Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst232Denominator hAst232DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst232Cross : equalCheck
    (mul hAst232Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst232Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst232Numerator) hAst232Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst232Code : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 5)+(Source.radius z.1 z.2 5))) :=
  hAst232Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst232Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst232Denominator)
    hAst232DenNonzero hAst232Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst233Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0,0,0,0,0,0,-8,0,56,0,72,0,144,0,72,0,56,0,-8],[20,8,114,24,294,16,464,-16,422,-24,246,-16,194,-24,170,-16,166,16,56,24,24,8,6],[8,0,44,0,104,0,132,0,64,0,4,0,-8,0,12,0,24],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1],[0],[0],[0],[32,0,192,0,480,0,640,0,480,0,192,0,32],[0],[0],[0],[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst233Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst233Raw : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 5)+(Source.radius z.1 z.2 5))+((((1 : ℚ) : ℝ)+(z.2)^6))^2)) :=
  (hAst232Code.add hAst228Code)
private theorem hAst233DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst233Denominator=true := by kernel_decide
private theorem hAst233DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst233Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst233Denominator hAst233DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst233Cross : equalCheck
    (mul hAst233Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst233Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst233Numerator) hAst233Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst233Code : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 5)+(Source.radius z.1 z.2 5))+((((1 : ℚ) : ℝ)+(z.2)^6))^2)) :=
  hAst233Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst233Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst233Denominator)
    hAst233DenNonzero hAst233Cross

/-- Article: proposed exact numerator for hPairUpper5. -/
def hPairUpper5Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0,0,0,0,0,0,-8,0,56,0,72,0,144,0,72,0,56,0,-8],[20,8,114,24,294,16,464,-16,422,-24,246,-16,194,-24,170,-16,166,16,56,24,24,8,6],[8,0,44,0,104,0,132,0,64,0,4,0,-8,0,12,0,24],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1],[0],[0],[0],[32,0,192,0,480,0,640,0,480,0,192,0,32],[0],[0],[0],[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: proposed positive denominator for hPairUpper5. -/
def hPairUpper5Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairUpper5Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 5)+(Source.radius z.1 z.2 5)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)) :=
  (hAst233Code.congr (by
    intro z hz
    ring))
private theorem hPairUpper5Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.discrepancy z.1 z.2 5)+(Source.radius z.1 z.2 5)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)=Source.pairSlack z.1 z.2 (1) 5 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairUpper5DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairUpper5Denominator=true := by kernel_decide
private theorem hPairUpper5DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper5Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairUpper5Denominator hPairUpper5DenCheck hz.1 hz.2).ne'
private theorem hPairUpper5Cross : equalCheck
    (mul hPairUpper5Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper5Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper5Numerator) hPairUpper5Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairUpper5. -/
def hPairUpper5Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (1) 5) :=
  (hPairUpper5Raw.congr hPairUpper5Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper5Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper5Denominator)
    hPairUpper5DenNonzero hPairUpper5Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst234Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,12,0,9,0,24,0,9,0,12,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst234Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst234Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 6 (radialCosine z.1))*(z.1)^6)) :=
  (hT6Code.mul hAst122Code)
private theorem hAst234DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst234Denominator=true := by kernel_decide
private theorem hAst234DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst234Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst234Denominator hAst234DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst234Cross : equalCheck
    (mul hAst234Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst234Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst234Numerator) hAst234Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst234Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 6 (radialCosine z.1))*(z.1)^6)) :=
  hAst234Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst234Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst234Denominator)
    hAst234DenNonzero hAst234Cross

/-- Article: proposed exact numerator for hPowerReal6. -/
def hPowerReal6Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,12,0,9,0,24,0,9,0,12,0,-1]]
/-- Article: proposed positive denominator for hPowerReal6. -/
def hPowerReal6Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerReal6Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 6 (radialCosine z.1))*(z.1)^6)) :=
  (hAst234Code.congr (by
    intro z hz
    ring))
private theorem hPowerReal6Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebT 6 (radialCosine z.1))*(z.1)^6)=Source.powerReal z.1 6 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.powerReal]; ring
private theorem hPowerReal6DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerReal6Denominator=true := by kernel_decide
private theorem hPowerReal6DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal6Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerReal6Denominator hPowerReal6DenCheck hz.1 hz.2).ne'
private theorem hPowerReal6Cross : equalCheck
    (mul hPowerReal6Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal6Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal6Numerator) hPowerReal6Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerReal6. -/
def hPowerReal6Code : RationalCode Source.domain (fun z => Source.powerReal z.1 6) :=
  (hPowerReal6Raw.congr hPowerReal6Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal6Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal6Denominator)
    hPowerReal6DenNonzero hPowerReal6Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst235Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-6,0,8,0,-4,0,8,0,-6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst235Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst235Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 5 (radialCosine z.1))*(z.1)^5)) :=
  (hU5Code.mul hAst187Code)
private theorem hAst235DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst235Denominator=true := by kernel_decide
private theorem hAst235DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst235Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst235Denominator hAst235DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst235Cross : equalCheck
    (mul hAst235Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst235Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst235Numerator) hAst235Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst235Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 5 (radialCosine z.1))*(z.1)^5)) :=
  hAst235Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst235Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst235Denominator)
    hAst235DenNonzero hAst235Cross

/-- Article: proposed exact numerator for hPowerImag6. -/
def hPowerImag6Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-6,0,8,0,-4,0,8,0,-6]]
/-- Article: proposed positive denominator for hPowerImag6. -/
def hPowerImag6Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,5,0,10,0,10,0,5,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerImag6Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 5 (radialCosine z.1))*(z.1)^5)) :=
  (hAst235Code.congr (by
    intro z hz
    ring))
private theorem hPowerImag6Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebU 5 (radialCosine z.1))*(z.1)^5)=Source.powerImag z.1 6 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.powerImag,ite_eq_right (by decide)]; ring
private theorem hPowerImag6DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerImag6Denominator=true := by kernel_decide
private theorem hPowerImag6DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag6Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerImag6Denominator hPowerImag6DenCheck hz.1 hz.2).ne'
private theorem hPowerImag6Cross : equalCheck
    (mul hPowerImag6Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag6Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag6Numerator) hPowerImag6Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerImag6. -/
def hPowerImag6Code : RationalCode Source.domain (fun z => Source.powerImag z.1 6) :=
  (hPowerImag6Raw.congr hPowerImag6Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag6Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag6Denominator)
    hPowerImag6DenNonzero hPowerImag6Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst236Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-12,0,-9,0,-24,0,-9,0,-12,0,1],[0],[0,0,0,0,0,0,1,0,-12,0,-9,0,-24,0,-9,0,-12,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst236Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst236Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 6)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerReal6Code.mul hSRealCode)
private theorem hAst236DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst236Denominator=true := by kernel_decide
private theorem hAst236DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst236Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst236Denominator hAst236DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst236Cross : equalCheck
    (mul hAst236Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst236Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst236Numerator) hAst236Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst236Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 6)*(Source.multiplierReal z.1 z.2))) :=
  hAst236Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst236Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst236Denominator)
    hAst236DenNonzero hAst236Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst237Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,6,0,-2,0,2,0,-12,0,2,0,-2,0,6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst237Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst237Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))) :=
  (hAst002Code.mul hPowerImag6Code)
private theorem hAst237DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst237Denominator=true := by kernel_decide
private theorem hAst237DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst237Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst237Denominator hAst237DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst237Cross : equalCheck
    (mul hAst237Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst237Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst237Numerator) hAst237Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst237Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))) :=
  hAst237Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst237Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst237Denominator)
    hAst237DenNonzero hAst237Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst238Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,3,0,-1,0,1,0,-6,0,1,0,-1,0,3],[0],[0,0,0,0,0,0,-3,0,1,0,-1,0,6,0,-1,0,1,0,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst238Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst238Raw : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))*(Source.multiplierImag z.1 z.2))) :=
  (hAst237Code.mul hSImagCode)
private theorem hAst238DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst238Denominator=true := by kernel_decide
private theorem hAst238DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst238Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst238Denominator hAst238DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst238Cross : equalCheck
    (mul hAst238Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst238Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst238Numerator) hAst238Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst238Code : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))*(Source.multiplierImag z.1 z.2))) :=
  hAst238Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst238Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst238Denominator)
    hAst238DenNonzero hAst238Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst239Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,7,0,-14,0,-7,0,-36,0,-7,0,-14,0,7],[0],[0,0,0,0,0,0,-5,0,-10,0,-11,0,-12,0,-11,0,-10,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst239Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst239Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 6)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))*(Source.multiplierImag z.1 z.2)))) :=
  (hAst236Code.add hAst238Code)
private theorem hAst239DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst239Denominator=true := by kernel_decide
private theorem hAst239DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst239Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst239Denominator hAst239DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst239Cross : equalCheck
    (mul hAst239Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst239Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst239Numerator) hAst239Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst239Code : RationalCode Source.domain (fun z => (((Source.powerReal z.1 6)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))*(Source.multiplierImag z.1 z.2)))) :=
  hAst239Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst239Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst239Denominator)
    hAst239DenNonzero hAst239Cross

/-- Article: proposed exact numerator for hGradientReal6. -/
def hGradientReal6Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,7,0,-14,0,-7,0,-36,0,-7,0,-14,0,7],[0],[0,0,0,0,0,0,-5,0,-10,0,-11,0,-12,0,-11,0,-10,0,-5]]
/-- Article: proposed positive denominator for hGradientReal6. -/
def hGradientReal6Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientReal6Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 6)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 6)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst239Code.congr (by
    intro z hz
    ring))
private theorem hGradientReal6Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerReal z.1 6)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 6)*(Source.multiplierImag z.1 z.2)))=Source.gradientReal z.1 z.2 6 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientReal]; ring
private theorem hGradientReal6DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientReal6Denominator=true := by kernel_decide
private theorem hGradientReal6DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal6Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientReal6Denominator hGradientReal6DenCheck hz.1 hz.2).ne'
private theorem hGradientReal6Cross : equalCheck
    (mul hGradientReal6Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal6Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal6Numerator) hGradientReal6Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientReal6. -/
def hGradientReal6Code : RationalCode Source.domain (fun z => Source.gradientReal z.1 z.2 6) :=
  (hGradientReal6Raw.congr hGradientReal6Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal6Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal6Denominator)
    hGradientReal6DenNonzero hGradientReal6Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst240Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,3,0,-4,0,2,0,-4,0,3],[0],[0,0,0,0,0,0,3,0,-4,0,2,0,-4,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst240Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst240Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 6)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerImag6Code.mul hSRealCode)
private theorem hAst240DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst240Denominator=true := by kernel_decide
private theorem hAst240DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst240Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst240Denominator hAst240DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst240Cross : equalCheck
    (mul hAst240Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst240Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst240Numerator) hAst240Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst240Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 6)*(Source.multiplierReal z.1 z.2))) :=
  hAst240Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst240Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst240Denominator)
    hAst240DenNonzero hAst240Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst241Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,12,0,9,0,24,0,9,0,12,0,-1],[0],[0,0,0,0,1,0,-12,0,-9,0,-24,0,-9,0,-12,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst241Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst241Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 6)*(Source.multiplierImag z.1 z.2))) :=
  (hPowerReal6Code.mul hSImagCode)
private theorem hAst241DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst241Denominator=true := by kernel_decide
private theorem hAst241DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst241Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst241Denominator hAst241DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst241Cross : equalCheck
    (mul hAst241Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst241Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst241Numerator) hAst241Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst241Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 6)*(Source.multiplierImag z.1 z.2))) :=
  hAst241Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst241Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst241Denominator)
    hAst241DenNonzero hAst241Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst242Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,18,0,1,0,28,0,1,0,18,0,-1],[0],[0,0,0,0,1,0,-6,0,-17,0,-20,0,-17,0,-6,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst242Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst242Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 6)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 6)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst240Code.add hAst241Code)
private theorem hAst242DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst242Denominator=true := by kernel_decide
private theorem hAst242DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst242Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst242Denominator hAst242DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst242Cross : equalCheck
    (mul hAst242Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst242Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst242Numerator) hAst242Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst242Code : RationalCode Source.domain (fun z => (((Source.powerImag z.1 6)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 6)*(Source.multiplierImag z.1 z.2)))) :=
  hAst242Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst242Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst242Denominator)
    hAst242DenNonzero hAst242Cross

/-- Article: proposed exact numerator for hGradientImag6. -/
def hGradientImag6Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,18,0,1,0,28,0,1,0,18,0,-1],[0],[0,0,0,0,1,0,-6,0,-17,0,-20,0,-17,0,-6,0,1]]
/-- Article: proposed positive denominator for hGradientImag6. -/
def hGradientImag6Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientImag6Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 6)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 6)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst242Code.congr (by
    intro z hz
    ring))
private theorem hGradientImag6Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerImag z.1 6)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 6)*(Source.multiplierImag z.1 z.2)))=Source.gradientImag z.1 z.2 6 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientImag]; ring
private theorem hGradientImag6DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientImag6Denominator=true := by kernel_decide
private theorem hGradientImag6DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag6Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientImag6Denominator hGradientImag6DenCheck hz.1 hz.2).ne'
private theorem hGradientImag6Cross : equalCheck
    (mul hGradientImag6Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag6Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag6Numerator) hGradientImag6Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientImag6. -/
def hGradientImag6Code : RationalCode Source.domain (fun z => Source.gradientImag z.1 z.2 6) :=
  (hGradientImag6Raw.congr hGradientImag6Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag6Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag6Denominator)
    hGradientImag6DenNonzero hGradientImag6Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst243Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,7,0,-14,0,-7,0,-36,0,-7,0,-14,0,7],[0],[-2,0,-13,0,-36,0,-60,0,-60,0,-38,0,-20,0,-12,0,-10,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst243Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst243Raw : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  (hGradientReal6Code.add hAst009Code)
private theorem hAst243DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst243Denominator=true := by kernel_decide
private theorem hAst243DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst243Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst243Denominator hAst243DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst243Cross : equalCheck
    (mul hAst243Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst243Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst243Numerator) hAst243Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst243Code : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  hAst243Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst243Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst243Denominator)
    hAst243DenNonzero hAst243Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst244Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,6,0,15,0,27,0,1,0,-1,0,-35,0,-7,0,-14,0,7],[0],[-1,0,-7,0,-21,0,-40,0,-45,0,-32,0,-19,0,-12,0,-10,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst244Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst244Raw : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  (hAst243Code.add hAst010Code)
private theorem hAst244DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst244Denominator=true := by kernel_decide
private theorem hAst244DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst244Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst244Denominator hAst244DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst244Cross : equalCheck
    (mul hAst244Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst244Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst244Numerator) hAst244Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst244Code : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  hAst244Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst244Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst244Denominator)
    hAst244DenNonzero hAst244Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst245Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,12,0,66,0,234,0,551,0,820,0,677,0,-410,0,-1215,0,-2256,0,-783,0,-490,0,1589,0,532,0,1015,0,-294,0,98,0,-196,0,49],[0],[0,0,-2,0,-26,0,-156,0,-596,0,-1580,0,-2950,0,-3890,0,-3176,0,-876,0,1786,0,3218,0,3020,0,2212,0,1382,0,962,0,560,0,182,0,0,0,-70],[0],[1,0,14,0,91,0,374,0,1091,0,2374,0,3976,0,5234,0,5571,0,5054,0,4184,0,3306,0,2429,0,1546,0,844,0,430,0,220,0,100,0,25]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst245Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,56,0,364,0,1456,0,4004,0,8008,0,12012,0,13728,0,12012,0,8008,0,4004,0,1456,0,364,0,56,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst245Raw : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  (hAst244Code.pow 2)
private theorem hAst245DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst245Denominator=true := by kernel_decide
private theorem hAst245DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst245Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst245Denominator hAst245DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst245Cross : equalCheck
    (mul hAst245Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst245Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst245Numerator) hAst245Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst245Code : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  hAst245Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst245Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst245Denominator)
    hAst245DenNonzero hAst245Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst246Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-12,0,-66,0,-234,0,-551,0,-820,0,-677,0,410,0,1215,0,2256,0,783,0,490,0,-1589,0,-532,0,-1015,0,294,0,-98,0,196,0,-49],[0],[0,0,2,0,26,0,156,0,596,0,1580,0,2950,0,3890,0,3176,0,876,0,-1786,0,-3218,0,-3020,0,-2212,0,-1382,0,-962,0,-560,0,-182,0,0,0,70],[0],[-1,0,-14,0,-91,0,-374,0,-1091,0,-2374,0,-3976,0,-5234,0,-5571,0,-5054,0,-4184,0,-3306,0,-2429,0,-1546,0,-844,0,-430,0,-220,0,-100,0,-25]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst246Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,224,0,1456,0,5824,0,16016,0,32032,0,48048,0,54912,0,48048,0,32032,0,16016,0,5824,0,1456,0,224,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst246Raw : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  ((RationalCode.constant Source.domain (-1/4)).mul hAst245Code)
private theorem hAst246DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst246Denominator=true := by kernel_decide
private theorem hAst246DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst246Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst246Denominator hAst246DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst246Cross : equalCheck
    (mul hAst246Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst246Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst246Numerator) hAst246Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst246Code : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  hAst246Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst246Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst246Denominator)
    hAst246DenNonzero hAst246Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst247Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-6,0,-15,0,-21,0,-3,0,3,0,23,0,9,0,12,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst247Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst247Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6))) :=
  ((RationalCode.constant Source.domain (-1)).add hPowerReal6Code)
private theorem hAst247DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst247Denominator=true := by kernel_decide
private theorem hAst247DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst247Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst247Denominator hAst247DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst247Cross : equalCheck
    (mul hAst247Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst247Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst247Numerator) hAst247Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst247Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6))) :=
  hAst247Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst247Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst247Denominator)
    hAst247DenNonzero hAst247Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst248Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,12,0,66,0,222,0,483,0,660,0,449,0,-258,0,-939,0,-1396,0,-855,0,-390,0,553,0,492,0,627,0,170,0,126,0,-24,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst248Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,12,0,66,0,220,0,495,0,792,0,924,0,792,0,495,0,220,0,66,0,12,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst248Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2) :=
  (hAst247Code.pow 2)
private theorem hAst248DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst248Denominator=true := by kernel_decide
private theorem hAst248DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst248Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst248Denominator hAst248DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst248Cross : equalCheck
    (mul hAst248Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst248Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst248Numerator) hAst248Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst248Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2) :=
  hAst248Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst248Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst248Denominator)
    hAst248DenNonzero hAst248Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst249Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,12,0,66,0,222,0,483,0,660,0,449,0,-258,0,-939,0,-1396,0,-855,0,-390,0,553,0,492,0,627,0,170,0,126,0,-24,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst249Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,48,0,264,0,880,0,1980,0,3168,0,3696,0,3168,0,1980,0,880,0,264,0,48,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst249Raw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2)) :=
  ((RationalCode.constant Source.domain (1/4)).mul hAst248Code)
private theorem hAst249DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst249Denominator=true := by kernel_decide
private theorem hAst249DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst249Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst249Denominator hAst249DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst249Cross : equalCheck
    (mul hAst249Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst249Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst249Numerator) hAst249Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst249Code : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2)) :=
  hAst249Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst249Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst249Denominator)
    hAst249DenNonzero hAst249Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst250Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,-1,0,18,0,1,0,28,0,1,0,18,0,-1],[0],[-1,0,-6,0,-15,0,-19,0,-21,0,-23,0,-21,0,-17,0,-6,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst250Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst250Raw : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  (hGradientImag6Code.add hAst018Code)
private theorem hAst250DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst250Denominator=true := by kernel_decide
private theorem hAst250DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst250Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst250Denominator hAst250DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst250Cross : equalCheck
    (mul hAst250Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst250Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst250Numerator) hAst250Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst250Code : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  hAst250Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst250Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst250Denominator)
    hAst250DenNonzero hAst250Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst251Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-6,0,-15,0,-21,0,3,0,-5,0,27,0,1,0,18,0,-1],[0],[0,0,0,0,1,0,-6,0,-17,0,-20,0,-17,0,-6,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst251Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst251Raw : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst250Code.add hAst019Code)
private theorem hAst251DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst251Denominator=true := by kernel_decide
private theorem hAst251DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst251Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst251Denominator hAst251DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst251Cross : equalCheck
    (mul hAst251Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst251Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst251Numerator) hAst251Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst251Code : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  hAst251Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst251Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst251Denominator)
    hAst251DenNonzero hAst251Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst252Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,12,0,66,0,222,0,471,0,604,0,357,0,-302,0,-639,0,-1408,0,-383,0,-990,0,869,0,-132,0,983,0,-18,0,322,0,-36,0,1],[0],[0,0,0,0,-2,0,0,0,76,0,382,0,1042,0,1484,0,1432,0,610,0,-574,0,-1240,0,-1492,0,-1054,0,-530,0,-180,0,48,0,-2],[0],[0,0,0,0,0,0,0,0,1,0,-12,0,2,0,164,0,495,0,872,0,1052,0,872,0,495,0,164,0,2,0,-12,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst252Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,48,0,264,0,880,0,1980,0,3168,0,3696,0,3168,0,1980,0,880,0,264,0,48,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst252Raw : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  (hAst251Code.pow 2)
private theorem hAst252DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst252Denominator=true := by kernel_decide
private theorem hAst252DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst252Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst252Denominator hAst252DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst252Cross : equalCheck
    (mul hAst252Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst252Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst252Numerator) hAst252Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst252Code : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  hAst252Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst252Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst252Denominator)
    hAst252DenNonzero hAst252Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst253Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-13,0,-79,0,-300,0,-759,0,-1297,0,-1432,0,-659,0,584,0,2349,0,2430,0,2781,0,504,0,253,0,-1720,0,-833,0,-1287,0,-268,0,-287,0,35,0,-1],[0],[0,0,0,0,0,0,2,0,2,0,-74,0,-458,0,-1500,0,-2908,0,-3958,0,-3526,0,-1468,0,1204,0,3306,0,3786,0,3076,0,1764,0,662,0,134,0,-46,0,2],[0],[0,0,0,0,0,0,0,0,0,0,-1,0,11,0,9,0,-154,0,-661,0,-1531,0,-2419,0,-2796,0,-2419,0,-1531,0,-661,0,-154,0,9,0,11,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst253Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,224,0,1456,0,5824,0,16016,0,32032,0,48048,0,54912,0,48048,0,32032,0,16016,0,5824,0,1456,0,224,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst253Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  (hAst023Code.mul hAst252Code)
private theorem hAst253DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst253Denominator=true := by kernel_decide
private theorem hAst253DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst253Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst253Denominator hAst253DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst253Cross : equalCheck
    (mul hAst253Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst253Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst253Numerator) hAst253Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst253Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  hAst253Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst253Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst253Denominator)
    hAst253DenNonzero hAst253Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst254Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,36,0,-96,0,112,0,-160,0,216,0,-160,0,112,0,-96,0,36]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst254Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,10,0,45,0,120,0,210,0,252,0,210,0,120,0,45,0,10,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst254Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 6))^2) :=
  (hPowerImag6Code.pow 2)
private theorem hAst254DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst254Denominator=true := by kernel_decide
private theorem hAst254DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst254Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst254Denominator hAst254DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst254Cross : equalCheck
    (mul hAst254Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst254Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst254Numerator) hAst254Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst254Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 6))^2) :=
  hAst254Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst254Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst254Denominator)
    hAst254DenNonzero hAst254Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst255Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,0,-15,0,13,0,-36,0,42,0,-26,0,42,0,-36,0,13,0,-15,0,9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst255Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,12,0,66,0,220,0,495,0,792,0,924,0,792,0,495,0,220,0,66,0,12,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst255Raw : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 6))^2)) :=
  (hAst026Code.mul hAst254Code)
private theorem hAst255DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst255Denominator=true := by kernel_decide
private theorem hAst255DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst255Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst255Denominator hAst255DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst255Cross : equalCheck
    (mul hAst255Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst255Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst255Numerator) hAst255Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst255Code : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 6))^2)) :=
  hAst255Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst255Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst255Denominator)
    hAst255DenNonzero hAst255Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst256Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-12,0,-66,0,-234,0,-551,0,-820,0,-677,0,410,0,1215,0,2256,0,783,0,490,0,-1589,0,-532,0,-1015,0,294,0,-98,0,196,0,-49],[0],[4,0,58,0,390,0,1620,0,4568,0,8972,0,11958,0,9090,0,-848,0,-13252,0,-20130,0,-17202,0,-7348,0,2620,0,7274,0,6702,0,3812,0,1410,0,316,0,-18,0,4],[0],[-1,0,-14,0,-91,0,-374,0,-1091,0,-2374,0,-3976,0,-5234,0,-5571,0,-5054,0,-4184,0,-3306,0,-2429,0,-1546,0,-844,0,-430,0,-220,0,-100,0,-25]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst256Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,224,0,1456,0,5824,0,16016,0,32032,0,48048,0,54912,0,48048,0,32032,0,16016,0,5824,0,1456,0,224,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst256Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2))) :=
  (hAst246Code.add hAst249Code)
private theorem hAst256DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst256Denominator=true := by kernel_decide
private theorem hAst256DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst256Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst256Denominator hAst256DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst256Cross : equalCheck
    (mul hAst256Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst256Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst256Numerator) hAst256Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst256Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2))) :=
  hAst256Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst256Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst256Denominator)
    hAst256DenNonzero hAst256Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst257Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-12,0,-66,0,-222,0,-483,0,-660,0,-449,0,222,0,999,0,1344,0,999,0,222,0,-449,0,-660,0,-483,0,-222,0,-66,0,-12,0,-1],[0],[4,0,50,0,286,0,1000,0,2284,0,3330,0,2556,0,-852,0,-4608,0,-7142,0,-4764,0,-2000,0,2620,0,2686,0,3068,0,956,0,596,0,-76,0,6],[0],[-1,0,-12,0,-66,0,-230,0,-565,0,-1015,0,-1370,0,-1470,0,-1415,0,-1415,0,-1470,0,-1370,0,-1015,0,-565,0,-230,0,-66,0,-12,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst257Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,192,0,1056,0,3520,0,7920,0,12672,0,14784,0,12672,0,7920,0,3520,0,1056,0,192,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst257Raw : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  (hAst256Code.add hAst253Code)
private theorem hAst257DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst257Denominator=true := by kernel_decide
private theorem hAst257DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst257Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst257Denominator hAst257DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst257Cross : equalCheck
    (mul hAst257Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst257Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst257Numerator) hAst257Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst257Code : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  hAst257Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst257Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst257Denominator)
    hAst257DenNonzero hAst257Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst258Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-37,0,-13,0,21,0,58,0,58,0,21,0,-13,0,-37,0,-21,0,-7,0,-1],[0],[4,0,30,0,96,0,180,0,104,0,-104,0,-274,0,-334,0,-98,0,52,0,194,0,106,0,38,0,6],[0],[-1,0,-7,0,-21,0,-45,0,-55,0,-44,0,-38,0,-44,0,-55,0,-45,0,-21,0,-7,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst258Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst258Raw : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 6))^2))) :=
  (hAst257Code.add hAst255Code)
private theorem hAst258DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst258Denominator=true := by kernel_decide
private theorem hAst258DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst258Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst258Denominator hAst258DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst258Cross : equalCheck
    (mul hAst258Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst258Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst258Numerator) hAst258Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst258Code : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 6))^2))) :=
  hAst258Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst258Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst258Denominator)
    hAst258DenNonzero hAst258Cross

/-- Article: proposed exact numerator for hRadius6. -/
def hRadius6Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-37,0,-13,0,21,0,58,0,58,0,21,0,-13,0,-37,0,-21,0,-7,0,-1],[0],[4,0,30,0,96,0,180,0,104,0,-104,0,-274,0,-334,0,-98,0,52,0,194,0,106,0,38,0,6],[0],[-1,0,-7,0,-21,0,-45,0,-55,0,-44,0,-38,0,-44,0,-55,0,-45,0,-21,0,-7,0,-1]]
/-- Article: proposed positive denominator for hRadius6. -/
def hRadius6Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hRadius6Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 6))^2))) :=
  (hAst258Code.congr (by
    intro z hz
    ring))
private theorem hRadius6Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 6)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 6))^2))=Source.radius z.1 z.2 6 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.radius]; ring
private theorem hRadius6DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hRadius6Denominator=true := by kernel_decide
private theorem hRadius6DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hRadius6Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hRadius6Denominator hRadius6DenCheck hz.1 hz.2).ne'
private theorem hRadius6Cross : equalCheck
    (mul hRadius6Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hRadius6Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hRadius6Numerator) hRadius6Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hRadius6. -/
def hRadius6Code : RationalCode Source.domain (fun z => Source.radius z.1 z.2 6) :=
  (hRadius6Raw.congr hRadius6Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius6Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius6Denominator)
    hRadius6DenNonzero hRadius6Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst259Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst259Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst259Raw : RationalCode Source.domain (fun z => (z.1)^12) :=
  ((RationalCode.first Source.domain).pow 12)
private theorem hAst259DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst259Denominator=true := by kernel_decide
private theorem hAst259DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst259Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst259Denominator hAst259DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst259Cross : equalCheck
    (mul hAst259Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst259Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst259Numerator) hAst259Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst259Code : RationalCode Source.domain (fun z => (z.1)^12) :=
  hAst259Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst259Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst259Denominator)
    hAst259DenNonzero hAst259Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst260Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,0,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst260Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst260Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^12)) :=
  ((RationalCode.constant Source.domain (-1)).add hAst259Code)
private theorem hAst260DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst260Denominator=true := by kernel_decide
private theorem hAst260DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst260Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst260Denominator hAst260DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst260Cross : equalCheck
    (mul hAst260Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst260Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst260Numerator) hAst260Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst260Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^12)) :=
  hAst260Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst260Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst260Denominator)
    hAst260DenNonzero hAst260Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst261Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,1,0,0,0,0,0,0,0,0,0,-1,0,-1],[0,2,-2,-2,4,0,-4,0,4,0,-4,0,4,-2,-2,2],[1,0,1,0,0,0,0,0,0,0,0,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst261Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,8,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst261Raw : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^12))) :=
  (hValueCode.mul hAst260Code)
private theorem hAst261DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst261Denominator=true := by kernel_decide
private theorem hAst261DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst261Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst261Denominator hAst261DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst261Cross : equalCheck
    (mul hAst261Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst261Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst261Numerator) hAst261Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst261Code : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^12))) :=
  hAst261Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst261Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst261Denominator)
    hAst261DenNonzero hAst261Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst262Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,7,0,-14,0,-7,0,-36,0,-7,0,-14,0,7],[0],[2,0,13,0,36,0,50,0,40,0,16,0,-4,0,-10,0,-10,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst262Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst262Raw : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6))) :=
  (hDRealCode.add hGradientReal6Code)
private theorem hAst262DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst262Denominator=true := by kernel_decide
private theorem hAst262DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst262Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst262Denominator hAst262DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst262Cross : equalCheck
    (mul hAst262Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst262Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst262Numerator) hAst262Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst262Code : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6))) :=
  hAst262Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst262Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst262Denominator)
    hAst262DenNonzero hAst262Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst263Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-13,0,-29,0,-13,0,-37,0,-7,0,-14,0,7],[0],[1,0,7,0,21,0,30,0,25,0,10,0,-5,0,-10,0,-10,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst263Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst263Raw : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6))+(Source.multiplierReal z.1 z.2))) :=
  (hAst262Code.add hSRealCode)
private theorem hAst263DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst263Denominator=true := by kernel_decide
private theorem hAst263DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst263Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst263Denominator hAst263DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst263Cross : equalCheck
    (mul hAst263Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst263Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst263Numerator) hAst263Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst263Code : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6))+(Source.multiplierReal z.1 z.2))) :=
  hAst263Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst263Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst263Denominator)
    hAst263DenNonzero hAst263Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst264Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,21,0,3,0,-3,0,-23,0,-9,0,-12,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst264Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst264Raw : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))) :=
  ((RationalCode.constant Source.domain (-1/2)).mul hAst247Code)
private theorem hAst264DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst264Denominator=true := by kernel_decide
private theorem hAst264DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst264Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst264Denominator hAst264DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst264Cross : equalCheck
    (mul hAst264Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst264Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst264Numerator) hAst264Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst264Code : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))) :=
  hAst264Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst264Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst264Denominator)
    hAst264DenNonzero hAst264Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst265Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-12,0,-66,0,-214,0,-461,0,-712,0,-827,0,-880,0,-521,0,-406,0,571,0,602,0,1429,0,684,0,795,0,12,0,98,0,-98,0,7],[0],[1,0,13,0,78,0,282,0,670,0,1069,0,1079,0,492,0,-508,0,-1327,0,-1525,0,-1094,0,-350,0,195,0,405,0,320,0,155,0,50,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst265Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,52,0,312,0,1144,0,2860,0,5148,0,6864,0,6864,0,5148,0,2860,0,1144,0,312,0,52,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst265Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6))+(Source.multiplierReal z.1 z.2)))) :=
  (hAst264Code.mul hAst263Code)
private theorem hAst265DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst265Denominator=true := by kernel_decide
private theorem hAst265DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst265Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst265Denominator hAst265DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst265Cross : equalCheck
    (mul hAst265Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst265Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst265Numerator) hAst265Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst265Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6))+(Source.multiplierReal z.1 z.2)))) :=
  hAst265Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst265Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst265Denominator)
    hAst265DenNonzero hAst265Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst266Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,-1,0,18,0,1,0,28,0,1,0,18,0,-1],[0],[1,0,6,0,15,0,21,0,9,0,-11,0,-19,0,-17,0,-6,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst266Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst266Raw : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 6))) :=
  (hDImagCode.add hGradientImag6Code)
private theorem hAst266DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst266Denominator=true := by kernel_decide
private theorem hAst266DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst266Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst266Denominator hAst266DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst266Cross : equalCheck
    (mul hAst266Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst266Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst266Numerator) hAst266Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst266Code : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 6))) :=
  hAst266Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst266Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst266Denominator)
    hAst266DenNonzero hAst266Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst267Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,19,0,33,0,7,0,29,0,1,0,18,0,-1],[0],[0,0,0,0,1,0,-6,0,-17,0,-20,0,-17,0,-6,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst267Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,12,0,30,0,40,0,30,0,12,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst267Raw : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 6))+(Source.multiplierImag z.1 z.2))) :=
  (hAst266Code.add hSImagCode)
private theorem hAst267DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst267Denominator=true := by kernel_decide
private theorem hAst267DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst267Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst267Denominator hAst267DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst267Cross : equalCheck
    (mul hAst267Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst267Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst267Numerator) hAst267Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst267Code : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 6))+(Source.multiplierImag z.1 z.2))) :=
  hAst267Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst267Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst267Denominator)
    hAst267DenNonzero hAst267Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst268Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,3,0,-1,0,1,0,-6,0,1,0,-1,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst268Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst268Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))) :=
  (hAst040Code.mul hPowerImag6Code)
private theorem hAst268DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst268Denominator=true := by kernel_decide
private theorem hAst268DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst268Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst268Denominator hAst268DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst268Cross : equalCheck
    (mul hAst268Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst268Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst268Numerator) hAst268Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst268Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))) :=
  hAst268Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst268Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst268Denominator)
    hAst268DenNonzero hAst268Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst269Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,3,0,17,0,40,0,42,0,60,0,-78,0,11,0,-195,0,99,0,-163,0,134,0,-116,0,110,0,-16,0,55,0,-3],[0],[0,0,0,0,0,0,0,0,0,0,0,0,3,0,-19,0,-44,0,-55,0,-11,0,74,0,104,0,74,0,-11,0,-55,0,-44,0,-19,0,3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst269Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,26,0,156,0,572,0,1430,0,2574,0,3432,0,3432,0,2574,0,1430,0,572,0,156,0,26,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst269Raw : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 6))+(Source.multiplierImag z.1 z.2)))) :=
  (hAst268Code.mul hAst267Code)
private theorem hAst269DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst269Denominator=true := by kernel_decide
private theorem hAst269DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst269Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst269Denominator hAst269DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst269Cross : equalCheck
    (mul hAst269Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst269Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst269Numerator) hAst269Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst269Code : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 6))+(Source.multiplierImag z.1 z.2)))) :=
  hAst269Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst269Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst269Denominator)
    hAst269DenNonzero hAst269Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst270Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,6,0,34,0,80,0,96,0,-100,0,-92,0,-406,0,142,0,-178,0,506,0,-108,0,300,0,-208,0,32,0,-110,0,6],[0,2,-2,20,-18,88,-70,220,-150,330,-180,264,-84,-2,86,-284,198,-418,220,-440,220,-418,198,-284,86,-2,-84,264,-180,330,-150,220,-70,88,-18,20,-2,2],[2,0,25,0,144,0,502,0,1165,0,1861,0,2002,0,1272,0,-79,0,-1327,0,-1954,0,-1874,0,-1273,0,-597,0,-90,0,100,0,89,0,38,0,-6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst270Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,52,0,312,0,1144,0,2860,0,5148,0,6864,0,6864,0,5148,0,2860,0,1144,0,312,0,52,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst270Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^12))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6))+(Source.multiplierReal z.1 z.2))))) :=
  (hAst261Code.add hAst265Code)
private theorem hAst270DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst270Denominator=true := by kernel_decide
private theorem hAst270DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst270Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst270Denominator hAst270DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst270Cross : equalCheck
    (mul hAst270Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst270Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst270Numerator) hAst270Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst270Code : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^12))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6))+(Source.multiplierReal z.1 z.2))))) :=
  hAst270Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst270Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst270Denominator)
    hAst270DenNonzero hAst270Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst271Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,12,0,-4,0,4,0,-24,0,4,0,-4,0,12],[0,2,-2,8,-6,10,-4,0,4,-10,6,-8,2,-4,2,-8,6,-10,4,0,-4,10,-6,8,-2,2],[2,0,13,0,36,0,51,0,29,0,-5,0,-37,0,-43,0,-31,0,-16,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst271Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,28,0,84,0,140,0,140,0,84,0,28,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst271Raw : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^12))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 6))+(Source.multiplierImag z.1 z.2))))) :=
  (hAst270Code.add hAst269Code)
private theorem hAst271DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst271Denominator=true := by kernel_decide
private theorem hAst271DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst271Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst271Denominator hAst271DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst271Cross : equalCheck
    (mul hAst271Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst271Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst271Numerator) hAst271Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst271Code : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^12))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 6))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 6))+(Source.multiplierImag z.1 z.2))))) :=
  hAst271Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst271Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst271Denominator)
    hAst271DenNonzero hAst271Cross

/-- Article: proposed exact numerator for hDiscrepancy6. -/
def hDiscrepancy6Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,12,0,-4,0,4,0,-24,0,4,0,-4,0,12],[0,2,-2,8,-6,10,-4,0,4,-10,6,-8,2,-4,2,-8,6,-10,4,0,-4,10,-6,8,-2,2],[2,0,13,0,36,0,51,0,29,0,-5,0,-37,0,-43,0,-31,0,-16,0,1]]
/-- Article: proposed positive denominator for hDiscrepancy6. -/
def hDiscrepancy6Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,28,0,84,0,140,0,140,0,84,0,28,0,4]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDiscrepancy6Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^12))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 6)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 6)+(Source.multiplierImag z.1 z.2))))) :=
  (hAst271Code.congr (by
    intro z hz
    ring))
private theorem hDiscrepancy6Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^12))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 6))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 6)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 6)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 6)+(Source.multiplierImag z.1 z.2))))=Source.discrepancy z.1 z.2 6 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.discrepancy]; ring
private theorem hDiscrepancy6DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDiscrepancy6Denominator=true := by kernel_decide
private theorem hDiscrepancy6DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy6Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDiscrepancy6Denominator hDiscrepancy6DenCheck hz.1 hz.2).ne'
private theorem hDiscrepancy6Cross : equalCheck
    (mul hDiscrepancy6Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy6Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy6Numerator) hDiscrepancy6Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDiscrepancy6. -/
def hDiscrepancy6Code : RationalCode Source.domain (fun z => Source.discrepancy z.1 z.2 6) :=
  (hDiscrepancy6Raw.congr hDiscrepancy6Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy6Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy6Denominator)
    hDiscrepancy6DenNonzero hDiscrepancy6Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst272Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,-12,0,4,0,-4,0,24,0,-4,0,4,0,-12],[0,-2,2,-8,6,-10,4,0,-4,10,-6,8,-2,4,-2,8,-6,10,-4,0,4,-10,6,-8,2,-2],[-2,0,-13,0,-36,0,-51,0,-29,0,5,0,37,0,43,0,31,0,16,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst272Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,28,0,84,0,140,0,140,0,84,0,28,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst272Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 6))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDiscrepancy6Code)
private theorem hAst272DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst272Denominator=true := by kernel_decide
private theorem hAst272DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst272Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst272Denominator hAst272DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst272Cross : equalCheck
    (mul hAst272Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst272Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst272Numerator) hAst272Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst272Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 6))) :=
  hAst272Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst272Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst272Denominator)
    hAst272DenNonzero hAst272Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst273Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-37,0,-13,0,21,0,58,0,58,0,21,0,-13,0,-37,0,-21,0,-7,0,-1],[0],[20,0,142,0,432,0,740,0,664,0,232,0,-162,0,-318,0,-98,0,52,0,194,0,106,0,38,0,6],[0],[-1,0,-7,0,-21,0,-45,0,-55,0,-44,0,-38,0,-44,0,-55,0,-45,0,-21,0,-7,0,-1],[0],[0],[0],[32,0,224,0,672,0,1120,0,1120,0,672,0,224,0,32],[0],[0],[0],[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst273Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst273Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 6)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)) :=
  (hRadius6Code.add hAst228Code)
private theorem hAst273DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst273Denominator=true := by kernel_decide
private theorem hAst273DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst273Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst273Denominator hAst273DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst273Cross : equalCheck
    (mul hAst273Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst273Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst273Numerator) hAst273Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst273Code : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 6)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)) :=
  hAst273Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst273Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst273Denominator)
    hAst273DenNonzero hAst273Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst274Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-37,0,-13,0,21,0,58,0,58,0,21,0,-13,0,-37,0,-21,0,-7,0,-1],[0,0,0,0,0,0,0,0,-48,0,16,0,-16,0,96,0,-16,0,16,0,-48],[20,-8,150,-32,456,-40,756,0,648,40,208,32,-170,16,-326,32,-122,40,36,0,210,-40,130,-32,46,-8,6],[-8,0,-52,0,-144,0,-204,0,-116,0,20,0,148,0,172,0,124,0,64,0,-4],[-1,0,-7,0,-21,0,-45,0,-55,0,-44,0,-38,0,-44,0,-55,0,-45,0,-21,0,-7,0,-1],[0],[0],[0],[32,0,224,0,672,0,1120,0,1120,0,672,0,224,0,32],[0],[0],[0],[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst274Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst274Raw : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 6)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 6)))) :=
  (hAst273Code.add hAst272Code)
private theorem hAst274DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst274Denominator=true := by kernel_decide
private theorem hAst274DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst274Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst274Denominator hAst274DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst274Cross : equalCheck
    (mul hAst274Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst274Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst274Numerator) hAst274Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst274Code : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 6)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 6)))) :=
  hAst274Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst274Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst274Denominator)
    hAst274DenNonzero hAst274Cross

/-- Article: proposed exact numerator for hPairLower6. -/
def hPairLower6Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-37,0,-13,0,21,0,58,0,58,0,21,0,-13,0,-37,0,-21,0,-7,0,-1],[0,0,0,0,0,0,0,0,-48,0,16,0,-16,0,96,0,-16,0,16,0,-48],[20,-8,150,-32,456,-40,756,0,648,40,208,32,-170,16,-326,32,-122,40,36,0,210,-40,130,-32,46,-8,6],[-8,0,-52,0,-144,0,-204,0,-116,0,20,0,148,0,172,0,124,0,64,0,-4],[-1,0,-7,0,-21,0,-45,0,-55,0,-44,0,-38,0,-44,0,-55,0,-45,0,-21,0,-7,0,-1],[0],[0],[0],[32,0,224,0,672,0,1120,0,1120,0,672,0,224,0,32],[0],[0],[0],[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: proposed positive denominator for hPairLower6. -/
def hPairLower6Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairLower6Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 6)+((((1 : ℚ) : ℝ)+(z.2)^6))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 6)))) :=
  (hAst274Code.congr (by
    intro z hz
    ring))
private theorem hPairLower6Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.radius z.1 z.2 6)+((((1 : ℚ) : ℝ)+(z.2)^6))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 6)))=Source.pairSlack z.1 z.2 (-1) 6 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairLower6DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairLower6Denominator=true := by kernel_decide
private theorem hPairLower6DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairLower6Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairLower6Denominator hPairLower6DenCheck hz.1 hz.2).ne'
private theorem hPairLower6Cross : equalCheck
    (mul hPairLower6Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairLower6Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairLower6Numerator) hPairLower6Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairLower6. -/
def hPairLower6Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (-1) 6) :=
  (hPairLower6Raw.congr hPairLower6Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower6Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower6Denominator)
    hPairLower6DenNonzero hPairLower6Cross

end
end polyak.Certificates.Startup.Codes
