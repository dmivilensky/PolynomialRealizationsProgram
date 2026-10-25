import polyak.Certificates.Startup.Code13

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: canonical numerator for one arithmetic source node. -/
def hAst454Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,96,-38,176,-26,64,10,-16,-1],[0,0,0,-32,28,-128,76,-160,44,-64,-4],[0,0,-2,0,-16,-16,-20,0,-32,16,-2],[0,0,-4,0,-20,0,-20,0,-4],[-1,0,-6,0,-10,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst454Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,192,0,192,0,64]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst454Raw : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))))) :=
  ((RationalCode.constant Source.domain 1).add hAst452Code)
private theorem hAst454DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst454Denominator=true := by kernel_decide
private theorem hAst454DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst454Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst454Denominator hAst454DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst454Cross : equalCheck
    (mul hAst454Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst454Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst454Numerator) hAst454Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst454Code : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))))) :=
  hAst454Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst454Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst454Denominator)
    hAst454DenNonzero hAst454Cross

/-- Article: proposed exact numerator for check15. -/
def check15Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,96,-38,176,-26,64,10,-16,-1],[0,0,0,-32,28,-128,76,-160,44,-64,-4],[0,0,-2,0,-16,-16,-20,0,-32,16,-2],[0,0,-4,0,-20,0,-20,0,-4],[-1,0,-6,0,-10,0,-6,0,-1]]
/-- Article: proposed positive denominator for check15. -/
def check15Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,192,0,192,0,64]]
/-- Article: composition of proved source-preserving rational operations. -/
def check15Raw : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))))) :=
  (hAst454Code.congr (by
    intro z hz
    ring))
private theorem check15Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))))=(((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check15DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check15Denominator=true := by kernel_decide
private theorem check15DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check15Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check15Denominator check15DenCheck hz.1 hz.2).ne'
private theorem check15Cross : equalCheck
    (mul check15Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check15Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check15Numerator) check15Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check15. -/
def check15Code : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))))) :=
  (check15Raw.congr check15Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check15Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check15Denominator)
    check15DenNonzero check15Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst455Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,6,6,6,40,-46,34,-6,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst455Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,40,0,120,0,120,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst455Raw : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  (hQuadraticUpperCode.add hAst420Code)
private theorem hAst455DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst455Denominator=true := by kernel_decide
private theorem hAst455DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst455Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst455Denominator hAst455DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst455Cross : equalCheck
    (mul hAst455Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst455Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst455Numerator) hAst455Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst455Code : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  hAst455Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst455Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst455Denominator)
    hAst455DenNonzero hAst455Cross

/-- Article: proposed exact numerator for check16. -/
def check16Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,6,6,6,40,-46,34,-6,-3]]
/-- Article: proposed positive denominator for check16. -/
def check16Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,40,0,120,0,120,0,40]]
/-- Article: composition of proved source-preserving rational operations. -/
def check16Raw : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  (hAst455Code.congr (by
    intro z hz
    ring))
private theorem check16Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.quadratic z.1 (1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))=((Source.quadratic z.1 (1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check16DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check16Denominator=true := by kernel_decide
private theorem check16DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check16Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check16Denominator check16DenCheck hz.1 hz.2).ne'
private theorem check16Cross : equalCheck
    (mul check16Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check16Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check16Numerator) check16Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check16. -/
def check16Code : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  (check16Raw.congr check16Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check16Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check16Denominator)
    check16DenNonzero check16Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst456Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2,16,-14,16],[0,0,8,0,12,0,4],[1,0,1,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst456Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,32,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst456Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1)))) :=
  (hConstantUpperCode.add hQuadraticUpperCode)
private theorem hAst456DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst456Denominator=true := by kernel_decide
private theorem hAst456DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst456Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst456Denominator hAst456DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst456Cross : equalCheck
    (mul hAst456Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst456Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst456Numerator) hAst456Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst456Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1)))) :=
  hAst456Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst456Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst456Denominator)
    hAst456DenNonzero hAst456Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst457Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,16,18,16,16],[0,0,8,0,12,0,4],[1,0,1,0,-1,0,-1],[0],[0,0,-32,0,-64,0,-32],[0],[0],[0],[0,0,16,0,32,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst457Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,32,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst457Raw : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1)))+(Source.reserve z.2))) :=
  (hAst456Code.add hReserveCode)
private theorem hAst457DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst457Denominator=true := by kernel_decide
private theorem hAst457DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst457Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst457Denominator hAst457DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst457Cross : equalCheck
    (mul hAst457Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst457Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst457Numerator) hAst457Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst457Code : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1)))+(Source.reserve z.2))) :=
  hAst457Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst457Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst457Denominator)
    hAst457DenNonzero hAst457Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst458Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,16],[0],[-1,0,-4,0,-1],[0],[0,0,-32,0,-32],[0],[0],[0],[0,0,16,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst458Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst458Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (1) 0))) :=
  (hAst457Code.add hResidueUpper0Code)
private theorem hAst458DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst458Denominator=true := by kernel_decide
private theorem hAst458DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst458Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst458Denominator hAst458DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst458Cross : equalCheck
    (mul hAst458Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst458Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst458Numerator) hAst458Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst458Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (1) 0))) :=
  hAst458Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst458Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst458Denominator)
    hAst458DenNonzero hAst458Cross

/-- Article: proposed exact numerator for check17. -/
def check17Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,16],[0],[-1,0,-4,0,-1],[0],[0,0,-32,0,-32],[0],[0],[0],[0,0,16,0,16]]
/-- Article: proposed positive denominator for check17. -/
def check17Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check17Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 0))) :=
  (hAst458Code.congr (by
    intro z hz
    ring))
private theorem check17Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 0))=((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 0)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check17DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check17Denominator=true := by kernel_decide
private theorem check17DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check17Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check17Denominator check17DenCheck hz.1 hz.2).ne'
private theorem check17Cross : equalCheck
    (mul check17Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check17Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check17Numerator) check17Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check17. -/
def check17Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 0))) :=
  (check17Raw.congr check17Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check17Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check17Denominator)
    check17DenNonzero check17Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst459Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-3,-1,-43,35,-37,6,3],[0,0,-20,0,-30,0,-10],[-5,0,-15,0,-10]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst459Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,40,0,80,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst459Raw : RationalCode Source.domain (fun z => ((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0))) :=
  (hEpsilonCode.add hResidueUpper0Code)
private theorem hAst459DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst459Denominator=true := by kernel_decide
private theorem hAst459DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst459Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst459Denominator hAst459DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst459Cross : equalCheck
    (mul hAst459Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst459Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst459Numerator) hAst459Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst459Code : RationalCode Source.domain (fun z => ((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0))) :=
  hAst459Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst459Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst459Denominator)
    hAst459DenNonzero hAst459Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst460Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,9,6,259,-124,2001,-2972,4377,-3112,1531,-234,-186,36,9],[0,0,0,120,40,1900,-1340,4120,-2320,2960,-1060,560,-120,-60],[0,30,10,520,80,1720,110,1940,420,650,480,-60,100],[0,0,200,0,900,0,1400,0,900,0,200],[25,0,150,0,325,0,300,0,100]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst460Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1600,0,6400,0,9600,0,6400,0,1600]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst460Raw : RationalCode Source.domain (fun z => (((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0)))^2) :=
  (hAst459Code.pow 2)
private theorem hAst460DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst460Denominator=true := by kernel_decide
private theorem hAst460DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst460Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst460Denominator hAst460DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst460Cross : equalCheck
    (mul hAst460Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst460Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst460Numerator) hAst460Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst460Code : RationalCode Source.domain (fun z => (((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0)))^2) :=
  hAst460Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst460Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst460Denominator)
    hAst460DenNonzero hAst460Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst461Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-9,-6,-259,124,-2001,2972,-4377,3112,-1531,234,186,-36,-9],[0,0,0,-120,-40,-1900,1340,-4120,2320,-2960,1060,-560,120,60],[0,-30,-10,-520,-80,-1720,-110,-1940,-420,-650,-480,60,-100],[0,0,-200,0,-900,0,-1400,0,-900,0,-200],[-25,0,-150,0,-325,0,-300,0,-100]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst461Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1600,0,6400,0,9600,0,6400,0,1600]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst461Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0)))^2)) :=
  ((RationalCode.constant Source.domain (-1)).mul hAst460Code)
private theorem hAst461DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst461Denominator=true := by kernel_decide
private theorem hAst461DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst461Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst461Denominator hAst461DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst461Cross : equalCheck
    (mul hAst461Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst461Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst461Numerator) hAst461Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst461Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0)))^2)) :=
  hAst461Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst461Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst461Denominator)
    hAst461DenNonzero hAst461Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst462Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,4,-4,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst462Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst462Raw : RationalCode Source.domain (fun z => (((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1)))) :=
  ((RationalCode.constant Source.domain 4).mul hQuadraticUpperCode)
private theorem hAst462DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst462Denominator=true := by kernel_decide
private theorem hAst462DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst462Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst462Denominator hAst462DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst462Cross : equalCheck
    (mul hAst462Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst462Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst462Numerator) hAst462Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst462Code : RationalCode Source.domain (fun z => (((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1)))) :=
  hAst462Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst462Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst462Denominator)
    hAst462DenNonzero hAst462Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst463Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,6,6,6,40,-46,34,-6,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst463Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,10,0,30,0,30,0,10]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst463Raw : RationalCode Source.domain (fun z => (((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))) :=
  (hAst435Code.add hAst462Code)
private theorem hAst463DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst463Denominator=true := by kernel_decide
private theorem hAst463DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst463Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst463Denominator hAst463DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst463Cross : equalCheck
    (mul hAst463Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst463Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst463Numerator) hAst463Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst463Code : RationalCode Source.domain (fun z => (((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))) :=
  hAst463Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst463Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst463Denominator)
    hAst463DenNonzero hAst463Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst464Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,42,132,276,420,1094,584,1464,24,2310,-1900,2148,-1084,394,-96,-48],[0,0,24,48,108,168,488,-152,1180,-848,1320,-832,644,-280,88,-24,-12],[3,6,12,18,52,-34,108,-110,50,-30,-92,86,-108,58,-28,6,3],[0],[0,0,-96,-192,-480,-768,-2144,320,-5600,3840,-7200,4800,-4256,2048,-800,192,96],[0],[0],[0],[0,0,48,96,240,384,1072,-160,2800,-1920,3600,-2400,2128,-1024,400,-96,-48]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst464Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,160,0,960,0,2400,0,3200,0,2400,0,960,0,160]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst464Raw : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1)))))) :=
  (hAst450Code.mul hAst463Code)
private theorem hAst464DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst464Denominator=true := by kernel_decide
private theorem hAst464DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst464Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst464Denominator hAst464DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst464Cross : equalCheck
    (mul hAst464Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst464Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst464Numerator) hAst464Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst464Code : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1)))))) :=
  hAst464Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst464Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst464Denominator)
    hAst464DenNonzero hAst464Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst465Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-9,414,1043,2872,1672,14154,-2798,23820,-12046,32530,-26253,25024,-12008,4102,-792,-516,-9],[0,0,0,120,440,-1060,2940,-3160,3440,-1300,-1440,2600,-3760,2420,-1500,440,-120,-60],[0,0,50,-460,80,-2270,-620,-4820,-1820,-5750,-1730,-4100,-620,-1610,-100,-220,-40,30],[0,0,-200,0,-1300,0,-3400,0,-4600,0,-3400,0,-1300,0,-200],[-25,0,-200,-960,-2570,-4800,-8780,-21440,2175,-56000,37900,-72000,47900,-42560,20480,-8000,1920,960],[0],[0],[0],[0,0,0,480,960,2400,3840,10720,-1600,28000,-19200,36000,-24000,21280,-10240,4000,-960,-480]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst465Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1600,0,9600,0,24000,0,32000,0,24000,0,9600,0,1600]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst465Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))))) :=
  (hAst461Code.add hAst464Code)
private theorem hAst465DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst465Denominator=true := by kernel_decide
private theorem hAst465DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst465Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst465Denominator hAst465DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst465Cross : equalCheck
    (mul hAst465Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst465Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst465Numerator) hAst465Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst465Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))))) :=
  hAst465Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst465Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst465Denominator)
    hAst465DenNonzero hAst465Cross

/-- Article: proposed exact numerator for check18. -/
def check18Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-9,414,1043,2872,1672,14154,-2798,23820,-12046,32530,-26253,25024,-12008,4102,-792,-516,-9],[0,0,0,120,440,-1060,2940,-3160,3440,-1300,-1440,2600,-3760,2420,-1500,440,-120,-60],[0,0,50,-460,80,-2270,-620,-4820,-1820,-5750,-1730,-4100,-620,-1610,-100,-220,-40,30],[0,0,-200,0,-1300,0,-3400,0,-4600,0,-3400,0,-1300,0,-200],[-25,0,-200,-960,-2570,-4800,-8780,-21440,2175,-56000,37900,-72000,47900,-42560,20480,-8000,1920,960],[0],[0],[0],[0,0,0,480,960,2400,3840,10720,-1600,28000,-19200,36000,-24000,21280,-10240,4000,-960,-480]]
/-- Article: proposed positive denominator for check18. -/
def check18Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1600,0,9600,0,24000,0,32000,0,24000,0,9600,0,1600]]
/-- Article: composition of proved source-preserving rational operations. -/
def check18Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))))) :=
  (hAst465Code.congr (by
    intro z hz
    ring))
private theorem check18Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))))=(((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1)))))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check18DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check18Denominator=true := by kernel_decide
private theorem check18DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check18Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check18Denominator check18DenCheck hz.1 hz.2).ne'
private theorem check18Cross : equalCheck
    (mul check18Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check18Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check18Numerator) check18Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check18. -/
def check18Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 0)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))))) :=
  (check18Raw.congr check18Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check18Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check18Denominator)
    check18DenNonzero check18Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst466Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2,24,16,26,18,24,0,-2],[0,-4,8,0,20,4,16,0,4],[1,4,2,10,0,8,-2,2,-1],[0],[0,0,-32,0,-96,0,-96,0,-32],[0],[0],[0],[0,0,16,0,48,0,48,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst466Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst466Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (1) 1))) :=
  (hAst457Code.add hResidueUpper1Code)
private theorem hAst466DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst466Denominator=true := by kernel_decide
private theorem hAst466DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst466Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst466Denominator hAst466DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst466Cross : equalCheck
    (mul hAst466Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst466Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst466Numerator) hAst466Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst466Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (1) 1))) :=
  hAst466Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst466Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst466Denominator)
    hAst466DenNonzero hAst466Cross

/-- Article: proposed exact numerator for check19. -/
def check19Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2,24,16,26,18,24,0,-2],[0,-4,8,0,20,4,16,0,4],[1,4,2,10,0,8,-2,2,-1],[0],[0,0,-32,0,-96,0,-96,0,-32],[0],[0],[0],[0,0,16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for check19. -/
def check19Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check19Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 1))) :=
  (hAst466Code.congr (by
    intro z hz
    ring))
private theorem check19Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 1))=((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 1)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check19DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check19Denominator=true := by kernel_decide
private theorem check19DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check19Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check19Denominator check19DenCheck hz.1 hz.2).ne'
private theorem check19Cross : equalCheck
    (mul check19Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check19Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check19Numerator) check19Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check19. -/
def check19Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 1))) :=
  (check19Raw.congr check19Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check19Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check19Denominator)
    check19DenNonzero check19Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst467Numerator : polyak.Numerics.IntegerBivariate.Source := [[-3,-46,14,-46,-15,-34,26,-34,-2],[-10,0,0,0,10],[10,0,25,0,20,0,5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst467Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,40,0,120,0,120,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst467Raw : RationalCode Source.domain (fun z => ((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1))) :=
  (hEpsilonCode.add hResidueUpper1Code)
private theorem hAst467DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst467Denominator=true := by kernel_decide
private theorem hAst467DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst467Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst467Denominator hAst467DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst467Cross : equalCheck
    (mul hAst467Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst467Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst467Numerator) hAst467Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst467Code : RationalCode Source.domain (fun z => ((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1))) :=
  hAst467Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst467Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst467Denominator)
    hAst467DenNonzero hAst467Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst468Numerator : polyak.Numerics.IntegerBivariate.Source := [[9,276,2032,-1012,4518,296,4668,-1760,7221,-2140,3448,-564,3048,-1632,1052,136,4],[60,920,-280,920,240,-240,-240,-240,-260,-680,520,-680,-40],[40,-920,130,-3220,80,-4820,300,-4680,900,-3520,790,-1700,180,-340,-20],[-200,0,-500,0,-200,0,400,0,400,0,100],[100,0,500,0,1025,0,1100,0,650,0,200,0,25]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst468Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1600,0,9600,0,24000,0,32000,0,24000,0,9600,0,1600]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst468Raw : RationalCode Source.domain (fun z => (((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1)))^2) :=
  (hAst467Code.pow 2)
private theorem hAst468DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst468Denominator=true := by kernel_decide
private theorem hAst468DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst468Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst468Denominator hAst468DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst468Cross : equalCheck
    (mul hAst468Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst468Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst468Numerator) hAst468Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst468Code : RationalCode Source.domain (fun z => (((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1)))^2) :=
  hAst468Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst468Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst468Denominator)
    hAst468DenNonzero hAst468Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst469Numerator : polyak.Numerics.IntegerBivariate.Source := [[-9,-276,-2032,1012,-4518,-296,-4668,1760,-7221,2140,-3448,564,-3048,1632,-1052,-136,-4],[-60,-920,280,-920,-240,240,240,240,260,680,-520,680,40],[-40,920,-130,3220,-80,4820,-300,4680,-900,3520,-790,1700,-180,340,20],[200,0,500,0,200,0,-400,0,-400,0,-100],[-100,0,-500,0,-1025,0,-1100,0,-650,0,-200,0,-25]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst469Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1600,0,9600,0,24000,0,32000,0,24000,0,9600,0,1600]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst469Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1)))^2)) :=
  ((RationalCode.constant Source.domain (-1)).mul hAst468Code)
private theorem hAst469DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst469Denominator=true := by kernel_decide
private theorem hAst469DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst469Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst469Denominator hAst469DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst469Cross : equalCheck
    (mul hAst469Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst469Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst469Numerator) hAst469Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst469Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1)))^2)) :=
  hAst469Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst469Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst469Denominator)
    hAst469DenNonzero hAst469Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst470Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-9,144,-712,3772,-318,10644,1172,16400,-6981,25240,-22448,22044,-13888,5572,-2012,-616,-4],[0,-60,-680,760,160,1440,5120,-1280,12040,-8220,13880,-8840,7120,-2760,880,-240,-120],[30,20,1040,50,3740,-420,5900,-1400,5180,-1200,2600,70,620,400,60,80,30],[0,200,0,500,0,200,0,-400,0,-400,0,-100],[0,-100,-960,-2420,-4800,-8705,-21440,2100,-56000,37750,-72000,47800,-42560,20455,-8000,1920,960],[0],[0],[0],[0,0,480,960,2400,3840,10720,-1600,28000,-19200,36000,-24000,21280,-10240,4000,-960,-480]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst470Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,1600,0,9600,0,24000,0,32000,0,24000,0,9600,0,1600]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst470Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))))) :=
  (hAst469Code.add hAst464Code)
private theorem hAst470DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst470Denominator=true := by kernel_decide
private theorem hAst470DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst470Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst470Denominator hAst470DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst470Cross : equalCheck
    (mul hAst470Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst470Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst470Numerator) hAst470Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst470Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))))) :=
  hAst470Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst470Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst470Denominator)
    hAst470DenNonzero hAst470Cross

/-- Article: proposed exact numerator for check20. -/
def check20Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-9,144,-712,3772,-318,10644,1172,16400,-6981,25240,-22448,22044,-13888,5572,-2012,-616,-4],[0,-60,-680,760,160,1440,5120,-1280,12040,-8220,13880,-8840,7120,-2760,880,-240,-120],[30,20,1040,50,3740,-420,5900,-1400,5180,-1200,2600,70,620,400,60,80,30],[0,200,0,500,0,200,0,-400,0,-400,0,-100],[0,-100,-960,-2420,-4800,-8705,-21440,2100,-56000,37750,-72000,47800,-42560,20455,-8000,1920,960],[0],[0],[0],[0,0,480,960,2400,3840,10720,-1600,28000,-19200,36000,-24000,21280,-10240,4000,-960,-480]]
/-- Article: proposed positive denominator for check20. -/
def check20Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,1600,0,9600,0,24000,0,32000,0,24000,0,9600,0,1600]]
/-- Article: composition of proved source-preserving rational operations. -/
def check20Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))))) :=
  (hAst470Code.congr (by
    intro z hz
    ring))
private theorem check20Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))))=(((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1)))))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check20DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check20Denominator=true := by kernel_decide
private theorem check20DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check20Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check20Denominator check20DenCheck hz.1 hz.2).ne'
private theorem check20Cross : equalCheck
    (mul check20Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check20Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check20Numerator) check20Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check20. -/
def check20Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (1) 1)))^2)+(((Source.constant z.1 z.2 (1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))))) :=
  (check20Raw.congr check20Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check20Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check20Denominator)
    check20DenNonzero check20Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst471Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,12,64,12,128,48,128,20,64,20],[0,0,24,0,56,0,64,0,40,0,8],[3,0,5,0,0,0,-4,0,-3,0,-1],[0],[0,0,-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[0,0,16,0,64,0,96,0,64,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst471Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst471Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (1) 2))) :=
  (hAst457Code.add hResidueUpper2Code)
private theorem hAst471DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst471Denominator=true := by kernel_decide
private theorem hAst471DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst471Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst471Denominator hAst471DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst471Cross : equalCheck
    (mul hAst471Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst471Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst471Numerator) hAst471Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst471Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (1) 2))) :=
  hAst471Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst471Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst471Denominator)
    hAst471DenNonzero hAst471Cross

/-- Article: proposed exact numerator for check21. -/
def check21Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,12,64,12,128,48,128,20,64,20],[0,0,24,0,56,0,64,0,40,0,8],[3,0,5,0,0,0,-4,0,-3,0,-1],[0],[0,0,-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[0,0,16,0,64,0,96,0,64,0,16]]
/-- Article: proposed positive denominator for check21. -/
def check21Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,64,0,96,0,64,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check21Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 2))) :=
  (hAst471Code.congr (by
    intro z hz
    ring))
private theorem check21Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 2))=((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 2)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check21DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check21Denominator=true := by kernel_decide
private theorem check21DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check21Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check21Denominator check21DenCheck hz.1 hz.2).ne'
private theorem check21Cross : equalCheck
    (mul check21Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check21Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check21Numerator) check21Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check21. -/
def check21Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.quadratic z.1 (1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (1) 2))) :=
  (check21Raw.congr check21Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check21Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check21Denominator)
    check21DenNonzero check21Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst472Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,2,-2,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst472Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst472Raw : RationalCode Source.domain (fun z => (((2 : ℚ) : ℝ)*(Source.quadratic z.1 (1)))) :=
  ((RationalCode.constant Source.domain 2).mul hQuadraticUpperCode)
private theorem hAst472DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst472Denominator=true := by kernel_decide
private theorem hAst472DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst472Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst472Denominator hAst472DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst472Cross : equalCheck
    (mul hAst472Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst472Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst472Numerator) hAst472Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst472Code : RationalCode Source.domain (fun z => (((2 : ℚ) : ℝ)*(Source.quadratic z.1 (1)))) :=
  hAst472Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst472Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst472Denominator)
    hAst472DenNonzero hAst472Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst473Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,3,1,129,-73,206,-45,194,-87,111,4,-3],[0,0,40,0,70,0,70,0,50,0,10],[5,0,5,0,-5,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst473Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,40,0,160,0,240,0,160,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst473Raw : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (1) 2)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  (hResidueUpper2Code.add hAst420Code)
private theorem hAst473DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst473Denominator=true := by kernel_decide
private theorem hAst473DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst473Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst473Denominator hAst473DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst473Cross : equalCheck
    (mul hAst473Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst473Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst473Numerator) hAst473Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst473Code : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (1) 2)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  hAst473Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst473Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst473Denominator)
    hAst473DenNonzero hAst473Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst474Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,3,1,129,-73,286,-125,354,-167,191,4,-3],[0,0,40,0,70,0,70,0,50,0,10],[5,0,5,0,-5,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst474Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,40,0,160,0,240,0,160,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst474Raw : RationalCode Source.domain (fun z => (((Source.residue z.1 z.2 (1) 2)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))) :=
  (hAst473Code.add hAst472Code)
private theorem hAst474DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst474Denominator=true := by kernel_decide
private theorem hAst474DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst474Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst474Denominator hAst474DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst474Cross : equalCheck
    (mul hAst474Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst474Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst474Numerator) hAst474Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst474Code : RationalCode Source.domain (fun z => (((Source.residue z.1 z.2 (1) 2)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))) :=
  hAst474Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst474Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst474Denominator)
    hAst474DenNonzero hAst474Cross

/-- Article: proposed exact numerator for check22. -/
def check22Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,3,1,129,-73,286,-125,354,-167,191,4,-3],[0,0,40,0,70,0,70,0,50,0,10],[5,0,5,0,-5,0,-5]]
/-- Article: proposed positive denominator for check22. -/
def check22Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,40,0,160,0,240,0,160,0,40]]
/-- Article: composition of proved source-preserving rational operations. -/
def check22Raw : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (1) 2)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))) :=
  (hAst474Code.congr (by
    intro z hz
    ring))
private theorem check22Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.residue z.1 z.2 (1) 2)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))=((Source.residue z.1 z.2 (1) 2)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (1)))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check22DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check22Denominator=true := by kernel_decide
private theorem check22DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check22Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check22Denominator check22DenCheck hz.1 hz.2).ne'
private theorem check22Cross : equalCheck
    (mul check22Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check22Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check22Numerator) check22Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check22. -/
def check22Code : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (1) 2)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (1))))) :=
  (check22Raw.congr check22Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check22Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check22Denominator)
    check22DenNonzero check22Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst475Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,1,-2,3,-2,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst475Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst475Raw : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (1)))^2) :=
  (hQuadraticUpperCode.pow 2)
private theorem hAst475DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst475Denominator=true := by kernel_decide
private theorem hAst475DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst475Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst475Denominator hAst475DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst475Cross : equalCheck
    (mul hAst475Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst475Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst475Numerator) hAst475Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst475Code : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (1)))^2) :=
  hAst475Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst475Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst475Denominator)
    hAst475DenNonzero hAst475Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst476Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,4,-8,12,-8,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst476Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst476Raw : RationalCode Source.domain (fun z => (((4 : ℚ) : ℝ)*((Source.quadratic z.1 (1)))^2)) :=
  ((RationalCode.constant Source.domain 4).mul hAst475Code)
private theorem hAst476DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst476Denominator=true := by kernel_decide
private theorem hAst476DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst476Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst476Denominator hAst476DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst476Cross : equalCheck
    (mul hAst476Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst476Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst476Numerator) hAst476Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst476Code : RationalCode Source.domain (fun z => (((4 : ℚ) : ℝ)*((Source.quadratic z.1 (1)))^2)) :=
  hAst476Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst476Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst476Denominator)
    hAst476DenNonzero hAst476Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst477Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,-8,12,-8,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst477Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst477Raw : RationalCode Source.domain (fun z => ((((4 : ℚ) : ℝ)*((Source.quadratic z.1 (1)))^2)*(z.1)^20)) :=
  (hAst476Code.mul hAst441Code)
private theorem hAst477DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst477Denominator=true := by kernel_decide
private theorem hAst477DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst477Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst477Denominator hAst477DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst477Cross : equalCheck
    (mul hAst477Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst477Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst477Numerator) hAst477Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst477Code : RationalCode Source.domain (fun z => ((((4 : ℚ) : ℝ)*((Source.quadratic z.1 (1)))^2)*(z.1)^20)) :=
  hAst477Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst477Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst477Denominator)
    hAst477DenNonzero hAst477Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst478Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-65,96,-425,464,-1103,880,-1463,800,-1047,320,-383,16,-57,-16,-1,0,0,0,0,0,0,0,0,0,0,0,256,-512,768,-512,256],[0,0,0,-32,28,-224,160,-640,356,-960,384,-800,196,-352,32,-64,-4],[0,0,-2,0,-22,-16,-74,-48,-142,-32,-174,32,-122,48,-38,16,-2],[0,0,-4,0,-32,0,-92,0,-128,0,-92,0,-32,0,-4],[-1,0,-9,0,-31,0,-55,0,-55,0,-31,0,-9,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst478Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,384,0,960,0,1280,0,960,0,384,0,64]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst478Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))+((((4 : ℚ) : ℝ)*((Source.quadratic z.1 (1)))^2)*(z.1)^20))) :=
  (hAst452Code.add hAst477Code)
private theorem hAst478DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst478Denominator=true := by kernel_decide
private theorem hAst478DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst478Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst478Denominator hAst478DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst478Cross : equalCheck
    (mul hAst478Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst478Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst478Numerator) hAst478Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst478Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))+((((4 : ℚ) : ℝ)*((Source.quadratic z.1 (1)))^2)*(z.1)^20))) :=
  hAst478Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst478Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst478Denominator)
    hAst478DenNonzero hAst478Cross

/-- Article: proposed exact numerator for check23. -/
def check23Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-65,96,-425,464,-1103,880,-1463,800,-1047,320,-383,16,-57,-16,-1,0,0,0,0,0,0,0,0,0,0,0,256,-512,768,-512,256],[0,0,0,-32,28,-224,160,-640,356,-960,384,-800,196,-352,32,-64,-4],[0,0,-2,0,-22,-16,-74,-48,-142,-32,-174,32,-122,48,-38,16,-2],[0,0,-4,0,-32,0,-92,0,-128,0,-92,0,-32,0,-4],[-1,0,-9,0,-31,0,-55,0,-55,0,-31,0,-9,0,-1]]
/-- Article: proposed positive denominator for check23. -/
def check23Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,384,0,960,0,1280,0,960,0,384,0,64]]
/-- Article: composition of proved source-preserving rational operations. -/
def check23Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))+(((4 : ℚ) : ℝ)*((Source.quadratic z.1 (1)))^2*(z.1)^20))) :=
  (hAst478Code.congr (by
    intro z hz
    ring))
private theorem check23Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))+(((4 : ℚ) : ℝ)*((Source.quadratic z.1 (1)))^2*(z.1)^20))=(((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))+(((4 : ℚ) : ℝ)*((Source.quadratic z.1 (1)))^2*(z.1)^20)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check23DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check23Denominator=true := by kernel_decide
private theorem check23DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check23Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check23Denominator check23DenCheck hz.1 hz.2).ne'
private theorem check23Cross : equalCheck
    (mul check23Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check23Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check23Numerator) check23Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check23. -/
def check23Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))+(((4 : ℚ) : ℝ)*((Source.quadratic z.1 (1)))^2*(z.1)^20))) :=
  (check23Raw.congr check23Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check23Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check23Denominator)
    check23DenNonzero check23Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst479Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst479Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst479Raw : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (1))*(z.1)^20)) :=
  (hQuadraticUpperCode.mul hAst441Code)
private theorem hAst479DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst479Denominator=true := by kernel_decide
private theorem hAst479DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst479Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst479Denominator hAst479DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst479Cross : equalCheck
    (mul hAst479Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst479Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst479Numerator) hAst479Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst479Code : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (1))*(z.1)^20)) :=
  hAst479Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst479Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst479Denominator)
    hAst479DenNonzero hAst479Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst480Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,16,18,0,32,0,-16,0,16,0,-16,0,16,0,-16,0,16,0,-16,0,16,0,-16,16],[0,0,8,0,12,0,4],[1,0,1,0,-1,0,-1],[0],[0,0,-32,0,-64,0,-32],[0],[0],[0],[0,0,16,0,32,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst480Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,32,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst480Raw : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (1))+(Source.reserve z.2))+((Source.quadratic z.1 (1))*(z.1)^20))) :=
  (hAst450Code.add hAst479Code)
private theorem hAst480DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst480Denominator=true := by kernel_decide
private theorem hAst480DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst480Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst480Denominator hAst480DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst480Cross : equalCheck
    (mul hAst480Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst480Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst480Numerator) hAst480Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst480Code : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (1))+(Source.reserve z.2))+((Source.quadratic z.1 (1))*(z.1)^20))) :=
  hAst480Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst480Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst480Denominator)
    hAst480DenNonzero hAst480Cross

/-- Article: proposed exact numerator for check24. -/
def check24Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,16,18,0,32,0,-16,0,16,0,-16,0,16,0,-16,0,16,0,-16,0,16,0,-16,16],[0,0,8,0,12,0,4],[1,0,1,0,-1,0,-1],[0],[0,0,-32,0,-64,0,-32],[0],[0],[0],[0,0,16,0,32,0,16]]
/-- Article: proposed positive denominator for check24. -/
def check24Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,32,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check24Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.reserve z.2)+((Source.quadratic z.1 (1))*(z.1)^20))) :=
  (hAst480Code.congr (by
    intro z hz
    ring))
private theorem check24Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.constant z.1 z.2 (1))+(Source.reserve z.2)+((Source.quadratic z.1 (1))*(z.1)^20))=((Source.constant z.1 z.2 (1))+(Source.reserve z.2)+((Source.quadratic z.1 (1))*(z.1)^20)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check24DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check24Denominator=true := by kernel_decide
private theorem check24DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check24Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check24Denominator check24DenCheck hz.1 hz.2).ne'
private theorem check24Cross : equalCheck
    (mul check24Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check24Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check24Numerator) check24Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check24. -/
def check24Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.reserve z.2)+((Source.quadratic z.1 (1))*(z.1)^20))) :=
  (check24Raw.congr check24Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check24Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check24Denominator)
    check24DenNonzero check24Cross

end
end polyak.Certificates.Startup.Codes
