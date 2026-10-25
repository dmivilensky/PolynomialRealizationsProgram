import polyak.Certificates.Startup.Code12

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: canonical numerator for one arithmetic source node. -/
def hAst425Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,2,-2,2]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst425Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst425Raw : RationalCode Source.domain (fun z => (((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1)))) :=
  ((RationalCode.constant Source.domain 2).mul hQuadraticLowerCode)
private theorem hAst425DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst425Denominator=true := by kernel_decide
private theorem hAst425DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst425Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst425Denominator hAst425DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst425Cross : equalCheck
    (mul hAst425Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst425Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst425Numerator) hAst425Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst425Code : RationalCode Source.domain (fun z => (((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1)))) :=
  hAst425Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst425Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst425Denominator)
    hAst425DenNonzero hAst425Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst426Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,3,11,-37,35,-43,-6,-3],[0,0,20,0,30,0,10],[-5,0,-15,0,-10]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst426Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,40,0,80,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst426Raw : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (-1) 0)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  (hResidueLower0Code.add hAst420Code)
private theorem hAst426DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst426Denominator=true := by kernel_decide
private theorem hAst426DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst426Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst426Denominator hAst426DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst426Cross : equalCheck
    (mul hAst426Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst426Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst426Numerator) hAst426Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst426Code : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (-1) 0)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  hAst426Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst426Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst426Denominator)
    hAst426DenNonzero hAst426Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst427Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,3,11,46,-34,0,29,-46,-6,-3],[0,0,20,0,50,0,40,0,10],[-5,0,-20,0,-25,0,-10]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst427Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,40,0,120,0,120,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst427Raw : RationalCode Source.domain (fun z => (((Source.residue z.1 z.2 (-1) 0)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))) :=
  (hAst426Code.add hAst425Code)
private theorem hAst427DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst427Denominator=true := by kernel_decide
private theorem hAst427DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst427Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst427Denominator hAst427DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst427Cross : equalCheck
    (mul hAst427Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst427Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst427Numerator) hAst427Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst427Code : RationalCode Source.domain (fun z => (((Source.residue z.1 z.2 (-1) 0)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))) :=
  hAst427Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst427Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst427Denominator)
    hAst427DenNonzero hAst427Cross

/-- Article: proposed exact numerator for check05. -/
def check05Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,3,11,46,-34,0,29,-46,-6,-3],[0,0,20,0,50,0,40,0,10],[-5,0,-20,0,-25,0,-10]]
/-- Article: proposed positive denominator for check05. -/
def check05Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,40,0,120,0,120,0,40]]
/-- Article: composition of proved source-preserving rational operations. -/
def check05Raw : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (-1) 0)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))) :=
  (hAst427Code.congr (by
    intro z hz
    ring))
private theorem check05Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.residue z.1 z.2 (-1) 0)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))=((Source.residue z.1 z.2 (-1) 0)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1)))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check05DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check05Denominator=true := by kernel_decide
private theorem check05DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check05Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check05Denominator check05DenCheck hz.1 hz.2).ne'
private theorem check05Cross : equalCheck
    (mul check05Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check05Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check05Numerator) check05Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check05. -/
def check05Code : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (-1) 0)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))) :=
  (check05Raw.congr check05Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check05Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check05Denominator)
    check05DenNonzero check05Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst428Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,30,-8,80,-6,82,-8,32,-2],[0,4,-8,0,-20,-4,-16,0,-4],[1,4,2,10,0,8,-2,2,-1],[0],[0,0,-32,0,-96,0,-96,0,-32],[0],[0],[0],[0,0,16,0,48,0,48,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst428Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst428Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (-1) 1))) :=
  (hAst423Code.add hResidueLower1Code)
private theorem hAst428DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst428Denominator=true := by kernel_decide
private theorem hAst428DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst428Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst428Denominator hAst428DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst428Cross : equalCheck
    (mul hAst428Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst428Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst428Numerator) hAst428Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst428Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (-1) 1))) :=
  hAst428Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst428Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst428Denominator)
    hAst428DenNonzero hAst428Cross

/-- Article: proposed exact numerator for check06. -/
def check06Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,30,-8,80,-6,82,-8,32,-2],[0,4,-8,0,-20,-4,-16,0,-4],[1,4,2,10,0,8,-2,2,-1],[0],[0,0,-32,0,-96,0,-96,0,-32],[0],[0],[0],[0,0,16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for check06. -/
def check06Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check06Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 1))) :=
  (hAst428Code.congr (by
    intro z hz
    ring))
private theorem check06Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 1))=((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 1)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check06DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check06Denominator=true := by kernel_decide
private theorem check06DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check06Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check06Denominator check06DenCheck hz.1 hz.2).ne'
private theorem check06Cross : equalCheck
    (mul check06Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check06Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check06Numerator) check06Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check06. -/
def check06Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 1))) :=
  (check06Raw.congr check06Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check06Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check06Denominator)
    check06DenNonzero check06Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst429Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,46,-54,126,-95,114,-66,34,-8],[10,0,0,0,-10],[10,0,25,0,20,0,5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst429Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,40,0,120,0,120,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst429Raw : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (-1) 1)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  (hResidueLower1Code.add hAst420Code)
private theorem hAst429DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst429Denominator=true := by kernel_decide
private theorem hAst429DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst429Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst429Denominator hAst429DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst429Cross : equalCheck
    (mul hAst429Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst429Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst429Numerator) hAst429Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst429Code : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (-1) 1)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  hAst429Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst429Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst429Denominator)
    hAst429DenNonzero hAst429Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst430Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,46,26,46,-15,114,-66,34,-8],[10,0,0,0,-10],[10,0,25,0,20,0,5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst430Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,40,0,120,0,120,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst430Raw : RationalCode Source.domain (fun z => (((Source.residue z.1 z.2 (-1) 1)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))) :=
  (hAst429Code.add hAst425Code)
private theorem hAst430DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst430Denominator=true := by kernel_decide
private theorem hAst430DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst430Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst430Denominator hAst430DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst430Cross : equalCheck
    (mul hAst430Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst430Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst430Numerator) hAst430Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst430Code : RationalCode Source.domain (fun z => (((Source.residue z.1 z.2 (-1) 1)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))) :=
  hAst430Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst430Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst430Denominator)
    hAst430DenNonzero hAst430Cross

/-- Article: proposed exact numerator for check07. -/
def check07Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,46,26,46,-15,114,-66,34,-8],[10,0,0,0,-10],[10,0,25,0,20,0,5]]
/-- Article: proposed positive denominator for check07. -/
def check07Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,40,0,120,0,120,0,40]]
/-- Article: composition of proved source-preserving rational operations. -/
def check07Raw : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (-1) 1)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))) :=
  (hAst430Code.congr (by
    intro z hz
    ring))
private theorem check07Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.residue z.1 z.2 (-1) 1)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))=((Source.residue z.1 z.2 (-1) 1)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1)))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check07DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check07Denominator=true := by kernel_decide
private theorem check07DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check07Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check07Denominator check07DenCheck hz.1 hz.2).ne'
private theorem check07Cross : equalCheck
    (mul check07Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check07Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check07Numerator) check07Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check07. -/
def check07Code : RationalCode Source.domain (fun z => ((Source.residue z.1 z.2 (-1) 1)+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))+(((2 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))) :=
  (check07Raw.congr check07Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check07Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check07Denominator)
    check07DenNonzero check07Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst431Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,12,0,76,0,112,0,84,0,20],[0,0,-24,0,-56,0,-64,0,-40,0,-8],[3,0,5,0,0,0,-4,0,-3,0,-1],[0],[0,0,-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[0,0,16,0,64,0,96,0,64,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst431Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,64,0,96,0,64,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst431Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (-1) 2))) :=
  (hAst423Code.add hResidueLower2Code)
private theorem hAst431DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst431Denominator=true := by kernel_decide
private theorem hAst431DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst431Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst431Denominator hAst431DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst431Cross : equalCheck
    (mul hAst431Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst431Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst431Numerator) hAst431Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst431Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (-1) 2))) :=
  hAst431Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst431Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst431Denominator)
    hAst431DenNonzero hAst431Cross

/-- Article: proposed exact numerator for check08. -/
def check08Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,12,0,76,0,112,0,84,0,20],[0,0,-24,0,-56,0,-64,0,-40,0,-8],[3,0,5,0,0,0,-4,0,-3,0,-1],[0],[0,0,-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[0,0,16,0,64,0,96,0,64,0,16]]
/-- Article: proposed positive denominator for check08. -/
def check08Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,64,0,96,0,64,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check08Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 2))) :=
  (hAst431Code.congr (by
    intro z hz
    ring))
private theorem check08Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 2))=((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 2)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check08DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check08Denominator=true := by kernel_decide
private theorem check08DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check08Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check08Denominator check08DenCheck hz.1 hz.2).ne'
private theorem check08Cross : equalCheck
    (mul check08Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check08Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check08Numerator) check08Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check08. -/
def check08Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 2))) :=
  (check08Raw.congr check08Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check08Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check08Denominator)
    check08DenNonzero check08Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst432Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,-3,-11,-49,63,-126,115,-114,97,-31,16,3],[0,0,-40,0,-70,0,-70,0,-50,0,-10],[5,0,5,0,-5,0,-5]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst432Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,40,0,160,0,240,0,160,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst432Raw : RationalCode Source.domain (fun z => ((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2))) :=
  (hEpsilonCode.add hResidueLower2Code)
private theorem hAst432DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst432Denominator=true := by kernel_decide
private theorem hAst432DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst432Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst432Denominator hAst432DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst432Cross : equalCheck
    (mul hAst432Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst432Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst432Numerator) hAst432Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst432Code : RationalCode Source.domain (fun z => ((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2))) :=
  hAst432Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst432Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst432Denominator)
    hAst432DenNonzero hAst432Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst433Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,9,66,415,700,1771,-4092,14471,-25220,39590,-52264,56843,-56204,44840,-32900,19401,-8972,3381,-410,70,96,9],[0,0,0,240,880,4340,-3500,17360,-16480,33920,-31580,41040,-37040,33640,-28580,17840,-14240,4960,-3540,320,-320,-60],[0,-30,-110,-520,2120,-1720,7490,-1880,12100,300,13150,2120,10740,1480,7270,280,3740,-30,1000,0,100],[0,0,-400,0,-1100,0,-1000,0,-100,0,800,0,1100,0,600,0,100],[25,0,50,0,-25,0,-100,0,-25,0,50,0,25]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst433Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1600,0,12800,0,44800,0,89600,0,112000,0,89600,0,44800,0,12800,0,1600]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst433Raw : RationalCode Source.domain (fun z => (((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2)))^2) :=
  (hAst432Code.pow 2)
private theorem hAst433DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst433Denominator=true := by kernel_decide
private theorem hAst433DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst433Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst433Denominator hAst433DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst433Cross : equalCheck
    (mul hAst433Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst433Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst433Numerator) hAst433Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst433Code : RationalCode Source.domain (fun z => (((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2)))^2) :=
  hAst433Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst433Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst433Denominator)
    hAst433DenNonzero hAst433Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst434Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-9,-66,-415,-700,-1771,4092,-14471,25220,-39590,52264,-56843,56204,-44840,32900,-19401,8972,-3381,410,-70,-96,-9],[0,0,0,-240,-880,-4340,3500,-17360,16480,-33920,31580,-41040,37040,-33640,28580,-17840,14240,-4960,3540,-320,320,60],[0,30,110,520,-2120,1720,-7490,1880,-12100,-300,-13150,-2120,-10740,-1480,-7270,-280,-3740,30,-1000,0,-100],[0,0,400,0,1100,0,1000,0,100,0,-800,0,-1100,0,-600,0,-100],[-25,0,-50,0,25,0,100,0,25,0,-50,0,-25]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst434Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1600,0,12800,0,44800,0,89600,0,112000,0,89600,0,44800,0,12800,0,1600]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst434Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2)))^2)) :=
  ((RationalCode.constant Source.domain (-1)).mul hAst433Code)
private theorem hAst434DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst434Denominator=true := by kernel_decide
private theorem hAst434DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst434Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst434Denominator hAst434DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst434Cross : equalCheck
    (mul hAst434Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst434Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst434Numerator) hAst434Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst434Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2)))^2)) :=
  hAst434Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst434Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst434Denominator)
    hAst434DenNonzero hAst434Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst435Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,6,0,-6,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst435Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,10,0,10]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst435Raw : RationalCode Source.domain (fun z => ((((-4) : ℚ) : ℝ)*(phaseBudget z.1))) :=
  ((RationalCode.constant Source.domain (-4)).mul hEpsilonCode)
private theorem hAst435DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst435Denominator=true := by kernel_decide
private theorem hAst435DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst435Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst435Denominator hAst435DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst435Cross : equalCheck
    (mul hAst435Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst435Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst435Numerator) hAst435Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst435Code : RationalCode Source.domain (fun z => ((((-4) : ℚ) : ℝ)*(phaseBudget z.1))) :=
  hAst435Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst435Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst435Denominator)
    hAst435DenNonzero hAst435Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst436Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,4,-4,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst436Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst436Raw : RationalCode Source.domain (fun z => (((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1)))) :=
  ((RationalCode.constant Source.domain 4).mul hQuadraticLowerCode)
private theorem hAst436DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst436Denominator=true := by kernel_decide
private theorem hAst436DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst436Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst436Denominator hAst436DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst436Cross : equalCheck
    (mul hAst436Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst436Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst436Numerator) hAst436Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst436Code : RationalCode Source.domain (fun z => (((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1)))) :=
  hAst436Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst436Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst436Denominator)
    hAst436DenNonzero hAst436Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst437Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,6,46,-34,40,-6,-6,-6,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst437Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,10,0,30,0,30,0,10]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst437Raw : RationalCode Source.domain (fun z => (((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))) :=
  (hAst435Code.add hAst436Code)
private theorem hAst437DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst437Denominator=true := by kernel_decide
private theorem hAst437DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst437Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst437Denominator hAst437DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst437Cross : equalCheck
    (mul hAst437Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst437Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst437Numerator) hAst437Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst437Code : RationalCode Source.domain (fun z => (((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))) :=
  hAst437Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst437Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst437Denominator)
    hAst437DenNonzero hAst437Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst438Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,42,84,788,-140,2966,-728,3000,-56,1126,-492,100,-444,-294,-144,-48],[0,0,-24,-48,-428,152,-1288,632,-1500,688,-680,352,-4,120,72,24,12],[3,6,52,-22,132,-74,68,-30,-110,50,-132,46,-28,18,12,6,3],[0],[0,0,-96,-192,-1760,512,-5984,2880,-8160,3840,-4640,2240,-416,768,480,192,96],[0],[0],[0],[0,0,48,96,880,-256,2992,-1440,4080,-1920,2320,-1120,208,-384,-240,-96,-48]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst438Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,160,0,960,0,2400,0,3200,0,2400,0,960,0,160]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst438Raw : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1)))))) :=
  (hAst415Code.mul hAst437Code)
private theorem hAst438DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst438Denominator=true := by kernel_decide
private theorem hAst438DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst438Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst438Denominator hAst438DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst438Cross : equalCheck
    (mul hAst438Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst438Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst438Numerator) hAst438Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst438Code : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1)))))) :=
  hAst438Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst438Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst438Denominator)
    hAst438DenNonzero hAst438Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst439Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-9,354,425,8020,-1491,49932,-23711,122420,-56110,153184,-70163,109724,-59680,43220,-34641,3612,-10701,-3490,-1510,-576,-9],[0,0,0,-480,-1360,-9100,4060,-39040,25360,-78960,52620,-90720,60640,-62280,43700,-24000,20400,-3440,5220,640,560,180],[0,60,170,1100,-2220,4110,-8610,5720,-14100,1280,-13990,-4960,-9580,-5500,-5670,-2040,-2860,20,-700,180,-40,30],[0,0,400,0,1100,0,1000,0,100,0,-800,0,-1100,0,-600,0,-100],[-25,0,-50,-960,-1895,-19520,1380,-96000,37145,-218880,101070,-269440,127975,-178560,90880,-49920,39680,6400,11520,6720,1920,960],[0],[0],[0],[0,0,0,480,960,9760,-640,48000,-18560,109440,-50560,134720,-64000,89280,-45440,24960,-19840,-3200,-5760,-3360,-960,-480]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst439Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1600,0,12800,0,44800,0,89600,0,112000,0,89600,0,44800,0,12800,0,1600]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst439Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2)))^2)+(((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))))) :=
  (hAst434Code.add hAst438Code)
private theorem hAst439DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst439Denominator=true := by kernel_decide
private theorem hAst439DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst439Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst439Denominator hAst439DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst439Cross : equalCheck
    (mul hAst439Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst439Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst439Numerator) hAst439Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst439Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2)))^2)+(((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))))) :=
  hAst439Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst439Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst439Denominator)
    hAst439DenNonzero hAst439Cross

/-- Article: proposed exact numerator for check09. -/
def check09Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-9,354,425,8020,-1491,49932,-23711,122420,-56110,153184,-70163,109724,-59680,43220,-34641,3612,-10701,-3490,-1510,-576,-9],[0,0,0,-480,-1360,-9100,4060,-39040,25360,-78960,52620,-90720,60640,-62280,43700,-24000,20400,-3440,5220,640,560,180],[0,60,170,1100,-2220,4110,-8610,5720,-14100,1280,-13990,-4960,-9580,-5500,-5670,-2040,-2860,20,-700,180,-40,30],[0,0,400,0,1100,0,1000,0,100,0,-800,0,-1100,0,-600,0,-100],[-25,0,-50,-960,-1895,-19520,1380,-96000,37145,-218880,101070,-269440,127975,-178560,90880,-49920,39680,6400,11520,6720,1920,960],[0],[0],[0],[0,0,0,480,960,9760,-640,48000,-18560,109440,-50560,134720,-64000,89280,-45440,24960,-19840,-3200,-5760,-3360,-960,-480]]
/-- Article: proposed positive denominator for check09. -/
def check09Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1600,0,12800,0,44800,0,89600,0,112000,0,89600,0,44800,0,12800,0,1600]]
/-- Article: composition of proved source-preserving rational operations. -/
def check09Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2)))^2)+(((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))))) :=
  (hAst439Code.congr (by
    intro z hz
    ring))
private theorem check09Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2)))^2)+(((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))))=(((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2)))^2)+(((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1)))))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check09DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check09Denominator=true := by kernel_decide
private theorem check09DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check09Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check09Denominator check09DenCheck hz.1 hz.2).ne'
private theorem check09Cross : equalCheck
    (mul check09Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check09Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check09Numerator) check09Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check09. -/
def check09Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(((phaseBudget z.1)+(Source.residue z.1 z.2 (-1) 2)))^2)+(((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))*(((((-4) : ℚ) : ℝ)*(phaseBudget z.1))+(((4 : ℚ) : ℝ)*(Source.quadratic z.1 (-1))))))) :=
  (check09Raw.congr check09Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check09Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check09Denominator)
    check09DenNonzero check09Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst440Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,-2,3,-2,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst440Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst440Raw : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (-1)))^2) :=
  (hQuadraticLowerCode.pow 2)
private theorem hAst440DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst440Denominator=true := by kernel_decide
private theorem hAst440DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst440Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst440Denominator hAst440DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst440Cross : equalCheck
    (mul hAst440Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst440Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst440Numerator) hAst440Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst440Code : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (-1)))^2) :=
  hAst440Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst440Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst440Denominator)
    hAst440DenNonzero hAst440Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst441Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst441Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst441Raw : RationalCode Source.domain (fun z => (z.1)^20) :=
  ((RationalCode.first Source.domain).pow 20)
private theorem hAst441DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst441Denominator=true := by kernel_decide
private theorem hAst441DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst441Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst441Denominator hAst441DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst441Cross : equalCheck
    (mul hAst441Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst441Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst441Numerator) hAst441Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst441Code : RationalCode Source.domain (fun z => (z.1)^20) :=
  hAst441Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst441Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst441Denominator)
    hAst441DenNonzero hAst441Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst442Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,4,-8,12,-8,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst442Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst442Raw : RationalCode Source.domain (fun z => (((4 : ℚ) : ℝ)*((Source.quadratic z.1 (-1)))^2)) :=
  ((RationalCode.constant Source.domain 4).mul hAst440Code)
private theorem hAst442DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst442Denominator=true := by kernel_decide
private theorem hAst442DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst442Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst442Denominator hAst442DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst442Cross : equalCheck
    (mul hAst442Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst442Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst442Numerator) hAst442Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst442Code : RationalCode Source.domain (fun z => (((4 : ℚ) : ℝ)*((Source.quadratic z.1 (-1)))^2)) :=
  hAst442Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst442Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst442Denominator)
    hAst442DenNonzero hAst442Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst443Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,-8,12,-8,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst443Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst443Raw : RationalCode Source.domain (fun z => ((((4 : ℚ) : ℝ)*((Source.quadratic z.1 (-1)))^2)*(z.1)^20)) :=
  (hAst442Code.mul hAst441Code)
private theorem hAst443DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst443Denominator=true := by kernel_decide
private theorem hAst443DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst443Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst443Denominator hAst443DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst443Cross : equalCheck
    (mul hAst443Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst443Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst443Numerator) hAst443Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst443Code : RationalCode Source.domain (fun z => ((((4 : ℚ) : ℝ)*((Source.quadratic z.1 (-1)))^2)*(z.1)^20)) :=
  hAst443Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst443Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst443Denominator)
    hAst443DenNonzero hAst443Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst444Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-65,192,-521,880,-1423,1680,-1943,1696,-1463,928,-575,240,-89,16,-1,0,0,0,0,0,0,0,256,-512,768,-512,256],[0,0,0,-32,36,-96,96,-64,92,64,64,96,60,32,32,0,4],[0,0,-2,-32,10,-176,54,-400,82,-480,50,-320,6,-112,-6,-16,-2],[0,0,4,0,32,0,92,0,128,0,92,0,32,0,4],[-1,0,-9,0,-31,0,-55,0,-55,0,-31,0,-9,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst444Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,384,0,960,0,1280,0,960,0,384,0,64]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst444Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))+((((4 : ℚ) : ℝ)*((Source.quadratic z.1 (-1)))^2)*(z.1)^20))) :=
  (hAst417Code.add hAst443Code)
private theorem hAst444DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst444Denominator=true := by kernel_decide
private theorem hAst444DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst444Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst444Denominator hAst444DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst444Cross : equalCheck
    (mul hAst444Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst444Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst444Numerator) hAst444Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst444Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))+((((4 : ℚ) : ℝ)*((Source.quadratic z.1 (-1)))^2)*(z.1)^20))) :=
  hAst444Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst444Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst444Denominator)
    hAst444DenNonzero hAst444Cross

/-- Article: proposed exact numerator for check10. -/
def check10Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-65,192,-521,880,-1423,1680,-1943,1696,-1463,928,-575,240,-89,16,-1,0,0,0,0,0,0,0,256,-512,768,-512,256],[0,0,0,-32,36,-96,96,-64,92,64,64,96,60,32,32,0,4],[0,0,-2,-32,10,-176,54,-400,82,-480,50,-320,6,-112,-6,-16,-2],[0,0,4,0,32,0,92,0,128,0,92,0,32,0,4],[-1,0,-9,0,-31,0,-55,0,-55,0,-31,0,-9,0,-1]]
/-- Article: proposed positive denominator for check10. -/
def check10Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,384,0,960,0,1280,0,960,0,384,0,64]]
/-- Article: composition of proved source-preserving rational operations. -/
def check10Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))+(((4 : ℚ) : ℝ)*((Source.quadratic z.1 (-1)))^2*(z.1)^20))) :=
  (hAst444Code.congr (by
    intro z hz
    ring))
private theorem check10Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))+(((4 : ℚ) : ℝ)*((Source.quadratic z.1 (-1)))^2*(z.1)^20))=(((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))+(((4 : ℚ) : ℝ)*((Source.quadratic z.1 (-1)))^2*(z.1)^20)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check10DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check10Denominator=true := by kernel_decide
private theorem check10DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check10Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check10Denominator check10DenCheck hz.1 hz.2).ne'
private theorem check10Cross : equalCheck
    (mul check10Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check10Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check10Numerator) check10Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check10. -/
def check10Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))+(((4 : ℚ) : ℝ)*((Source.quadratic z.1 (-1)))^2*(z.1)^20))) :=
  (check10Raw.congr check10Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check10Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check10Denominator)
    check10DenNonzero check10Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst445Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst445Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,3,0,3,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst445Raw : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (-1))*(z.1)^20)) :=
  (hQuadraticLowerCode.mul hAst441Code)
private theorem hAst445DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst445Denominator=true := by kernel_decide
private theorem hAst445DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst445Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst445Denominator hAst445DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst445Cross : equalCheck
    (mul hAst445Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst445Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst445Numerator) hAst445Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst445Code : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (-1))*(z.1)^20)) :=
  hAst445Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst445Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst445Denominator)
    hAst445DenNonzero hAst445Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst446Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,0,34,16,0,0,16,0,-16,0,16,0,-16,0,16,0,-16,0,16,0,-16,16],[0,0,-8,0,-12,0,-4],[1,0,1,0,-1,0,-1],[0],[0,0,-32,0,-64,0,-32],[0],[0],[0],[0,0,16,0,32,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst446Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,32,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst446Raw : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))+((Source.quadratic z.1 (-1))*(z.1)^20))) :=
  (hAst415Code.add hAst445Code)
private theorem hAst446DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst446Denominator=true := by kernel_decide
private theorem hAst446DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst446Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst446Denominator hAst446DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst446Cross : equalCheck
    (mul hAst446Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst446Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst446Numerator) hAst446Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst446Code : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))+((Source.quadratic z.1 (-1))*(z.1)^20))) :=
  hAst446Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst446Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst446Denominator)
    hAst446DenNonzero hAst446Cross

/-- Article: proposed exact numerator for check11. -/
def check11Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,0,34,16,0,0,16,0,-16,0,16,0,-16,0,16,0,-16,0,16,0,-16,16],[0,0,-8,0,-12,0,-4],[1,0,1,0,-1,0,-1],[0],[0,0,-32,0,-64,0,-32],[0],[0],[0],[0,0,16,0,32,0,16]]
/-- Article: proposed positive denominator for check11. -/
def check11Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,32,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check11Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)+((Source.quadratic z.1 (-1))*(z.1)^20))) :=
  (hAst446Code.congr (by
    intro z hz
    ring))
private theorem check11Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)+((Source.quadratic z.1 (-1))*(z.1)^20))=((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)+((Source.quadratic z.1 (-1))*(z.1)^20)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check11DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check11Denominator=true := by kernel_decide
private theorem check11DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check11Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check11Denominator check11DenCheck hz.1 hz.2).ne'
private theorem check11Cross : equalCheck
    (mul check11Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check11Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check11Numerator) check11Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check11. -/
def check11Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)+((Source.quadratic z.1 (-1))*(z.1)^20))) :=
  (check11Raw.congr check11Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check11Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check11Denominator)
    check11DenNonzero check11Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst447Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,196,0,952,448,1156,1088,704,0,640,512,-640,-512,896,512,-1152,-512,1408,512,-1664,-512,1920,960,-2624,576,2304,0,-2048,512,1792,-512,-1536,512,1280,-512,-1024,512,768,-512,-512,512,256,-512,256],[0,0,0,0,-224,0,-880,-256,-928,-384,-528,-128,-128,0,0,0,0,0,0,0,0,0,0,0,0,-256,256,-384,128,-128],[0,0,28,0,160,32,232,32,144,-32,28,-32,-16,0,0,0,0,0,0,0,0,0,0,32,-32,32,0,-32,32,-32],[0,0,-16,0,-40,0,-16,0,32,0,32,0,8],[1,0,2,0,-897,0,-3972,-1024,-5249,-2048,-3198,-1024,-1023,0,0,0,0,0,0,0,0,0,0,0,0,-1024,1024,-2048,1024,-1024],[0,0,0,0,512,0,1792,0,2304,0,1280,0,256],[0,0,-64,0,-192,0,-128,0,128,0,192,0,64],[0],[0,0,0,0,1472,0,6080,512,8768,1024,5696,512,1536,0,0,0,0,0,0,0,0,0,0,0,0,512,-512,1024,-512,512],[0,0,0,0,-256,0,-896,0,-1152,0,-640,0,-128],[0,0,32,0,96,0,64,0,-64,0,-96,0,-32],[0],[0,0,0,0,-1024,0,-4096,0,-6144,0,-4096,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst447Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst447Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))+((Source.quadratic z.1 (-1))*(z.1)^20)))^2) :=
  (hAst446Code.pow 2)
private theorem hAst447DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst447Denominator=true := by kernel_decide
private theorem hAst447DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst447Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst447Denominator hAst447DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst447Cross : equalCheck
    (mul hAst447Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst447Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst447Numerator) hAst447Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst447Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))+((Source.quadratic z.1 (-1))*(z.1)^20)))^2) :=
  hAst447Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst447Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst447Denominator)
    hAst447DenNonzero hAst447Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst448Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-65,192,-391,496,-576,496,-400,208,-87,16,-1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-32,36,-32,24,32,8,32,24,0,4],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,-32,14,-112,28,-144,12,-80,-2,-16,-2],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,24,0,40,0,24,0,4],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,-7,0,-16,0,-16,0,-7,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst448Denominator : polyak.Numerics.IntegerBivariate.Source := [[64,0,256,0,384,0,256,0,64]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst448Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))*(z.1)^20)) :=
  (hAst417Code.mul hAst441Code)
private theorem hAst448DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst448Denominator=true := by kernel_decide
private theorem hAst448DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst448Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst448Denominator hAst448DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst448Cross : equalCheck
    (mul hAst448Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst448Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst448Numerator) hAst448Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst448Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))*(z.1)^20)) :=
  hAst448Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst448Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst448Denominator)
    hAst448DenNonzero hAst448Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst449Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,196,0,952,448,1156,1088,704,0,640,512,-640,-512,896,512,-1152,-512,1408,512,-1664,-512,1660,1728,-4188,2560,0,1984,-3648,1344,1444,-448,-1540,512,1280,-512,-1024,512,768,-512,-512,512,256,-512,256],[0,0,0,0,-224,0,-880,-256,-928,-384,-528,-128,-128,0,0,0,0,0,0,0,0,0,0,-128,144,-384,352,-256,160,0,96,0,16],[0,0,28,0,160,32,232,32,144,-32,28,-32,-16,0,0,0,0,0,0,0,0,0,-8,-96,24,-416,112,-608,80,-352,-8,-64,-8],[0,0,-16,0,-40,0,-16,0,32,0,32,0,8,0,0,0,0,0,0,0,0,0,16,0,96,0,160,0,96,0,16],[1,0,2,0,-897,0,-3972,-1024,-5249,-2048,-3198,-1024,-1023,0,0,0,0,0,0,0,-4,0,-28,0,-64,-1024,960,-2048,996,-1024,-4],[0,0,0,0,512,0,1792,0,2304,0,1280,0,256],[0,0,-64,0,-192,0,-128,0,128,0,192,0,64],[0],[0,0,0,0,1472,0,6080,512,8768,1024,5696,512,1536,0,0,0,0,0,0,0,0,0,0,0,0,512,-512,1024,-512,512],[0,0,0,0,-256,0,-896,0,-1152,0,-640,0,-128],[0,0,32,0,96,0,64,0,-64,0,-96,0,-32],[0],[0,0,0,0,-1024,0,-4096,0,-6144,0,-4096,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst449Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst449Raw : RationalCode Source.domain (fun z => (((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))+((Source.quadratic z.1 (-1))*(z.1)^20)))^2+(((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))*(z.1)^20))) :=
  (hAst447Code.add hAst448Code)
private theorem hAst449DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst449Denominator=true := by kernel_decide
private theorem hAst449DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst449Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst449Denominator hAst449DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst449Cross : equalCheck
    (mul hAst449Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst449Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst449Numerator) hAst449Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst449Code : RationalCode Source.domain (fun z => (((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))+((Source.quadratic z.1 (-1))*(z.1)^20)))^2+(((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))*(z.1)^20))) :=
  hAst449Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst449Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst449Denominator)
    hAst449DenNonzero hAst449Cross

/-- Article: proposed exact numerator for check12. -/
def check12Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,196,0,952,448,1156,1088,704,0,640,512,-640,-512,896,512,-1152,-512,1408,512,-1664,-512,1660,1728,-4188,2560,0,1984,-3648,1344,1444,-448,-1540,512,1280,-512,-1024,512,768,-512,-512,512,256,-512,256],[0,0,0,0,-224,0,-880,-256,-928,-384,-528,-128,-128,0,0,0,0,0,0,0,0,0,0,-128,144,-384,352,-256,160,0,96,0,16],[0,0,28,0,160,32,232,32,144,-32,28,-32,-16,0,0,0,0,0,0,0,0,0,-8,-96,24,-416,112,-608,80,-352,-8,-64,-8],[0,0,-16,0,-40,0,-16,0,32,0,32,0,8,0,0,0,0,0,0,0,0,0,16,0,96,0,160,0,96,0,16],[1,0,2,0,-897,0,-3972,-1024,-5249,-2048,-3198,-1024,-1023,0,0,0,0,0,0,0,-4,0,-28,0,-64,-1024,960,-2048,996,-1024,-4],[0,0,0,0,512,0,1792,0,2304,0,1280,0,256],[0,0,-64,0,-192,0,-128,0,128,0,192,0,64],[0],[0,0,0,0,1472,0,6080,512,8768,1024,5696,512,1536,0,0,0,0,0,0,0,0,0,0,0,0,512,-512,1024,-512,512],[0,0,0,0,-256,0,-896,0,-1152,0,-640,0,-128],[0,0,32,0,96,0,64,0,-64,0,-96,0,-32],[0],[0,0,0,0,-1024,0,-4096,0,-6144,0,-4096,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: proposed positive denominator for check12. -/
def check12Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: composition of proved source-preserving rational operations. -/
def check12Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)+((Source.quadratic z.1 (-1))*(z.1)^20)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))*(z.1)^20))) :=
  (hAst449Code.congr (by
    intro z hz
    ring))
private theorem check12Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)+((Source.quadratic z.1 (-1))*(z.1)^20)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))*(z.1)^20))=((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)+((Source.quadratic z.1 (-1))*(z.1)^20)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))*(z.1)^20)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check12DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check12Denominator=true := by kernel_decide
private theorem check12DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check12Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check12Denominator check12DenCheck hz.1 hz.2).ne'
private theorem check12Cross : equalCheck
    (mul check12Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check12Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check12Numerator) check12Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check12. -/
def check12Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)+((Source.quadratic z.1 (-1))*(z.1)^20)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))*(z.1)^20))) :=
  (check12Raw.congr check12Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check12Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check12Denominator)
    check12DenNonzero check12Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst450Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,16,32,16,50,0,16],[0,0,8,0,20,0,16,0,4],[1,0,2,0,0,0,-2,0,-1],[0],[0,0,-32,0,-96,0,-96,0,-32],[0],[0],[0],[0,0,16,0,48,0,48,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst450Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst450Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.reserve z.2))) :=
  (hConstantUpperCode.add hReserveCode)
private theorem hAst450DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst450Denominator=true := by kernel_decide
private theorem hAst450DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst450Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst450Denominator hAst450DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst450Cross : equalCheck
    (mul hAst450Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst450Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst450Numerator) hAst450Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst450Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.reserve z.2))) :=
  hAst450Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst450Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst450Denominator)
    hAst450DenNonzero hAst450Cross

/-- Article: proposed exact numerator for check13. -/
def check13Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,16,32,16,50,0,16],[0,0,8,0,20,0,16,0,4],[1,0,2,0,0,0,-2,0,-1],[0],[0,0,-32,0,-96,0,-96,0,-32],[0],[0],[0],[0,0,16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for check13. -/
def check13Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check13Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.reserve z.2))) :=
  (hAst450Code.congr (by
    intro z hz
    ring))
private theorem check13Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.constant z.1 z.2 (1))+(Source.reserve z.2))=((Source.constant z.1 z.2 (1))+(Source.reserve z.2)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check13DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check13Denominator=true := by kernel_decide
private theorem check13DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check13Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check13Denominator check13DenCheck hz.1 hz.2).ne'
private theorem check13Cross : equalCheck
    (mul check13Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check13Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check13Numerator) check13Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check13. -/
def check13Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (1))+(Source.reserve z.2))) :=
  (check13Raw.congr check13Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check13Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check13Denominator)
    check13DenNonzero check13Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst451Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,196,448,1152,1472,2936,2624,3904,2112,3524,512,1600,0,256],[0,0,0,0,224,256,1072,896,2528,1152,3392,640,2496,128,912,0,128],[0,0,28,32,184,96,548,64,832,-64,612,-96,152,-32,-36,0,-16],[0,0,16,0,72,0,112,0,40,0,-80,0,-104,0,-48,0,-8],[1,0,4,0,-892,-1024,-4740,-4096,-12042,-6144,-17668,-4096,-14716,-1024,-6268,0,-1023],[0,0,0,0,-512,0,-2816,0,-6400,0,-7680,0,-5120,0,-1792,0,-256],[0,0,-64,0,-320,0,-576,0,-320,0,320,0,576,0,320,0,64],[0],[0,0,0,0,1472,512,8512,2048,21376,3072,29312,2048,22720,512,9280,0,1536],[0,0,0,0,256,0,1408,0,3200,0,3840,0,2560,0,896,0,128],[0,0,32,0,160,0,288,0,160,0,-160,0,-288,0,-160,0,-32],[0],[0,0,0,0,-1024,0,-6144,0,-15360,0,-20480,0,-15360,0,-6144,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst451Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst451Raw : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (1))+(Source.reserve z.2)))^2) :=
  (hAst450Code.pow 2)
private theorem hAst451DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst451Denominator=true := by kernel_decide
private theorem hAst451DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst451Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst451Denominator hAst451DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst451Cross : equalCheck
    (mul hAst451Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst451Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst451Numerator) hAst451Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst451Code : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (1))+(Source.reserve z.2)))^2) :=
  hAst451Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst451Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst451Denominator)
    hAst451DenNonzero hAst451Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst452Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-65,96,-230,176,-218,64,-54,-16,-1],[0,0,0,-32,28,-128,76,-160,44,-64,-4],[0,0,-2,0,-16,-16,-20,0,-32,16,-2],[0,0,-4,0,-20,0,-20,0,-4],[-1,0,-6,0,-10,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst452Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,192,0,192,0,64]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst452Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))) :=
  ((RationalCode.constant Source.domain (-1)).mul hBetaNormUpperCode)
private theorem hAst452DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst452Denominator=true := by kernel_decide
private theorem hAst452DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst452Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst452Denominator hAst452DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst452Cross : equalCheck
    (mul hAst452Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst452Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst452Numerator) hAst452Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst452Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))) :=
  hAst452Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst452Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst452Denominator)
    hAst452DenNonzero hAst452Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst453Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-64,832,-548,3328,-1476,6144,-1948,5312,-664,1792,68,64,28,-64,-4],[0,0,0,-128,336,-640,1712,-1664,3952,-2688,4928,-2560,3280,-1280,1040,-256,112],[0,0,20,32,96,32,252,-128,264,-192,-84,32,-336,160,-188,64,-24],[0,0,0,0,-56,0,-256,0,-472,0,-448,0,-232,0,-64,0,-8],[-3,0,-32,0,-1016,-1024,-4960,-4096,-12262,-6144,-17792,-4096,-14752,-1024,-6272,0,-1023],[0,0,0,0,-512,0,-2816,0,-6400,0,-7680,0,-5120,0,-1792,0,-256],[0,0,-64,0,-320,0,-576,0,-320,0,320,0,576,0,320,0,64],[0],[0,0,0,0,1472,512,8512,2048,21376,3072,29312,2048,22720,512,9280,0,1536],[0,0,0,0,256,0,1408,0,3200,0,3840,0,2560,0,896,0,128],[0,0,32,0,160,0,288,0,160,0,-160,0,-288,0,-160,0,-32],[0],[0,0,0,0,-1024,0,-6144,0,-15360,0,-20480,0,-15360,0,-6144,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst453Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst453Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))))) :=
  (hAst451Code.add hAst452Code)
private theorem hAst453DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst453Denominator=true := by kernel_decide
private theorem hAst453DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst453Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst453Denominator hAst453DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst453Cross : equalCheck
    (mul hAst453Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst453Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst453Numerator) hAst453Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst453Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))))) :=
  hAst453Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst453Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst453Denominator)
    hAst453DenNonzero hAst453Cross

/-- Article: proposed exact numerator for check14. -/
def check14Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-64,832,-548,3328,-1476,6144,-1948,5312,-664,1792,68,64,28,-64,-4],[0,0,0,-128,336,-640,1712,-1664,3952,-2688,4928,-2560,3280,-1280,1040,-256,112],[0,0,20,32,96,32,252,-128,264,-192,-84,32,-336,160,-188,64,-24],[0,0,0,0,-56,0,-256,0,-472,0,-448,0,-232,0,-64,0,-8],[-3,0,-32,0,-1016,-1024,-4960,-4096,-12262,-6144,-17792,-4096,-14752,-1024,-6272,0,-1023],[0,0,0,0,-512,0,-2816,0,-6400,0,-7680,0,-5120,0,-1792,0,-256],[0,0,-64,0,-320,0,-576,0,-320,0,320,0,576,0,320,0,64],[0],[0,0,0,0,1472,512,8512,2048,21376,3072,29312,2048,22720,512,9280,0,1536],[0,0,0,0,256,0,1408,0,3200,0,3840,0,2560,0,896,0,128],[0,0,32,0,160,0,288,0,160,0,-160,0,-288,0,-160,0,-32],[0],[0,0,0,0,-1024,0,-6144,0,-15360,0,-20480,0,-15360,0,-6144,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: proposed positive denominator for check14. -/
def check14Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: composition of proved source-preserving rational operations. -/
def check14Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))))) :=
  (hAst453Code.congr (by
    intro z hz
    ring))
private theorem check14Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((Source.constant z.1 z.2 (1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))))=((((Source.constant z.1 z.2 (1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check14DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check14Denominator=true := by kernel_decide
private theorem check14DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check14Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check14Denominator check14DenCheck hz.1 hz.2).ne'
private theorem check14Cross : equalCheck
    (mul check14Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check14Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check14Numerator) check14Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check14. -/
def check14Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))))) :=
  (check14Raw.congr check14Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check14Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check14Denominator)
    check14DenNonzero check14Cross

end
end polyak.Certificates.Startup.Codes
