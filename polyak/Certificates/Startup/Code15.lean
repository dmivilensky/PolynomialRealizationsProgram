import polyak.Certificates.Startup.Code14

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: canonical numerator for one arithmetic source node. -/
def hAst481Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,196,448,760,576,1220,1024,704,-512,896,512,-896,-512,1152,512,-1408,-512,1664,512,-1920,-512,2176,512,-2432,-64,2752,576,-3072,1024,2304,-512,-2048,512,1792,-512,-1536,512,1280,-512,-1024,512,768,-512,-512,512,256,-512,256],[0,0,0,0,224,256,624,384,1056,128,656,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,256,-256,384,-128,128],[0,0,28,32,128,32,264,-32,176,-32,-4,0,-16,0,0,0,0,0,0,0,0,0,0,0,0,32,-32,32,0,-32,32,-32],[0,0,16,0,40,0,16,0,-32,0,-32,0,-8],[1,0,2,0,-897,-1024,-2948,-2048,-5249,-1024,-4222,0,-1023,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1024,1024,-2048,1024,-1024],[0,0,0,0,-512,0,-1792,0,-2304,0,-1280,0,-256],[0,0,-64,0,-192,0,-128,0,128,0,192,0,64],[0],[0,0,0,0,1472,512,5568,1024,8768,512,6208,0,1536,0,0,0,0,0,0,0,0,0,0,0,0,0,0,512,-512,1024,-512,512],[0,0,0,0,256,0,896,0,1152,0,640,0,128],[0,0,32,0,96,0,64,0,-64,0,-96,0,-32],[0],[0,0,0,0,-1024,0,-4096,0,-6144,0,-4096,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst481Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst481Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.reserve z.2))+((Source.quadratic z.1 (1))*(z.1)^20)))^2) :=
  (hAst480Code.pow 2)
private theorem hAst481DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst481Denominator=true := by kernel_decide
private theorem hAst481DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst481Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst481Denominator hAst481DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst481Cross : equalCheck
    (mul hAst481Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst481Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst481Numerator) hAst481Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst481Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.reserve z.2))+((Source.quadratic z.1 (1))*(z.1)^20)))^2) :=
  hAst481Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst481Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst481Denominator)
    hAst481DenNonzero hAst481Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst482Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-65,96,-230,176,-218,64,-54,-16,-1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-32,28,-128,76,-160,44,-64,-4],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,-16,-16,-20,0,-32,16,-2],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-4,0,-20,0,-20,0,-4],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,-6,0,-10,0,-6,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst482Denominator : polyak.Numerics.IntegerBivariate.Source := [[64,0,192,0,192,0,64]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst482Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))*(z.1)^20)) :=
  (hAst452Code.mul hAst441Code)
private theorem hAst482DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst482Denominator=true := by kernel_decide
private theorem hAst482DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst482Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst482Denominator hAst482DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst482Cross : equalCheck
    (mul hAst482Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst482Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst482Numerator) hAst482Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst482Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))*(z.1)^20)) :=
  hAst482Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst482Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst482Denominator)
    hAst482DenNonzero hAst482Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst483Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,196,448,760,576,1220,1024,704,-512,896,512,-896,-512,1152,512,-1408,-512,1664,512,-1920,-512,1916,896,-3612,1024,960,1536,-4160,1216,2084,-576,-2052,512,1792,-512,-1536,512,1280,-512,-1024,512,768,-512,-512,512,256,-512,256],[0,0,0,0,224,256,624,384,1056,128,656,0,128,0,0,0,0,0,0,0,0,0,0,-128,112,-640,416,-896,224,-512,32,-128,-16],[0,0,28,32,128,32,264,-32,176,-32,-4,0,-16,0,0,0,0,0,0,0,0,0,-8,0,-72,-32,-176,-32,-208,32,-104,32,-8],[0,0,16,0,40,0,16,0,-32,0,-32,0,-8,0,0,0,0,0,0,0,0,0,-16,0,-96,0,-160,0,-96,0,-16],[1,0,2,0,-897,-1024,-2948,-2048,-5249,-1024,-4222,0,-1023,0,0,0,0,0,0,0,-4,0,-28,0,-64,0,-64,-1024,996,-2048,1020,-1024],[0,0,0,0,-512,0,-1792,0,-2304,0,-1280,0,-256],[0,0,-64,0,-192,0,-128,0,128,0,192,0,64],[0],[0,0,0,0,1472,512,5568,1024,8768,512,6208,0,1536,0,0,0,0,0,0,0,0,0,0,0,0,0,0,512,-512,1024,-512,512],[0,0,0,0,256,0,896,0,1152,0,640,0,128],[0,0,32,0,96,0,64,0,-64,0,-96,0,-32],[0],[0,0,0,0,-1024,0,-4096,0,-6144,0,-4096,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst483Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst483Raw : RationalCode Source.domain (fun z => (((((Source.constant z.1 z.2 (1))+(Source.reserve z.2))+((Source.quadratic z.1 (1))*(z.1)^20)))^2+(((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))*(z.1)^20))) :=
  (hAst481Code.add hAst482Code)
private theorem hAst483DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst483Denominator=true := by kernel_decide
private theorem hAst483DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst483Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst483Denominator hAst483DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst483Cross : equalCheck
    (mul hAst483Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst483Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst483Numerator) hAst483Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst483Code : RationalCode Source.domain (fun z => (((((Source.constant z.1 z.2 (1))+(Source.reserve z.2))+((Source.quadratic z.1 (1))*(z.1)^20)))^2+(((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1)))*(z.1)^20))) :=
  hAst483Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst483Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst483Denominator)
    hAst483DenNonzero hAst483Cross

/-- Article: proposed exact numerator for check25. -/
def check25Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,196,448,760,576,1220,1024,704,-512,896,512,-896,-512,1152,512,-1408,-512,1664,512,-1920,-512,1916,896,-3612,1024,960,1536,-4160,1216,2084,-576,-2052,512,1792,-512,-1536,512,1280,-512,-1024,512,768,-512,-512,512,256,-512,256],[0,0,0,0,224,256,624,384,1056,128,656,0,128,0,0,0,0,0,0,0,0,0,0,-128,112,-640,416,-896,224,-512,32,-128,-16],[0,0,28,32,128,32,264,-32,176,-32,-4,0,-16,0,0,0,0,0,0,0,0,0,-8,0,-72,-32,-176,-32,-208,32,-104,32,-8],[0,0,16,0,40,0,16,0,-32,0,-32,0,-8,0,0,0,0,0,0,0,0,0,-16,0,-96,0,-160,0,-96,0,-16],[1,0,2,0,-897,-1024,-2948,-2048,-5249,-1024,-4222,0,-1023,0,0,0,0,0,0,0,-4,0,-28,0,-64,0,-64,-1024,996,-2048,1020,-1024],[0,0,0,0,-512,0,-1792,0,-2304,0,-1280,0,-256],[0,0,-64,0,-192,0,-128,0,128,0,192,0,64],[0],[0,0,0,0,1472,512,5568,1024,8768,512,6208,0,1536,0,0,0,0,0,0,0,0,0,0,0,0,0,0,512,-512,1024,-512,512],[0,0,0,0,256,0,896,0,1152,0,640,0,128],[0,0,32,0,96,0,64,0,-64,0,-96,0,-32],[0],[0,0,0,0,-1024,0,-4096,0,-6144,0,-4096,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: proposed positive denominator for check25. -/
def check25Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]
/-- Article: composition of proved source-preserving rational operations. -/
def check25Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.reserve z.2)+((Source.quadratic z.1 (1))*(z.1)^20)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))*(z.1)^20))) :=
  (hAst483Code.congr (by
    intro z hz
    ring))
private theorem check25Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((Source.constant z.1 z.2 (1))+(Source.reserve z.2)+((Source.quadratic z.1 (1))*(z.1)^20)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))*(z.1)^20))=((((Source.constant z.1 z.2 (1))+(Source.reserve z.2)+((Source.quadratic z.1 (1))*(z.1)^20)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))*(z.1)^20)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check25DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check25Denominator=true := by kernel_decide
private theorem check25DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check25Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check25Denominator check25DenCheck hz.1 hz.2).ne'
private theorem check25Cross : equalCheck
    (mul check25Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check25Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check25Numerator) check25Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check25. -/
def check25Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (1))+(Source.reserve z.2)+((Source.quadratic z.1 (1))*(z.1)^20)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (1))*(z.1)^20))) :=
  (check25Raw.congr check25Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check25Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check25Denominator)
    check25DenNonzero check25Cross

/-- Article: proposed exact numerator for check26. -/
def check26Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-10,0,-6,0,-1],[0,0,8,0,16,0,16,0,8],[20,-8,80,8,72,8,48,-8,4],[-12,0,-36,0,-36,0,-12],[32,0,96,0,96,0,32],[0],[16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for check26. -/
def check26Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check26Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 1)) :=
  (hPairLower1Code.congr (by
    intro z hz
    ring))
private theorem check26Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (-1) 1)=(Source.pairSlack z.1 z.2 (-1) 1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check26DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check26Denominator=true := by kernel_decide
private theorem check26DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check26Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check26Denominator check26DenCheck hz.1 hz.2).ne'
private theorem check26Cross : equalCheck
    (mul check26Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check26Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check26Numerator) check26Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check26. -/
def check26Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 1)) :=
  (check26Raw.congr check26Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check26Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check26Denominator)
    check26DenNonzero check26Cross

/-- Article: proposed exact numerator for check27. -/
def check27Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-10,0,-6,0,-1],[0,0,-8,0,-16,0,-16,0,-8],[20,8,64,-8,104,-8,32,8,4],[12,0,36,0,36,0,12],[32,0,96,0,96,0,32],[0],[16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for check27. -/
def check27Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check27Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 1)) :=
  (hPairUpper1Code.congr (by
    intro z hz
    ring))
private theorem check27Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (1) 1)=(Source.pairSlack z.1 z.2 (1) 1) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check27DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check27Denominator=true := by kernel_decide
private theorem check27DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check27Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check27Denominator check27DenCheck hz.1 hz.2).ne'
private theorem check27Cross : equalCheck
    (mul check27Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check27Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check27Numerator) check27Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check27. -/
def check27Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 1)) :=
  (check27Raw.congr check27Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check27Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check27Denominator)
    check27DenNonzero check27Cross

/-- Article: proposed exact numerator for check28. -/
def check28Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-6,0,-6,0,-5,0,-1],[0,0,0,0,-16,0,-16,0,-16],[20,-8,80,0,82,16,46,0,38,-8,6],[-8,0,-20,0,-12,0,-4,0,-4],[31,0,90,0,86,0,26,0,-1],[0],[16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for check28. -/
def check28Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check28Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 2)) :=
  (hPairLower2Code.congr (by
    intro z hz
    ring))
private theorem check28Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (-1) 2)=(Source.pairSlack z.1 z.2 (-1) 2) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check28DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check28Denominator=true := by kernel_decide
private theorem check28DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check28Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check28Denominator check28DenCheck hz.1 hz.2).ne'
private theorem check28Cross : equalCheck
    (mul check28Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check28Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check28Numerator) check28Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check28. -/
def check28Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 2)) :=
  (check28Raw.congr check28Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check28Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check28Denominator)
    check28DenNonzero check28Cross

/-- Article: proposed exact numerator for check29. -/
def check29Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-6,0,-6,0,-5,0,-1],[0,0,0,0,16,0,16,0,16],[20,8,64,0,98,-16,62,0,22,8,6],[8,0,20,0,12,0,4,0,4],[31,0,90,0,86,0,26,0,-1],[0],[16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for check29. -/
def check29Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check29Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 2)) :=
  (hPairUpper2Code.congr (by
    intro z hz
    ring))
private theorem check29Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (1) 2)=(Source.pairSlack z.1 z.2 (1) 2) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check29DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check29Denominator=true := by kernel_decide
private theorem check29DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check29Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check29Denominator check29DenCheck hz.1 hz.2).ne'
private theorem check29Cross : equalCheck
    (mul check29Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check29Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check29Numerator) check29Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check29. -/
def check29Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 2)) :=
  (check29Raw.congr check29Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check29Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check29Denominator)
    check29DenNonzero check29Cross

/-- Article: proposed exact numerator for check30. -/
def check30Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,0,0,5,0,5,0,0,0,-4,0,-1],[0,0,0,0,-8,0,8,0,0,0,8,0,-8],[20,-8,90,-8,102,8,30,16,-16,8,-6,-8,30,-8,6],[-8,0,-24,0,-16,0,8,0,24,0,16],[-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1],[0],[-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: proposed positive denominator for check30. -/
def check30Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check30Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 3)) :=
  (hPairLower3Code.congr (by
    intro z hz
    ring))
private theorem check30Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (-1) 3)=(Source.pairSlack z.1 z.2 (-1) 3) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check30DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check30Denominator=true := by kernel_decide
private theorem check30DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check30Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check30Denominator check30DenCheck hz.1 hz.2).ne'
private theorem check30Cross : equalCheck
    (mul check30Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check30Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check30Numerator) check30Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check30. -/
def check30Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 3)) :=
  (check30Raw.congr check30Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check30Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check30Denominator)
    check30DenNonzero check30Cross

/-- Article: proposed exact numerator for check31. -/
def check31Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-4,0,0,0,5,0,5,0,0,0,-4,0,-1],[0,0,0,0,8,0,-8,0,0,0,-8,0,8],[20,8,74,8,102,-8,46,-16,0,-8,-6,8,14,8,6],[8,0,24,0,16,0,-8,0,-24,0,-16],[-1,0,-6,0,-11,0,-12,0,-11,0,-6,0,-1],[0],[-32,0,-128,0,-192,0,-128,0,-32],[0],[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: proposed positive denominator for check31. -/
def check31Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,64,0,96,0,64,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check31Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 3)) :=
  (hPairUpper3Code.congr (by
    intro z hz
    ring))
private theorem check31Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (1) 3)=(Source.pairSlack z.1 z.2 (1) 3) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check31DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check31Denominator=true := by kernel_decide
private theorem check31DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check31Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check31Denominator check31DenCheck hz.1 hz.2).ne'
private theorem check31Cross : equalCheck
    (mul check31Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check31Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check31Numerator) check31Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check31. -/
def check31Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 3)) :=
  (check31Raw.congr check31Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check31Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check31Denominator)
    check31DenNonzero check31Cross

/-- Article: proposed exact numerator for check32. -/
def check32Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0,0,0,0,0,0,32,0,32,0,64,0,32,0,32],[20,-8,110,-16,206,0,212,16,146,16,68,16,58,0,36,-16,34,-8,6],[-8,0,-36,0,-72,0,-100,0,-88,0,-60,0,-24,0,4],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1],[0],[-32,0,-160,0,-320,0,-320,0,-160,0,-32],[0],[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: proposed positive denominator for check32. -/
def check32Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check32Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 4)) :=
  (hPairLower4Code.congr (by
    intro z hz
    ring))
private theorem check32Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (-1) 4)=(Source.pairSlack z.1 z.2 (-1) 4) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check32DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check32Denominator=true := by kernel_decide
private theorem check32DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check32Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check32Denominator check32DenCheck hz.1 hz.2).ne'
private theorem check32Cross : equalCheck
    (mul check32Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check32Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check32Numerator) check32Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check32. -/
def check32Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 4)) :=
  (check32Raw.congr check32Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check32Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check32Denominator)
    check32DenNonzero check32Cross

/-- Article: proposed exact numerator for check33. -/
def check33Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0,0,0,0,0,0,-32,0,-32,0,-64,0,-32,0,-32],[20,8,94,16,190,0,228,-16,162,-16,84,-16,74,0,20,16,18,8,6],[8,0,36,0,72,0,100,0,88,0,60,0,24,0,-4],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1],[0],[-32,0,-160,0,-320,0,-320,0,-160,0,-32],[0],[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: proposed positive denominator for check33. -/
def check33Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check33Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 4)) :=
  (hPairUpper4Code.congr (by
    intro z hz
    ring))
private theorem check33Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (1) 4)=(Source.pairSlack z.1 z.2 (1) 4) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check33DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check33Denominator=true := by kernel_decide
private theorem check33DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check33Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check33Denominator check33DenCheck hz.1 hz.2).ne'
private theorem check33Cross : equalCheck
    (mul check33Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check33Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check33Numerator) check33Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check33. -/
def check33Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 4)) :=
  (check33Raw.congr check33Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check33Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check33Denominator)
    check33DenNonzero check33Cross

/-- Article: proposed exact numerator for check34. -/
def check34Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0,0,0,0,0,0,8,0,-56,0,-72,0,-144,0,-72,0,-56,0,8],[20,-8,130,-24,326,-16,464,16,390,24,230,16,178,24,138,16,166,-16,88,-24,40,-8,6],[-8,0,-44,0,-104,0,-132,0,-64,0,-4,0,8,0,-12,0,-24],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1],[0],[0],[0],[32,0,192,0,480,0,640,0,480,0,192,0,32],[0],[0],[0],[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: proposed positive denominator for check34. -/
def check34Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check34Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 5)) :=
  (hPairLower5Code.congr (by
    intro z hz
    ring))
private theorem check34Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (-1) 5)=(Source.pairSlack z.1 z.2 (-1) 5) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check34DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check34Denominator=true := by kernel_decide
private theorem check34DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check34Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check34Denominator check34DenCheck hz.1 hz.2).ne'
private theorem check34Cross : equalCheck
    (mul check34Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check34Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check34Numerator) check34Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check34. -/
def check34Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 5)) :=
  (check34Raw.congr check34Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check34Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check34Denominator)
    check34DenNonzero check34Cross

end
end polyak.Certificates.Startup.Codes
