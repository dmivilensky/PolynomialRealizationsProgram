import polyak.Certificates.Startup.Code11

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: canonical numerator for one arithmetic source node. -/
def hAst375Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,32,0,-28,0,32,0,-70,0,32,0,-28,0,32,0,-1],[0],[0,0,0,0,0,0,0,0,-1,0,32,0,-28,0,32,0,-70,0,32,0,-28,0,32,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst375Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst375Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 9)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerImag9Code.mul hSRealCode)
private theorem hAst375DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst375Denominator=true := by kernel_decide
private theorem hAst375DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst375Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst375Denominator hAst375DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst375Cross : equalCheck
    (mul hAst375Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst375Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst375Numerator) hAst375Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst375Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 9)*(Source.multiplierReal z.1 z.2))) :=
  hAst375Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst375Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst375Denominator)
    hAst375DenNonzero hAst375Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst376Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-9,0,48,0,36,0,144,0,74,0,144,0,36,0,48,0,-9],[0],[0,0,0,0,0,0,0,0,9,0,-48,0,-36,0,-144,0,-74,0,-144,0,-36,0,-48,0,9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst376Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst376Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 9)*(Source.multiplierImag z.1 z.2))) :=
  (hPowerReal9Code.mul hSImagCode)
private theorem hAst376DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst376Denominator=true := by kernel_decide
private theorem hAst376DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst376Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst376Denominator hAst376DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst376Cross : equalCheck
    (mul hAst376Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst376Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst376Numerator) hAst376Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst376Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 9)*(Source.multiplierImag z.1 z.2))) :=
  hAst376Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst376Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst376Denominator)
    hAst376DenNonzero hAst376Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst377Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-5,0,40,0,4,0,88,0,2,0,88,0,4,0,40,0,-5],[0],[0,0,0,0,0,0,0,0,4,0,-8,0,-32,0,-56,0,-72,0,-56,0,-32,0,-8,0,4]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst377Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst377Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 9)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 9)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst375Code.add hAst376Code)
private theorem hAst377DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst377Denominator=true := by kernel_decide
private theorem hAst377DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst377Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst377Denominator hAst377DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst377Cross : equalCheck
    (mul hAst377Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst377Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst377Numerator) hAst377Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst377Code : RationalCode Source.domain (fun z => (((Source.powerImag z.1 9)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 9)*(Source.multiplierImag z.1 z.2)))) :=
  hAst377Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst377Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst377Denominator)
    hAst377DenNonzero hAst377Cross

/-- Article: proposed exact numerator for hGradientImag9. -/
def hGradientImag9Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-5,0,40,0,4,0,88,0,2,0,88,0,4,0,40,0,-5],[0],[0,0,0,0,0,0,0,0,4,0,-8,0,-32,0,-56,0,-72,0,-56,0,-32,0,-8,0,4]]
/-- Article: proposed positive denominator for hGradientImag9. -/
def hGradientImag9Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientImag9Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 9)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 9)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst377Code.congr (by
    intro z hz
    ring))
private theorem hGradientImag9Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerImag z.1 9)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 9)*(Source.multiplierImag z.1 z.2)))=Source.gradientImag z.1 z.2 9 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientImag]; ring
private theorem hGradientImag9DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientImag9Denominator=true := by kernel_decide
private theorem hGradientImag9DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag9Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientImag9Denominator hGradientImag9DenCheck hz.1 hz.2).ne'
private theorem hGradientImag9Cross : equalCheck
    (mul hGradientImag9Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag9Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag9Numerator) hGradientImag9Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientImag9. -/
def hGradientImag9Code : RationalCode Source.domain (fun z => Source.gradientImag z.1 z.2 9) :=
  (hGradientImag9Raw.congr hGradientImag9Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag9Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag9Denominator)
    hGradientImag9DenNonzero hGradientImag9Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst378Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,40,0,-45,0,0,0,-210,0,-80,0,-210,0,0,0,-45,0,40,0,-1],[0],[-2,0,-19,0,-81,0,-204,0,-335,0,-400,0,-345,0,-228,0,-132,0,-79,0,-79,0,-72,0,-51,0,-22,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst378Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,20,0,90,0,240,0,420,0,504,0,420,0,240,0,90,0,20,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst378Raw : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  (hGradientReal9Code.add hAst009Code)
private theorem hAst378DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst378Denominator=true := by kernel_decide
private theorem hAst378DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst378Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst378Denominator hAst378DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst378Cross : equalCheck
    (mul hAst378Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst378Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst378Numerator) hAst378Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst378Code : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  hAst378Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst378Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst378Denominator)
    hAst378DenNonzero hAst378Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst379Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,9,0,36,0,84,0,125,0,166,0,39,0,36,0,-201,0,-79,0,-210,0,0,0,-45,0,40,0,-1],[0],[-1,0,-10,0,-45,0,-120,0,-209,0,-274,0,-261,0,-192,0,-123,0,-78,0,-79,0,-72,0,-51,0,-22,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst379Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,20,0,90,0,240,0,420,0,504,0,420,0,240,0,90,0,20,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst379Raw : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  (hAst378Code.add hAst010Code)
private theorem hAst379DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst379Denominator=true := by kernel_decide
private theorem hAst379DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst379Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst379Denominator hAst379DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst379Cross : equalCheck
    (mul hAst379Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst379Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst379Numerator) hAst379Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst379Code : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  hAst379Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst379Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst379Denominator)
    hAst379DenNonzero hAst379Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst380Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,18,0,153,0,816,0,3058,0,8630,0,19122,0,33726,0,46567,0,46868,0,27040,0,-21288,0,-65259,0,-119684,0,-95632,0,-95052,0,13731,0,11530,0,100181,0,32728,0,64992,0,-9042,0,12982,0,-16642,0,2445,0,-3600,0,1690,0,-80,0,1],[0],[0,0,-2,0,-38,0,-342,0,-1938,0,-7748,0,-23342,0,-55310,0,-105714,0,-164444,0,-206352,0,-203744,0,-139368,0,-32802,0,80868,0,154020,0,171420,0,146646,0,106042,0,81514,0,66078,0,59784,0,44778,0,25610,0,9398,0,-1432,0,-1956,0,-1748,0,124,0,-2],[0],[1,0,20,0,190,0,1140,0,4843,0,15528,0,39212,0,80424,0,137017,0,197068,0,243042,0,261548,0,252123,0,226736,0,199144,0,175536,0,152283,0,124012,0,91426,0,60556,0,37945,0,24360,0,16428,0,10664,0,5611,0,2100,0,382,0,-44,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst380Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,80,0,760,0,4560,0,19380,0,62016,0,155040,0,310080,0,503880,0,671840,0,739024,0,671840,0,503880,0,310080,0,155040,0,62016,0,19380,0,4560,0,760,0,80,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst380Raw : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  (hAst379Code.pow 2)
private theorem hAst380DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst380Denominator=true := by kernel_decide
private theorem hAst380DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst380Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst380Denominator hAst380DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst380Cross : equalCheck
    (mul hAst380Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst380Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst380Numerator) hAst380Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst380Code : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  hAst380Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst380Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst380Denominator)
    hAst380DenNonzero hAst380Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst381Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-18,0,-153,0,-816,0,-3058,0,-8630,0,-19122,0,-33726,0,-46567,0,-46868,0,-27040,0,21288,0,65259,0,119684,0,95632,0,95052,0,-13731,0,-11530,0,-100181,0,-32728,0,-64992,0,9042,0,-12982,0,16642,0,-2445,0,3600,0,-1690,0,80,0,-1],[0],[0,0,2,0,38,0,342,0,1938,0,7748,0,23342,0,55310,0,105714,0,164444,0,206352,0,203744,0,139368,0,32802,0,-80868,0,-154020,0,-171420,0,-146646,0,-106042,0,-81514,0,-66078,0,-59784,0,-44778,0,-25610,0,-9398,0,1432,0,1956,0,1748,0,-124,0,2],[0],[-1,0,-20,0,-190,0,-1140,0,-4843,0,-15528,0,-39212,0,-80424,0,-137017,0,-197068,0,-243042,0,-261548,0,-252123,0,-226736,0,-199144,0,-175536,0,-152283,0,-124012,0,-91426,0,-60556,0,-37945,0,-24360,0,-16428,0,-10664,0,-5611,0,-2100,0,-382,0,44,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst381Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,320,0,3040,0,18240,0,77520,0,248064,0,620160,0,1240320,0,2015520,0,2687360,0,2956096,0,2687360,0,2015520,0,1240320,0,620160,0,248064,0,77520,0,18240,0,3040,0,320,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst381Raw : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  ((RationalCode.constant Source.domain (-1/4)).mul hAst380Code)
private theorem hAst381DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst381Denominator=true := by kernel_decide
private theorem hAst381DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst381Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst381Denominator hAst381DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst381Cross : equalCheck
    (mul hAst381Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst381Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst381Numerator) hAst381Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst381Code : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  hAst381Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst381Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst381Denominator)
    hAst381DenNonzero hAst381Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst382Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-9,0,-36,0,-84,0,-126,0,-135,0,-36,0,0,0,135,0,73,0,144,0,36,0,48,0,-9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst382Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,9,0,36,0,84,0,126,0,126,0,84,0,36,0,9,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst382Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9))) :=
  ((RationalCode.constant Source.domain (-1)).add hPowerReal9Code)
private theorem hAst382DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst382Denominator=true := by kernel_decide
private theorem hAst382DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst382Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst382Denominator hAst382DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst382Cross : equalCheck
    (mul hAst382Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst382Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst382Numerator) hAst382Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst382Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9))) :=
  hAst382Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst382Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst382Denominator)
    hAst382DenNonzero hAst382Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst383Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,18,0,153,0,816,0,3060,0,8586,0,18630,0,31536,0,40878,0,37492,0,15975,0,-20880,0,-56100,0,-82476,0,-75060,0,-60624,0,-12447,0,6426,0,43183,0,31392,0,38952,0,14946,0,13806,0,864,0,1656,0,-864,0,81]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst383Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,18,0,153,0,816,0,3060,0,8568,0,18564,0,31824,0,43758,0,48620,0,43758,0,31824,0,18564,0,8568,0,3060,0,816,0,153,0,18,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst383Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2) :=
  (hAst382Code.pow 2)
private theorem hAst383DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst383Denominator=true := by kernel_decide
private theorem hAst383DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst383Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst383Denominator hAst383DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst383Cross : equalCheck
    (mul hAst383Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst383Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst383Numerator) hAst383Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst383Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2) :=
  hAst383Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst383Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst383Denominator)
    hAst383DenNonzero hAst383Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst384Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,18,0,153,0,816,0,3060,0,8586,0,18630,0,31536,0,40878,0,37492,0,15975,0,-20880,0,-56100,0,-82476,0,-75060,0,-60624,0,-12447,0,6426,0,43183,0,31392,0,38952,0,14946,0,13806,0,864,0,1656,0,-864,0,81]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst384Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,72,0,612,0,3264,0,12240,0,34272,0,74256,0,127296,0,175032,0,194480,0,175032,0,127296,0,74256,0,34272,0,12240,0,3264,0,612,0,72,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst384Raw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2)) :=
  ((RationalCode.constant Source.domain (1/4)).mul hAst383Code)
private theorem hAst384DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst384Denominator=true := by kernel_decide
private theorem hAst384DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst384Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst384Denominator hAst384DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst384Cross : equalCheck
    (mul hAst384Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst384Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst384Numerator) hAst384Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst384Code : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2)) :=
  hAst384Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst384Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst384Denominator)
    hAst384DenNonzero hAst384Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst385Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,-10,0,80,0,8,0,176,0,4,0,176,0,8,0,80,0,-10],[0],[-1,0,-9,0,-36,0,-84,0,-126,0,-118,0,-100,0,-100,0,-121,0,-145,0,-112,0,-64,0,-16,0,8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst385Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst385Raw : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  (hGradientImag9Code.add hAst018Code)
private theorem hAst385DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst385Denominator=true := by kernel_decide
private theorem hAst385DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst385Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst385Denominator hAst385DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst385Cross : equalCheck
    (mul hAst385Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst385Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst385Numerator) hAst385Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst385Code : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  hAst385Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst385Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst385Denominator)
    hAst385DenNonzero hAst385Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst386Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-9,0,-36,0,-84,0,-126,0,-136,0,-4,0,-28,0,167,0,3,0,176,0,8,0,80,0,-10],[0],[0,0,0,0,0,0,0,0,8,0,-16,0,-64,0,-112,0,-144,0,-112,0,-64,0,-16,0,8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst386Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst386Raw : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst385Code.add hAst019Code)
private theorem hAst386DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst386Denominator=true := by kernel_decide
private theorem hAst386DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst386Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst386Denominator hAst386DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst386Cross : equalCheck
    (mul hAst386Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst386Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst386Numerator) hAst386Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst386Code : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  hAst386Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst386Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst386Denominator)
    hAst386DenNonzero hAst386Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst387Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,18,0,153,0,816,0,3060,0,8588,0,18584,0,31088,0,39182,0,33948,0,11778,0,-23312,0,-47932,0,-77520,0,-52644,0,-71984,0,5657,0,-28158,0,60425,0,-672,0,58304,0,-44,0,28164,0,-2240,0,6240,0,-1600,0,100],[0],[0,0,0,0,0,0,0,0,-16,0,-112,0,-160,0,1184,0,7584,0,23488,0,51744,0,78752,0,94528,0,78336,0,37472,0,-14240,0,-61152,0,-79904,0,-83616,0,-64544,0,-42544,0,-21648,0,-5440,0,-1152,0,1600,0,-160],[0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,-256,0,-768,0,256,0,5376,0,17152,0,33536,0,48384,0,54656,0,48384,0,33536,0,17152,0,5376,0,256,0,-768,0,-256,0,64]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst387Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,72,0,612,0,3264,0,12240,0,34272,0,74256,0,127296,0,175032,0,194480,0,175032,0,127296,0,74256,0,34272,0,12240,0,3264,0,612,0,72,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst387Raw : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  (hAst386Code.pow 2)
private theorem hAst387DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst387Denominator=true := by kernel_decide
private theorem hAst387DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst387Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst387Denominator hAst387DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst387Cross : equalCheck
    (mul hAst387Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst387Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst387Numerator) hAst387Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst387Code : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  hAst387Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst387Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst387Denominator)
    hAst387DenNonzero hAst387Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst388Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-19,0,-172,0,-987,0,-4029,0,-12464,0,-30232,0,-58260,0,-88854,0,-104218,0,-84908,0,-22414,0,59466,0,148764,0,178096,0,202148,0,118971,0,94485,0,-37924,0,-31595,0,-118057,0,-57588,0,-86424,0,-25880,0,-32164,0,-2400,0,-4740,0,1500,0,-100],[0],[0,0,0,0,0,0,0,0,0,0,16,0,128,0,288,0,-912,0,-8608,0,-32256,0,-82816,0,-153984,0,-225024,0,-251616,0,-210336,0,-101568,0,37920,0,155296,0,224672,0,228064,0,190704,0,128736,0,69632,0,28240,0,4992,0,-288,0,-1440,0,160],[0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-64,0,192,0,960,0,768,0,-4864,0,-22784,0,-56064,0,-99072,0,-136576,0,-151424,0,-136576,0,-99072,0,-56064,0,-22784,0,-4864,0,768,0,960,0,192,0,-64]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst388Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,320,0,3040,0,18240,0,77520,0,248064,0,620160,0,1240320,0,2015520,0,2687360,0,2956096,0,2687360,0,2015520,0,1240320,0,620160,0,248064,0,77520,0,18240,0,3040,0,320,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst388Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  (hAst023Code.mul hAst387Code)
private theorem hAst388DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst388Denominator=true := by kernel_decide
private theorem hAst388DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst388Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst388Denominator hAst388DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst388Cross : equalCheck
    (mul hAst388Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst388Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst388Numerator) hAst388Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst388Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  hAst388Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst388Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst388Denominator)
    hAst388DenNonzero hAst388Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst389Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-64,0,1080,0,-1856,0,2972,0,-6336,0,7048,0,-8128,0,10566,0,-8128,0,7048,0,-6336,0,2972,0,-1856,0,1080,0,-64,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst389Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,16,0,120,0,560,0,1820,0,4368,0,8008,0,11440,0,12870,0,11440,0,8008,0,4368,0,1820,0,560,0,120,0,16,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst389Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 9))^2) :=
  (hPowerImag9Code.pow 2)
private theorem hAst389DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst389Denominator=true := by kernel_decide
private theorem hAst389DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst389Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst389Denominator hAst389DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst389Cross : equalCheck
    (mul hAst389Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst389Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst389Numerator) hAst389Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst389Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 9))^2) :=
  hAst389Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst389Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst389Denominator)
    hAst389DenNonzero hAst389Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst390Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-63,0,1017,0,-840,0,2196,0,-5220,0,3684,0,-7416,0,9486,0,-5690,0,9486,0,-7416,0,3684,0,-5220,0,2196,0,-840,0,1017,0,-63,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst390Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,72,0,612,0,3264,0,12240,0,34272,0,74256,0,127296,0,175032,0,194480,0,175032,0,127296,0,74256,0,34272,0,12240,0,3264,0,612,0,72,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst390Raw : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 9))^2)) :=
  (hAst026Code.mul hAst389Code)
private theorem hAst390DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst390Denominator=true := by kernel_decide
private theorem hAst390DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst390Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst390Denominator hAst390DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst390Cross : equalCheck
    (mul hAst390Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst390Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst390Numerator) hAst390Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst390Code : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 9))^2)) :=
  hAst390Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst390Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst390Denominator)
    hAst390DenNonzero hAst390Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst391Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-18,0,-153,0,-816,0,-3058,0,-8630,0,-19122,0,-33726,0,-46567,0,-46868,0,-27040,0,21288,0,65259,0,119684,0,95632,0,95052,0,-13731,0,-11530,0,-100181,0,-32728,0,-64992,0,9042,0,-12982,0,16642,0,-2445,0,3600,0,-1690,0,80,0,-1],[0],[4,0,82,0,798,0,4902,0,21318,0,69836,0,178790,0,364838,0,596034,0,767580,0,733700,0,397992,0,-188172,0,-829422,0,-1265316,0,-1326900,0,-1006440,0,-463014,0,68310,0,415222,0,513598,0,437184,0,285822,0,148078,0,59362,0,14680,0,1992,0,-1060,0,200,0,2],[0],[-1,0,-20,0,-190,0,-1140,0,-4843,0,-15528,0,-39212,0,-80424,0,-137017,0,-197068,0,-243042,0,-261548,0,-252123,0,-226736,0,-199144,0,-175536,0,-152283,0,-124012,0,-91426,0,-60556,0,-37945,0,-24360,0,-16428,0,-10664,0,-5611,0,-2100,0,-382,0,44,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst391Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,320,0,3040,0,18240,0,77520,0,248064,0,620160,0,1240320,0,2015520,0,2687360,0,2956096,0,2687360,0,2015520,0,1240320,0,620160,0,248064,0,77520,0,18240,0,3040,0,320,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst391Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2))) :=
  (hAst381Code.add hAst384Code)
private theorem hAst391DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst391Denominator=true := by kernel_decide
private theorem hAst391DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst391Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst391Denominator hAst391DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst391Cross : equalCheck
    (mul hAst391Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst391Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst391Numerator) hAst391Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst391Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2))) :=
  hAst391Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst391Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst391Denominator)
    hAst391DenNonzero hAst391Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst392Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-18,0,-153,0,-816,0,-3060,0,-8586,0,-18630,0,-31536,0,-40878,0,-37493,0,-15912,0,19863,0,56940,0,80280,0,80280,0,56940,0,19863,0,-15912,0,-37493,0,-40878,0,-31536,0,-18630,0,-8586,0,-3060,0,-816,0,-153,0,-18,0,-1],[0],[4,0,74,0,646,0,3536,0,13600,0,39116,0,87086,0,151838,0,204360,0,198414,0,100256,0,-83750,0,-274912,0,-420872,0,-400276,0,-315812,0,-76108,0,42934,0,213846,0,169268,0,189280,0,80060,0,65158,0,7334,0,7776,0,-3214,0,356,0,2],[0],[-1,0,-18,0,-153,0,-816,0,-3058,0,-8596,0,-18962,0,-33904,0,-50247,0,-62734,0,-67135,0,-63584,0,-57052,0,-53912,0,-57052,0,-63584,0,-67135,0,-62734,0,-50247,0,-33904,0,-18962,0,-8596,0,-3058,0,-816,0,-153,0,-18,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst392Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,288,0,2448,0,13056,0,48960,0,137088,0,297024,0,509184,0,700128,0,777920,0,700128,0,509184,0,297024,0,137088,0,48960,0,13056,0,2448,0,288,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst392Raw : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  (hAst391Code.add hAst388Code)
private theorem hAst392DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst392Denominator=true := by kernel_decide
private theorem hAst392DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst392Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst392Denominator hAst392DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst392Cross : equalCheck
    (mul hAst392Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst392Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst392Numerator) hAst392Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst392Code : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  hAst392Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst392Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst392Denominator)
    hAst392DenNonzero hAst392Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst393Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-120,0,-210,0,-270,0,-132,0,48,0,315,0,425,0,425,0,315,0,48,0,-132,0,-270,0,-210,0,-120,0,-45,0,-10,0,-1],[0],[4,0,42,0,198,0,552,0,1008,0,1344,0,874,0,-170,0,-1372,0,-2400,0,-2142,0,-1806,0,-120,0,648,0,1398,0,1034,0,608,0,238,0,56,0,6],[0],[-1,0,-10,0,-45,0,-120,0,-208,0,-296,0,-312,0,-264,0,-202,0,-156,0,-202,0,-264,0,-312,0,-296,0,-208,0,-120,0,-45,0,-10,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst393Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst393Raw : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 9))^2))) :=
  (hAst392Code.add hAst390Code)
private theorem hAst393DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst393Denominator=true := by kernel_decide
private theorem hAst393DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst393Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst393Denominator hAst393DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst393Cross : equalCheck
    (mul hAst393Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst393Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst393Numerator) hAst393Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst393Code : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 9))^2))) :=
  hAst393Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst393Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst393Denominator)
    hAst393DenNonzero hAst393Cross

/-- Article: proposed exact numerator for hRadius9. -/
def hRadius9Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-120,0,-210,0,-270,0,-132,0,48,0,315,0,425,0,425,0,315,0,48,0,-132,0,-270,0,-210,0,-120,0,-45,0,-10,0,-1],[0],[4,0,42,0,198,0,552,0,1008,0,1344,0,874,0,-170,0,-1372,0,-2400,0,-2142,0,-1806,0,-120,0,648,0,1398,0,1034,0,608,0,238,0,56,0,6],[0],[-1,0,-10,0,-45,0,-120,0,-208,0,-296,0,-312,0,-264,0,-202,0,-156,0,-202,0,-264,0,-312,0,-296,0,-208,0,-120,0,-45,0,-10,0,-1]]
/-- Article: proposed positive denominator for hRadius9. -/
def hRadius9Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hRadius9Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 9))^2))) :=
  (hAst393Code.congr (by
    intro z hz
    ring))
private theorem hRadius9Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 9)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 9))^2))=Source.radius z.1 z.2 9 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.radius]; ring
private theorem hRadius9DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hRadius9Denominator=true := by kernel_decide
private theorem hRadius9DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hRadius9Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hRadius9Denominator hRadius9DenCheck hz.1 hz.2).ne'
private theorem hRadius9Cross : equalCheck
    (mul hRadius9Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hRadius9Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hRadius9Numerator) hRadius9Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hRadius9. -/
def hRadius9Code : RationalCode Source.domain (fun z => Source.radius z.1 z.2 9) :=
  (hRadius9Raw.congr hRadius9Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius9Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius9Denominator)
    hRadius9DenNonzero hRadius9Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst394Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst394Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst394Raw : RationalCode Source.domain (fun z => (z.1)^18) :=
  ((RationalCode.first Source.domain).pow 18)
private theorem hAst394DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst394Denominator=true := by kernel_decide
private theorem hAst394DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst394Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst394Denominator hAst394DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst394Cross : equalCheck
    (mul hAst394Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst394Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst394Numerator) hAst394Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst394Code : RationalCode Source.domain (fun z => (z.1)^18) :=
  hAst394Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst394Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst394Denominator)
    hAst394DenNonzero hAst394Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst395Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst395Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst395Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^18)) :=
  ((RationalCode.constant Source.domain (-1)).add hAst394Code)
private theorem hAst395DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst395Denominator=true := by kernel_decide
private theorem hAst395DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst395Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst395Denominator hAst395DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst395Cross : equalCheck
    (mul hAst395Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst395Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst395Numerator) hAst395Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst395Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^18)) :=
  hAst395Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst395Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst395Denominator)
    hAst395DenNonzero hAst395Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst396Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,-2,0,-1],[0,2,-2,0,2,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,2,0,-2,2],[1,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,-2,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst396Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst396Raw : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^18))) :=
  (hValueCode.mul hAst395Code)
private theorem hAst396DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst396Denominator=true := by kernel_decide
private theorem hAst396DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst396Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst396Denominator hAst396DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst396Cross : equalCheck
    (mul hAst396Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst396Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst396Numerator) hAst396Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst396Code : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^18))) :=
  hAst396Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst396Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst396Denominator)
    hAst396DenNonzero hAst396Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst397Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,40,0,-45,0,0,0,-210,0,-80,0,-210,0,0,0,-45,0,40,0,-1],[0],[2,0,19,0,81,0,204,0,337,0,356,0,243,0,84,0,-24,0,-57,0,-77,0,-72,0,-51,0,-22,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst397Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,20,0,90,0,240,0,420,0,504,0,420,0,240,0,90,0,20,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst397Raw : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9))) :=
  (hDRealCode.add hGradientReal9Code)
private theorem hAst397DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst397Denominator=true := by kernel_decide
private theorem hAst397DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst397Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst397Denominator hAst397DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst397Cross : equalCheck
    (mul hAst397Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst397Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst397Numerator) hAst397Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst397Code : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9))) :=
  hAst397Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst397Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst397Denominator)
    hAst397DenNonzero hAst397Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst398Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-127,0,-86,0,-129,0,-36,0,-219,0,-81,0,-210,0,0,0,-45,0,40,0,-1],[0],[1,0,10,0,45,0,120,0,211,0,230,0,159,0,48,0,-33,0,-58,0,-77,0,-72,0,-51,0,-22,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst398Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,20,0,90,0,240,0,420,0,504,0,420,0,240,0,90,0,20,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst398Raw : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9))+(Source.multiplierReal z.1 z.2))) :=
  (hAst397Code.add hSRealCode)
private theorem hAst398DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst398Denominator=true := by kernel_decide
private theorem hAst398DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst398Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst398Denominator hAst398DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst398Cross : equalCheck
    (mul hAst398Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst398Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst398Numerator) hAst398Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst398Code : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9))+(Source.multiplierReal z.1 z.2))) :=
  hAst398Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst398Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst398Denominator)
    hAst398DenNonzero hAst398Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst399Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,9,0,36,0,84,0,126,0,135,0,36,0,0,0,-135,0,-73,0,-144,0,-36,0,-48,0,9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst399Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst399Raw : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))) :=
  ((RationalCode.constant Source.domain (-1/2)).mul hAst382Code)
private theorem hAst399DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst399Denominator=true := by kernel_decide
private theorem hAst399DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst399Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst399Denominator hAst399DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst399Cross : equalCheck
    (mul hAst399Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst399Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst399Numerator) hAst399Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst399Code : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))) :=
  hAst399Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst399Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst399Denominator)
    hAst399DenNonzero hAst399Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst400Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-18,0,-153,0,-816,0,-3061,0,-8546,0,-18318,0,-30729,0,-40914,0,-43901,0,-38622,0,-32949,0,-22674,0,-24376,0,112,0,1326,0,49299,0,38616,0,76167,0,36750,0,49383,0,7362,0,13046,0,-5957,0,864,0,-2289,0,408,0,-9],[0],[1,0,19,0,171,0,969,0,3877,0,11624,0,26961,0,49038,0,69714,0,75091,0,53976,0,9207,0,-44430,0,-85400,0,-101830,0,-90780,0,-60003,0,-23703,0,7411,0,23351,0,27369,0,22320,0,14581,0,7694,0,2448,0,561,0,-246,0,9]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst400Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,76,0,684,0,3876,0,15504,0,46512,0,108528,0,201552,0,302328,0,369512,0,369512,0,302328,0,201552,0,108528,0,46512,0,15504,0,3876,0,684,0,76,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst400Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9))+(Source.multiplierReal z.1 z.2)))) :=
  (hAst399Code.mul hAst398Code)
private theorem hAst400DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst400Denominator=true := by kernel_decide
private theorem hAst400DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst400Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst400Denominator hAst400DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst400Cross : equalCheck
    (mul hAst400Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst400Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst400Numerator) hAst400Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst400Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9))+(Source.multiplierReal z.1 z.2)))) :=
  hAst400Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst400Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst400Denominator)
    hAst400DenNonzero hAst400Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst401Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,-10,0,80,0,8,0,176,0,4,0,176,0,8,0,80,0,-10],[0],[1,0,9,0,36,0,84,0,126,0,134,0,68,0,-28,0,-103,0,-143,0,-112,0,-64,0,-16,0,8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst401Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst401Raw : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 9))) :=
  (hDImagCode.add hGradientImag9Code)
private theorem hAst401DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst401Denominator=true := by kernel_decide
private theorem hAst401DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst401Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst401Denominator hAst401DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst401Cross : equalCheck
    (mul hAst401Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst401Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst401Numerator) hAst401Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst401Code : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 9))) :=
  hAst401Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst401Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst401Denominator)
    hAst401DenNonzero hAst401Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst402Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,9,0,36,0,84,0,126,0,116,0,164,0,44,0,185,0,5,0,176,0,8,0,80,0,-10],[0],[0,0,0,0,0,0,0,0,8,0,-16,0,-64,0,-112,0,-144,0,-112,0,-64,0,-16,0,8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst402Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,18,0,72,0,168,0,252,0,252,0,168,0,72,0,18,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst402Raw : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 9))+(Source.multiplierImag z.1 z.2))) :=
  (hAst401Code.add hSImagCode)
private theorem hAst402DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst402Denominator=true := by kernel_decide
private theorem hAst402DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst402Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst402Denominator hAst402DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst402Cross : equalCheck
    (mul hAst402Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst402Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst402Numerator) hAst402Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst402Code : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 9))+(Source.multiplierImag z.1 z.2))) :=
  hAst402Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst402Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst402Denominator)
    hAst402DenNonzero hAst402Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst403Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,31,0,3,0,36,0,-66,0,-6,0,-66,0,36,0,3,0,31,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst403Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,20,0,90,0,240,0,420,0,504,0,420,0,240,0,90,0,20,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst403Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))) :=
  (hAst040Code.mul hPowerImag9Code)
private theorem hAst403DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst403Denominator=true := by kernel_decide
private theorem hAst403DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst403Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst403Denominator hAst403DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst403Cross : equalCheck
    (mul hAst403Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst403Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst403Numerator) hAst403Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst403Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))) :=
  hAst403Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst403Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst403Denominator)
    hAst403DenNonzero hAst403Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst404Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,22,0,246,0,1095,0,2844,0,4738,0,4338,0,3606,0,-5022,0,-836,0,-14308,0,6474,0,-15300,0,14580,0,-18092,0,12696,0,-15369,0,11694,0,-4434,0,9015,0,-48,0,2442,0,-390,0,10],[0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-8,0,264,0,-408,0,-1632,0,-4624,0,-5984,0,-4080,0,1632,0,9120,0,11440,0,9120,0,1632,0,-4080,0,-5984,0,-4624,0,-1632,0,-408,0,264,0,-8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst404Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,76,0,684,0,3876,0,15504,0,46512,0,108528,0,201552,0,302328,0,369512,0,369512,0,302328,0,201552,0,108528,0,46512,0,15504,0,3876,0,684,0,76,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst404Raw : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 9))+(Source.multiplierImag z.1 z.2)))) :=
  (hAst403Code.mul hAst402Code)
private theorem hAst404DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst404Denominator=true := by kernel_decide
private theorem hAst404DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst404Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst404Denominator hAst404DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst404Cross : equalCheck
    (mul hAst404Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst404Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst404Numerator) hAst404Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst404Code : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 9))+(Source.multiplierImag z.1 z.2)))) :=
  hAst404Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst404Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst404Denominator)
    hAst404DenNonzero hAst404Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst405Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-1,0,22,0,246,0,1095,0,2844,0,4718,0,5118,0,-1278,0,-4926,0,-18868,0,-5396,0,-16422,0,17628,0,-5124,0,27548,0,-7008,0,17559,0,-11202,0,4478,0,-9017,0,48,0,-2442,0,390,0,-10],[0,2,-2,32,-30,238,-208,1088,-880,3400,-2520,7616,-5096,12376,-7280,14144,-6864,9724,-2860,-2,2862,-9756,6894,-14382,7488,-13464,5976,-11016,5040,-11016,5976,-13464,7488,-14382,6894,-9756,2862,-2,-2860,9724,-6864,14144,-7280,12376,-5096,7616,-2520,3400,-880,1088,-208,238,-30,32,-2,2],[2,0,37,0,324,0,1785,0,6937,0,20192,0,45525,0,80862,0,113472,0,123710,0,97716,0,40878,0,-26682,0,-79892,0,-107338,0,-108528,0,-91674,0,-67443,0,-41208,0,-20407,0,-4455,0,3756,0,6013,0,4634,0,1632,0,408,0,-264,0,8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst405Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,76,0,684,0,3876,0,15504,0,46512,0,108528,0,201552,0,302328,0,369512,0,369512,0,302328,0,201552,0,108528,0,46512,0,15504,0,3876,0,684,0,76,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst405Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^18))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9))+(Source.multiplierReal z.1 z.2))))) :=
  (hAst396Code.add hAst400Code)
private theorem hAst405DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst405Denominator=true := by kernel_decide
private theorem hAst405DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst405Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst405Denominator hAst405DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst405Cross : equalCheck
    (mul hAst405Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst405Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst405Numerator) hAst405Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst405Code : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^18))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9))+(Source.multiplierReal z.1 z.2))))) :=
  hAst405Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst405Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst405Denominator)
    hAst405DenNonzero hAst405Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst406Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-2,0,62,0,6,0,72,0,-132,0,-12,0,-132,0,72,0,6,0,62,0,-2],[0,2,-2,14,-12,40,-28,56,-28,28,0,-28,28,-56,28,-40,12,-14,2,-4,2,-14,12,-40,28,-56,28,-28,0,28,-28,56,-28,40,-12,14,-2,2],[2,0,19,0,81,0,204,0,337,0,365,0,204,0,0,0,-204,0,-275,0,-295,0,-252,0,-135,0,-61,0,10]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst406Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,40,0,180,0,480,0,840,0,1008,0,840,0,480,0,180,0,40,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst406Raw : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^18))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 9))+(Source.multiplierImag z.1 z.2))))) :=
  (hAst405Code.add hAst404Code)
private theorem hAst406DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst406Denominator=true := by kernel_decide
private theorem hAst406DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst406Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst406Denominator hAst406DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst406Cross : equalCheck
    (mul hAst406Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst406Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst406Numerator) hAst406Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst406Code : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^18))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 9))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 9))+(Source.multiplierImag z.1 z.2))))) :=
  hAst406Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst406Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst406Denominator)
    hAst406DenNonzero hAst406Cross

/-- Article: proposed exact numerator for hDiscrepancy9. -/
def hDiscrepancy9Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-2,0,62,0,6,0,72,0,-132,0,-12,0,-132,0,72,0,6,0,62,0,-2],[0,2,-2,14,-12,40,-28,56,-28,28,0,-28,28,-56,28,-40,12,-14,2,-4,2,-14,12,-40,28,-56,28,-28,0,28,-28,56,-28,40,-12,14,-2,2],[2,0,19,0,81,0,204,0,337,0,365,0,204,0,0,0,-204,0,-275,0,-295,0,-252,0,-135,0,-61,0,10]]
/-- Article: proposed positive denominator for hDiscrepancy9. -/
def hDiscrepancy9Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,40,0,180,0,480,0,840,0,1008,0,840,0,480,0,180,0,40,0,4]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDiscrepancy9Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^18))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 9)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 9)+(Source.multiplierImag z.1 z.2))))) :=
  (hAst406Code.congr (by
    intro z hz
    ring))
private theorem hDiscrepancy9Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^18))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 9))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 9)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 9)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 9)+(Source.multiplierImag z.1 z.2))))=Source.discrepancy z.1 z.2 9 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.discrepancy]; ring
private theorem hDiscrepancy9DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDiscrepancy9Denominator=true := by kernel_decide
private theorem hDiscrepancy9DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy9Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDiscrepancy9Denominator hDiscrepancy9DenCheck hz.1 hz.2).ne'
private theorem hDiscrepancy9Cross : equalCheck
    (mul hDiscrepancy9Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy9Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy9Numerator) hDiscrepancy9Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDiscrepancy9. -/
def hDiscrepancy9Code : RationalCode Source.domain (fun z => Source.discrepancy z.1 z.2 9) :=
  (hDiscrepancy9Raw.congr hDiscrepancy9Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy9Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy9Denominator)
    hDiscrepancy9DenNonzero hDiscrepancy9Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst407Numerator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst407Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst407Raw : RationalCode Source.domain (fun z => (z.2)^10) :=
  ((RationalCode.second Source.domain).pow 10)
private theorem hAst407DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst407Denominator=true := by kernel_decide
private theorem hAst407DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst407Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst407Denominator hAst407DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst407Cross : equalCheck
    (mul hAst407Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst407Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst407Numerator) hAst407Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst407Code : RationalCode Source.domain (fun z => (z.2)^10) :=
  hAst407Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst407Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst407Denominator)
    hAst407DenNonzero hAst407Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst408Numerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst408Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst408Raw : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+(z.2)^10)) :=
  ((RationalCode.constant Source.domain 1).add hAst407Code)
private theorem hAst408DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst408Denominator=true := by kernel_decide
private theorem hAst408DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst408Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst408Denominator hAst408DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst408Cross : equalCheck
    (mul hAst408Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst408Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst408Numerator) hAst408Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst408Code : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+(z.2)^10)) :=
  hAst408Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst408Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst408Denominator)
    hAst408DenNonzero hAst408Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst409Numerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[0],[0],[0],[0],[0],[0],[0],[0],[2],[0],[0],[0],[0],[0],[0],[0],[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst409Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst409Raw : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+(z.2)^10))^2) :=
  (hAst408Code.pow 2)
private theorem hAst409DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst409Denominator=true := by kernel_decide
private theorem hAst409DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst409Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst409Denominator hAst409DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst409Cross : equalCheck
    (mul hAst409Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst409Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst409Numerator) hAst409Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst409Code : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+(z.2)^10))^2) :=
  hAst409Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst409Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst409Denominator)
    hAst409DenNonzero hAst409Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst410Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,2,0,-62,0,-6,0,-72,0,132,0,12,0,132,0,-72,0,-6,0,-62,0,2],[0,-2,2,-14,12,-40,28,-56,28,-28,0,28,-28,56,-28,40,-12,14,-2,4,-2,14,-12,40,-28,56,-28,28,0,-28,28,-56,28,-40,12,-14,2,-2],[-2,0,-19,0,-81,0,-204,0,-337,0,-365,0,-204,0,0,0,204,0,275,0,295,0,252,0,135,0,61,0,-10]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst410Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,40,0,180,0,480,0,840,0,1008,0,840,0,480,0,180,0,40,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst410Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 9))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDiscrepancy9Code)
private theorem hAst410DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst410Denominator=true := by kernel_decide
private theorem hAst410DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst410Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst410Denominator hAst410DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst410Cross : equalCheck
    (mul hAst410Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst410Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst410Numerator) hAst410Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst410Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 9))) :=
  hAst410Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst410Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst410Denominator)
    hAst410DenNonzero hAst410Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst411Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-120,0,-210,0,-270,0,-132,0,48,0,315,0,425,0,425,0,315,0,48,0,-132,0,-270,0,-210,0,-120,0,-45,0,-10,0,-1],[0],[20,0,202,0,918,0,2472,0,4368,0,5376,0,4234,0,1750,0,-652,0,-2240,0,-2126,0,-1806,0,-120,0,648,0,1398,0,1034,0,608,0,238,0,56,0,6],[0],[-1,0,-10,0,-45,0,-120,0,-208,0,-296,0,-312,0,-264,0,-202,0,-156,0,-202,0,-264,0,-312,0,-296,0,-208,0,-120,0,-45,0,-10,0,-1],[0],[0],[0],[0],[0],[0],[0],[32,0,320,0,1440,0,3840,0,6720,0,8064,0,6720,0,3840,0,1440,0,320,0,32],[0],[0],[0],[0],[0],[0],[0],[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst411Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst411Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 9)+((((1 : ℚ) : ℝ)+(z.2)^10))^2)) :=
  (hRadius9Code.add hAst409Code)
private theorem hAst411DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst411Denominator=true := by kernel_decide
private theorem hAst411DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst411Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst411Denominator hAst411DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst411Cross : equalCheck
    (mul hAst411Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst411Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst411Numerator) hAst411Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst411Code : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 9)+((((1 : ℚ) : ℝ)+(z.2)^10))^2)) :=
  hAst411Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst411Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst411Denominator)
    hAst411DenNonzero hAst411Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst412Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-120,0,-210,0,-270,0,-132,0,48,0,315,0,425,0,425,0,315,0,48,0,-132,0,-270,0,-210,0,-120,0,-45,0,-10,0,-1],[0,0,0,0,0,0,0,0,0,0,8,0,-248,0,-24,0,-288,0,528,0,48,0,528,0,-288,0,-24,0,-248,0,8],[20,-8,210,-56,966,-160,2584,-224,4480,-112,5376,112,4122,224,1638,160,-700,56,-2248,16,-2134,56,-1854,160,-232,224,536,112,1398,-112,1146,-224,720,-160,286,-56,64,-8,6],[-8,0,-76,0,-324,0,-816,0,-1348,0,-1460,0,-816,0,0,0,816,0,1100,0,1180,0,1008,0,540,0,244,0,-40],[-1,0,-10,0,-45,0,-120,0,-208,0,-296,0,-312,0,-264,0,-202,0,-156,0,-202,0,-264,0,-312,0,-296,0,-208,0,-120,0,-45,0,-10,0,-1],[0],[0],[0],[0],[0],[0],[0],[32,0,320,0,1440,0,3840,0,6720,0,8064,0,6720,0,3840,0,1440,0,320,0,32],[0],[0],[0],[0],[0],[0],[0],[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst412Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst412Raw : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 9)+((((1 : ℚ) : ℝ)+(z.2)^10))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 9)))) :=
  (hAst411Code.add hAst410Code)
private theorem hAst412DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst412Denominator=true := by kernel_decide
private theorem hAst412DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst412Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst412Denominator hAst412DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst412Cross : equalCheck
    (mul hAst412Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst412Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst412Numerator) hAst412Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst412Code : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 9)+((((1 : ℚ) : ℝ)+(z.2)^10))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 9)))) :=
  hAst412Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst412Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst412Denominator)
    hAst412DenNonzero hAst412Cross

/-- Article: proposed exact numerator for hPairLower9. -/
def hPairLower9Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-120,0,-210,0,-270,0,-132,0,48,0,315,0,425,0,425,0,315,0,48,0,-132,0,-270,0,-210,0,-120,0,-45,0,-10,0,-1],[0,0,0,0,0,0,0,0,0,0,8,0,-248,0,-24,0,-288,0,528,0,48,0,528,0,-288,0,-24,0,-248,0,8],[20,-8,210,-56,966,-160,2584,-224,4480,-112,5376,112,4122,224,1638,160,-700,56,-2248,16,-2134,56,-1854,160,-232,224,536,112,1398,-112,1146,-224,720,-160,286,-56,64,-8,6],[-8,0,-76,0,-324,0,-816,0,-1348,0,-1460,0,-816,0,0,0,816,0,1100,0,1180,0,1008,0,540,0,244,0,-40],[-1,0,-10,0,-45,0,-120,0,-208,0,-296,0,-312,0,-264,0,-202,0,-156,0,-202,0,-264,0,-312,0,-296,0,-208,0,-120,0,-45,0,-10,0,-1],[0],[0],[0],[0],[0],[0],[0],[32,0,320,0,1440,0,3840,0,6720,0,8064,0,6720,0,3840,0,1440,0,320,0,32],[0],[0],[0],[0],[0],[0],[0],[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: proposed positive denominator for hPairLower9. -/
def hPairLower9Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairLower9Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 9)+((((1 : ℚ) : ℝ)+(z.2)^10))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 9)))) :=
  (hAst412Code.congr (by
    intro z hz
    ring))
private theorem hPairLower9Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.radius z.1 z.2 9)+((((1 : ℚ) : ℝ)+(z.2)^10))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 9)))=Source.pairSlack z.1 z.2 (-1) 9 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairLower9DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairLower9Denominator=true := by kernel_decide
private theorem hPairLower9DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairLower9Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairLower9Denominator hPairLower9DenCheck hz.1 hz.2).ne'
private theorem hPairLower9Cross : equalCheck
    (mul hPairLower9Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairLower9Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairLower9Numerator) hPairLower9Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairLower9. -/
def hPairLower9Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (-1) 9) :=
  (hPairLower9Raw.congr hPairLower9Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower9Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower9Denominator)
    hPairLower9DenNonzero hPairLower9Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst413Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-120,0,-210,0,-270,0,-132,0,48,0,315,0,425,0,425,0,315,0,48,0,-132,0,-270,0,-210,0,-120,0,-45,0,-10,0,-1],[0,0,0,0,0,0,0,0,0,0,-8,0,248,0,24,0,288,0,-528,0,-48,0,-528,0,288,0,24,0,248,0,-8],[4,8,34,56,150,160,440,224,896,112,1344,-112,986,-224,-58,-160,-1324,-56,-2392,-16,-2134,-56,-1758,-160,-8,-224,760,-112,1398,112,922,224,496,160,190,56,48,8,6],[8,0,76,0,324,0,816,0,1348,0,1460,0,816,0,0,0,-816,0,-1100,0,-1180,0,-1008,0,-540,0,-244,0,40],[-1,0,-10,0,-45,0,-120,0,-208,0,-296,0,-312,0,-264,0,-202,0,-156,0,-202,0,-264,0,-312,0,-296,0,-208,0,-120,0,-45,0,-10,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst413Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst413Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 9)+(Source.radius z.1 z.2 9))) :=
  (hDiscrepancy9Code.add hRadius9Code)
private theorem hAst413DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst413Denominator=true := by kernel_decide
private theorem hAst413DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst413Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst413Denominator hAst413DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst413Cross : equalCheck
    (mul hAst413Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst413Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst413Numerator) hAst413Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst413Code : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 9)+(Source.radius z.1 z.2 9))) :=
  hAst413Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst413Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst413Denominator)
    hAst413DenNonzero hAst413Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst414Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-120,0,-210,0,-270,0,-132,0,48,0,315,0,425,0,425,0,315,0,48,0,-132,0,-270,0,-210,0,-120,0,-45,0,-10,0,-1],[0,0,0,0,0,0,0,0,0,0,-8,0,248,0,24,0,288,0,-528,0,-48,0,-528,0,288,0,24,0,248,0,-8],[20,8,194,56,870,160,2360,224,4256,112,5376,-112,4346,-224,1862,-160,-604,-56,-2232,-16,-2118,-56,-1758,-160,-8,-224,760,-112,1398,112,922,224,496,160,190,56,48,8,6],[8,0,76,0,324,0,816,0,1348,0,1460,0,816,0,0,0,-816,0,-1100,0,-1180,0,-1008,0,-540,0,-244,0,40],[-1,0,-10,0,-45,0,-120,0,-208,0,-296,0,-312,0,-264,0,-202,0,-156,0,-202,0,-264,0,-312,0,-296,0,-208,0,-120,0,-45,0,-10,0,-1],[0],[0],[0],[0],[0],[0],[0],[32,0,320,0,1440,0,3840,0,6720,0,8064,0,6720,0,3840,0,1440,0,320,0,32],[0],[0],[0],[0],[0],[0],[0],[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst414Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst414Raw : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 9)+(Source.radius z.1 z.2 9))+((((1 : ℚ) : ℝ)+(z.2)^10))^2)) :=
  (hAst413Code.add hAst409Code)
private theorem hAst414DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst414Denominator=true := by kernel_decide
private theorem hAst414DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst414Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst414Denominator hAst414DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst414Cross : equalCheck
    (mul hAst414Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst414Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst414Numerator) hAst414Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst414Code : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 9)+(Source.radius z.1 z.2 9))+((((1 : ℚ) : ℝ)+(z.2)^10))^2)) :=
  hAst414Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst414Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst414Denominator)
    hAst414DenNonzero hAst414Cross

/-- Article: proposed exact numerator for hPairUpper9. -/
def hPairUpper9Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-120,0,-210,0,-270,0,-132,0,48,0,315,0,425,0,425,0,315,0,48,0,-132,0,-270,0,-210,0,-120,0,-45,0,-10,0,-1],[0,0,0,0,0,0,0,0,0,0,-8,0,248,0,24,0,288,0,-528,0,-48,0,-528,0,288,0,24,0,248,0,-8],[20,8,194,56,870,160,2360,224,4256,112,5376,-112,4346,-224,1862,-160,-604,-56,-2232,-16,-2118,-56,-1758,-160,-8,-224,760,-112,1398,112,922,224,496,160,190,56,48,8,6],[8,0,76,0,324,0,816,0,1348,0,1460,0,816,0,0,0,-816,0,-1100,0,-1180,0,-1008,0,-540,0,-244,0,40],[-1,0,-10,0,-45,0,-120,0,-208,0,-296,0,-312,0,-264,0,-202,0,-156,0,-202,0,-264,0,-312,0,-296,0,-208,0,-120,0,-45,0,-10,0,-1],[0],[0],[0],[0],[0],[0],[0],[32,0,320,0,1440,0,3840,0,6720,0,8064,0,6720,0,3840,0,1440,0,320,0,32],[0],[0],[0],[0],[0],[0],[0],[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: proposed positive denominator for hPairUpper9. -/
def hPairUpper9Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairUpper9Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 9)+(Source.radius z.1 z.2 9)+((((1 : ℚ) : ℝ)+(z.2)^10))^2)) :=
  (hAst414Code.congr (by
    intro z hz
    ring))
private theorem hPairUpper9Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.discrepancy z.1 z.2 9)+(Source.radius z.1 z.2 9)+((((1 : ℚ) : ℝ)+(z.2)^10))^2)=Source.pairSlack z.1 z.2 (1) 9 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairUpper9DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairUpper9Denominator=true := by kernel_decide
private theorem hPairUpper9DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper9Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairUpper9Denominator hPairUpper9DenCheck hz.1 hz.2).ne'
private theorem hPairUpper9Cross : equalCheck
    (mul hPairUpper9Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper9Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper9Numerator) hPairUpper9Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairUpper9. -/
def hPairUpper9Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (1) 9) :=
  (hPairUpper9Raw.congr hPairUpper9Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper9Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper9Denominator)
    hPairUpper9DenNonzero hPairUpper9Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst415Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,0,48,16,34,16,16],[0,0,-8,0,-20,0,-16,0,-4],[1,0,2,0,0,0,-2,0,-1],[0],[0,0,-32,0,-96,0,-96,0,-32],[0],[0],[0],[0,0,16,0,48,0,48,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst415Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,48,0,48,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst415Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))) :=
  (hConstantLowerCode.add hReserveCode)
private theorem hAst415DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst415Denominator=true := by kernel_decide
private theorem hAst415DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst415Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst415Denominator hAst415DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst415Cross : equalCheck
    (mul hAst415Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst415Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst415Numerator) hAst415Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst415Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))) :=
  hAst415Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst415Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst415Denominator)
    hAst415DenNonzero hAst415Cross

/-- Article: proposed exact numerator for check00. -/
def check00Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,0,48,16,34,16,16],[0,0,-8,0,-20,0,-16,0,-4],[1,0,2,0,0,0,-2,0,-1],[0],[0,0,-32,0,-96,0,-96,0,-32],[0],[0],[0],[0,0,16,0,48,0,48,0,16]]
/-- Article: proposed positive denominator for check00. -/
def check00Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,48,0,48,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check00Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))) :=
  (hAst415Code.congr (by
    intro z hz
    ring))
private theorem check00Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))=((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check00DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check00Denominator=true := by kernel_decide
private theorem check00DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check00Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check00Denominator check00DenCheck hz.1 hz.2).ne'
private theorem check00Cross : equalCheck
    (mul check00Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check00Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check00Numerator) check00Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check00. -/
def check00Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.reserve z.2))) :=
  (check00Raw.congr check00Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check00Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check00Denominator)
    check00DenNonzero check00Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst416Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,196,0,1344,448,3256,1984,3968,2624,3204,1600,1344,512,256],[0,0,0,0,-224,0,-1328,-256,-2912,-896,-3264,-1152,-2112,-640,-784,-128,-128],[0,0,28,0,216,32,580,96,768,64,548,-64,184,-96,-4,-32,-16],[0,0,-16,0,-72,0,-112,0,-40,0,80,0,104,0,48,0,8],[1,0,4,0,-892,0,-5764,-1024,-14090,-4096,-17668,-6144,-12668,-4096,-5244,-1024,-1023],[0,0,0,0,512,0,2816,0,6400,0,7680,0,5120,0,1792,0,256],[0,0,-64,0,-320,0,-576,0,-320,0,320,0,576,0,320,0,64],[0],[0,0,0,0,1472,0,9024,512,22400,2048,29312,3072,21696,2048,8768,512,1536],[0,0,0,0,-256,0,-1408,0,-3200,0,-3840,0,-2560,0,-896,0,-128],[0,0,32,0,160,0,288,0,160,0,-160,0,-288,0,-160,0,-32],[0],[0,0,0,0,-1024,0,-6144,0,-15360,0,-20480,0,-15360,0,-6144,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst416Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst416Raw : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)))^2) :=
  (hAst415Code.pow 2)
private theorem hAst416DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst416Denominator=true := by kernel_decide
private theorem hAst416DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst416Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst416Denominator hAst416DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst416Cross : equalCheck
    (mul hAst416Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst416Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst416Numerator) hAst416Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst416Code : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)))^2) :=
  hAst416Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst416Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst416Denominator)
    hAst416DenNonzero hAst416Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst417Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-65,192,-391,496,-576,496,-400,208,-87,16,-1],[0,0,0,-32,36,-32,24,32,8,32,24,0,4],[0,0,-2,-32,14,-112,28,-144,12,-80,-2,-16,-2],[0,0,4,0,24,0,40,0,24,0,4],[-1,0,-7,0,-16,0,-16,0,-7,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst417Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,256,0,384,0,256,0,64]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst417Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))) :=
  ((RationalCode.constant Source.domain (-1)).mul hBetaNormLowerCode)
private theorem hAst417DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst417Denominator=true := by kernel_decide
private theorem hAst417DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst417Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst417Denominator hAst417DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst417Cross : equalCheck
    (mul hAst417Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst417Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst417Numerator) hAst417Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst417Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))) :=
  hAst417Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst417Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst417Denominator)
    hAst417DenNonzero hAst417Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst418Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-64,768,-740,3968,-2436,8704,-3804,9408,-2648,5312,-956,1472,-100,64,-4],[0,0,0,-128,-80,-384,-944,-512,-2544,-640,-3008,-768,-1872,-512,-656,-128,-112],[0,0,20,-128,256,-672,796,-1504,1096,-1856,748,-1344,208,-544,-28,-96,-24],[0,0,0,0,56,0,256,0,472,0,448,0,232,0,64,0,8],[-3,0,-32,0,-1016,0,-5984,-1024,-14310,-4096,-17792,-6144,-12704,-4096,-5248,-1024,-1023],[0,0,0,0,512,0,2816,0,6400,0,7680,0,5120,0,1792,0,256],[0,0,-64,0,-320,0,-576,0,-320,0,320,0,576,0,320,0,64],[0],[0,0,0,0,1472,0,9024,512,22400,2048,29312,3072,21696,2048,8768,512,1536],[0,0,0,0,-256,0,-1408,0,-3200,0,-3840,0,-2560,0,-896,0,-128],[0,0,32,0,160,0,288,0,160,0,-160,0,-288,0,-160,0,-32],[0],[0,0,0,0,-1024,0,-6144,0,-15360,0,-20480,0,-15360,0,-6144,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst418Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst418Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))))) :=
  (hAst416Code.add hAst417Code)
private theorem hAst418DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst418Denominator=true := by kernel_decide
private theorem hAst418DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst418Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst418Denominator hAst418DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst418Cross : equalCheck
    (mul hAst418Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst418Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst418Numerator) hAst418Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst418Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))))) :=
  hAst418Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst418Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst418Denominator)
    hAst418DenNonzero hAst418Cross

/-- Article: proposed exact numerator for check01. -/
def check01Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-64,768,-740,3968,-2436,8704,-3804,9408,-2648,5312,-956,1472,-100,64,-4],[0,0,0,-128,-80,-384,-944,-512,-2544,-640,-3008,-768,-1872,-512,-656,-128,-112],[0,0,20,-128,256,-672,796,-1504,1096,-1856,748,-1344,208,-544,-28,-96,-24],[0,0,0,0,56,0,256,0,472,0,448,0,232,0,64,0,8],[-3,0,-32,0,-1016,0,-5984,-1024,-14310,-4096,-17792,-6144,-12704,-4096,-5248,-1024,-1023],[0,0,0,0,512,0,2816,0,6400,0,7680,0,5120,0,1792,0,256],[0,0,-64,0,-320,0,-576,0,-320,0,320,0,576,0,320,0,64],[0],[0,0,0,0,1472,0,9024,512,22400,2048,29312,3072,21696,2048,8768,512,1536],[0,0,0,0,-256,0,-1408,0,-3200,0,-3840,0,-2560,0,-896,0,-128],[0,0,32,0,160,0,288,0,160,0,-160,0,-288,0,-160,0,-32],[0],[0,0,0,0,-1024,0,-6144,0,-15360,0,-20480,0,-15360,0,-6144,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: proposed positive denominator for check01. -/
def check01Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]
/-- Article: composition of proved source-preserving rational operations. -/
def check01Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))))) :=
  (hAst418Code.congr (by
    intro z hz
    ring))
private theorem check01Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))))=((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check01DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check01Denominator=true := by kernel_decide
private theorem check01DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check01Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check01Denominator check01DenCheck hz.1 hz.2).ne'
private theorem check01Cross : equalCheck
    (mul check01Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check01Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check01Numerator) check01Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check01. -/
def check01Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.reserve z.2)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))))) :=
  (check01Raw.congr check01Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check01Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check01Denominator)
    check01DenNonzero check01Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst419Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,192,-135,496,-192,496,-144,208,-23,16,-1],[0,0,0,-32,36,-32,24,32,8,32,24,0,4],[0,0,-2,-32,14,-112,28,-144,12,-80,-2,-16,-2],[0,0,4,0,24,0,40,0,24,0,4],[-1,0,-7,0,-16,0,-16,0,-7,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst419Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,256,0,384,0,256,0,64]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst419Raw : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))))) :=
  ((RationalCode.constant Source.domain 1).add hAst417Code)
private theorem hAst419DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst419Denominator=true := by kernel_decide
private theorem hAst419DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst419Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst419Denominator hAst419DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst419Cross : equalCheck
    (mul hAst419Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst419Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst419Numerator) hAst419Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst419Code : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))))) :=
  hAst419Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst419Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst419Denominator)
    hAst419DenNonzero hAst419Cross

/-- Article: proposed exact numerator for check02. -/
def check02Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,192,-135,496,-192,496,-144,208,-23,16,-1],[0,0,0,-32,36,-32,24,32,8,32,24,0,4],[0,0,-2,-32,14,-112,28,-144,12,-80,-2,-16,-2],[0,0,4,0,24,0,40,0,24,0,4],[-1,0,-7,0,-16,0,-16,0,-7,0,-1]]
/-- Article: proposed positive denominator for check02. -/
def check02Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,64,0,256,0,384,0,256,0,64]]
/-- Article: composition of proved source-preserving rational operations. -/
def check02Raw : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))))) :=
  (hAst419Code.congr (by
    intro z hz
    ring))
private theorem check02Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))))=(((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1)))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check02DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check02Denominator=true := by kernel_decide
private theorem check02DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check02Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check02Denominator check02DenCheck hz.1 hz.2).ne'
private theorem check02Cross : equalCheck
    (mul check02Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check02Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check02Numerator) check02Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check02. -/
def check02Code : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm z.1 z.2 (-1))))) :=
  (check02Raw.congr check02Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check02Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check02Denominator)
    check02DenNonzero check02Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst420Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,6,0,-6,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst420Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,40,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst420Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(phaseBudget z.1))) :=
  ((RationalCode.constant Source.domain (-1)).mul hEpsilonCode)
private theorem hAst420DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst420Denominator=true := by kernel_decide
private theorem hAst420DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst420Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst420Denominator hAst420DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst420Cross : equalCheck
    (mul hAst420Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst420Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst420Numerator) hAst420Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst420Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(phaseBudget z.1))) :=
  hAst420Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst420Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst420Denominator)
    hAst420DenNonzero hAst420Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst421Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,6,46,-34,40,-6,-6,-6,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst421Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,40,0,120,0,120,0,40]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst421Raw : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (-1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  (hQuadraticLowerCode.add hAst420Code)
private theorem hAst421DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst421Denominator=true := by kernel_decide
private theorem hAst421DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst421Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst421Denominator hAst421DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst421Cross : equalCheck
    (mul hAst421Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst421Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst421Numerator) hAst421Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst421Code : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (-1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  hAst421Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst421Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst421Denominator)
    hAst421DenNonzero hAst421Cross

/-- Article: proposed exact numerator for check03. -/
def check03Numerator : polyak.Numerics.IntegerBivariate.Source := [[3,6,46,-34,40,-6,-6,-6,-3]]
/-- Article: proposed positive denominator for check03. -/
def check03Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,40,0,120,0,120,0,40]]
/-- Article: composition of proved source-preserving rational operations. -/
def check03Raw : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (-1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  (hAst421Code.congr (by
    intro z hz
    ring))
private theorem check03Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.quadratic z.1 (-1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))=((Source.quadratic z.1 (-1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1))) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check03DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check03Denominator=true := by kernel_decide
private theorem check03DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check03Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check03Denominator check03DenCheck hz.1 hz.2).ne'
private theorem check03Cross : equalCheck
    (mul check03Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check03Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check03Numerator) check03Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check03. -/
def check03Code : RationalCode Source.domain (fun z => ((Source.quadratic z.1 (-1))+((((-1) : ℚ) : ℝ)*(phaseBudget z.1)))) :=
  (check03Raw.congr check03Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check03Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check03Denominator)
    check03DenNonzero check03Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst422Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-2,16,-14,16],[0,0,-8,0,-12,0,-4],[1,0,1,0,-1,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst422Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,32,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst422Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1)))) :=
  (hConstantLowerCode.add hQuadraticLowerCode)
private theorem hAst422DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst422Denominator=true := by kernel_decide
private theorem hAst422DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst422Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst422Denominator hAst422DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst422Cross : equalCheck
    (mul hAst422Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst422Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst422Numerator) hAst422Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst422Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1)))) :=
  hAst422Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst422Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst422Denominator)
    hAst422DenNonzero hAst422Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst423Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,16,18,16,16],[0,0,-8,0,-12,0,-4],[1,0,1,0,-1,0,-1],[0],[0,0,-32,0,-64,0,-32],[0],[0],[0],[0,0,16,0,32,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst423Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,32,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst423Raw : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1)))+(Source.reserve z.2))) :=
  (hAst422Code.add hReserveCode)
private theorem hAst423DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst423Denominator=true := by kernel_decide
private theorem hAst423DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst423Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst423Denominator hAst423DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst423Cross : equalCheck
    (mul hAst423Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst423Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst423Numerator) hAst423Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst423Code : RationalCode Source.domain (fun z => (((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1)))+(Source.reserve z.2))) :=
  hAst423Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst423Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst423Denominator)
    hAst423DenNonzero hAst423Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst424Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,16],[0],[-1,0,-4,0,-1],[0],[0,0,-32,0,-32],[0],[0],[0],[0,0,16,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst424Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst424Raw : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (-1) 0))) :=
  (hAst423Code.add hResidueLower0Code)
private theorem hAst424DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst424Denominator=true := by kernel_decide
private theorem hAst424DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst424Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst424Denominator hAst424DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst424Cross : equalCheck
    (mul hAst424Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst424Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst424Numerator) hAst424Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst424Code : RationalCode Source.domain (fun z => ((((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1)))+(Source.reserve z.2))+(Source.residue z.1 z.2 (-1) 0))) :=
  hAst424Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst424Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst424Denominator)
    hAst424DenNonzero hAst424Cross

/-- Article: proposed exact numerator for check04. -/
def check04Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,16],[0],[-1,0,-4,0,-1],[0],[0,0,-32,0,-32],[0],[0],[0],[0,0,16,0,16]]
/-- Article: proposed positive denominator for check04. -/
def check04Denominator : polyak.Numerics.IntegerBivariate.Source := [[0,0,16,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check04Raw : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 0))) :=
  (hAst424Code.congr (by
    intro z hz
    ring))
private theorem check04Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 0))=((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 0)) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check04DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check04Denominator=true := by kernel_decide
private theorem check04DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check04Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check04Denominator check04DenCheck hz.1 hz.2).ne'
private theorem check04Cross : equalCheck
    (mul check04Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check04Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check04Numerator) check04Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check04. -/
def check04Code : RationalCode Source.domain (fun z => ((Source.constant z.1 z.2 (-1))+(Source.quadratic z.1 (-1))+(Source.reserve z.2)+(Source.residue z.1 z.2 (-1) 0))) :=
  (check04Raw.congr check04Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check04Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check04Denominator)
    check04DenNonzero check04Cross

end
end polyak.Certificates.Startup.Codes
