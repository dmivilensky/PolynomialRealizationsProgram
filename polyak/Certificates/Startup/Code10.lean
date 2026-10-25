import polyak.Certificates.Startup.Code09

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: canonical numerator for one arithmetic source node. -/
def hAst275Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-37,0,-13,0,21,0,58,0,58,0,21,0,-13,0,-37,0,-21,0,-7,0,-1],[0,0,0,0,0,0,0,0,48,0,-16,0,16,0,-96,0,16,0,-16,0,48],[4,8,22,32,72,40,164,0,120,-40,-80,-32,-266,-16,-326,-32,-74,-40,68,0,178,40,82,32,30,8,6],[8,0,52,0,144,0,204,0,116,0,-20,0,-148,0,-172,0,-124,0,-64,0,4],[-1,0,-7,0,-21,0,-45,0,-55,0,-44,0,-38,0,-44,0,-55,0,-45,0,-21,0,-7,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst275Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst275Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 6)+(Source.radius z.1 z.2 6))) :=
  (hDiscrepancy6Code.add hRadius6Code)
private theorem hAst275DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst275Denominator=true := by kernel_decide
private theorem hAst275DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst275Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst275Denominator hAst275DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst275Cross : equalCheck
    (mul hAst275Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst275Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst275Numerator) hAst275Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst275Code : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 6)+(Source.radius z.1 z.2 6))) :=
  hAst275Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst275Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst275Denominator)
    hAst275DenNonzero hAst275Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst276Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-37,0,-13,0,21,0,58,0,58,0,21,0,-13,0,-37,0,-21,0,-7,0,-1],[0,0,0,0,0,0,0,0,48,0,-16,0,16,0,-96,0,16,0,-16,0,48],[20,8,134,32,408,40,724,0,680,-40,256,-32,-154,-16,-310,-32,-74,-40,68,0,178,40,82,32,30,8,6],[8,0,52,0,144,0,204,0,116,0,-20,0,-148,0,-172,0,-124,0,-64,0,4],[-1,0,-7,0,-21,0,-45,0,-55,0,-44,0,-38,0,-44,0,-55,0,-45,0,-21,0,-7,0,-1],[0],[0],[0],[32,0,224,0,672,0,1120,0,1120,0,672,0,224,0,32],[0],[0],[0],[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst276Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst276Raw : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 6)+(Source.radius z.1 z.2 6))+((((1 : ℚ) : ℝ)+(z.2)^6))^2)) :=
  (hAst275Code.add hAst228Code)
private theorem hAst276DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst276Denominator=true := by kernel_decide
private theorem hAst276DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst276Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst276Denominator hAst276DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst276Cross : equalCheck
    (mul hAst276Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst276Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst276Numerator) hAst276Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst276Code : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 6)+(Source.radius z.1 z.2 6))+((((1 : ℚ) : ℝ)+(z.2)^6))^2)) :=
  hAst276Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst276Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst276Denominator)
    hAst276DenNonzero hAst276Cross

/-- Article: proposed exact numerator for hPairUpper6. -/
def hPairUpper6Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-37,0,-13,0,21,0,58,0,58,0,21,0,-13,0,-37,0,-21,0,-7,0,-1],[0,0,0,0,0,0,0,0,48,0,-16,0,16,0,-96,0,16,0,-16,0,48],[20,8,134,32,408,40,724,0,680,-40,256,-32,-154,-16,-310,-32,-74,-40,68,0,178,40,82,32,30,8,6],[8,0,52,0,144,0,204,0,116,0,-20,0,-148,0,-172,0,-124,0,-64,0,4],[-1,0,-7,0,-21,0,-45,0,-55,0,-44,0,-38,0,-44,0,-55,0,-45,0,-21,0,-7,0,-1],[0],[0],[0],[32,0,224,0,672,0,1120,0,1120,0,672,0,224,0,32],[0],[0],[0],[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: proposed positive denominator for hPairUpper6. -/
def hPairUpper6Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairUpper6Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 6)+(Source.radius z.1 z.2 6)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)) :=
  (hAst276Code.congr (by
    intro z hz
    ring))
private theorem hPairUpper6Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.discrepancy z.1 z.2 6)+(Source.radius z.1 z.2 6)+((((1 : ℚ) : ℝ)+(z.2)^6))^2)=Source.pairSlack z.1 z.2 (1) 6 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairUpper6DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairUpper6Denominator=true := by kernel_decide
private theorem hPairUpper6DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper6Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairUpper6Denominator hPairUpper6DenCheck hz.1 hz.2).ne'
private theorem hPairUpper6Cross : equalCheck
    (mul hPairUpper6Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper6Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper6Numerator) hPairUpper6Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairUpper6. -/
def hPairUpper6Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (1) 6) :=
  (hPairUpper6Raw.congr hPairUpper6Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper6Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper6Denominator)
    hPairUpper6DenNonzero hPairUpper6Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst277Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst277Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst277Raw : RationalCode Source.domain (fun z => (z.1)^7) :=
  ((RationalCode.first Source.domain).pow 7)
private theorem hAst277DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst277Denominator=true := by kernel_decide
private theorem hAst277DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst277Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst277Denominator hAst277DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst277Cross : equalCheck
    (mul hAst277Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst277Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst277Numerator) hAst277Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst277Code : RationalCode Source.domain (fun z => (z.1)^7) :=
  hAst277Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst277Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst277Denominator)
    hAst277DenNonzero hAst277Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst278Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,7,0,-14,0,-7,0,-36,0,-7,0,-14,0,7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst278Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst278Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 7 (radialCosine z.1))*(z.1)^7)) :=
  (hT7Code.mul hAst277Code)
private theorem hAst278DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst278Denominator=true := by kernel_decide
private theorem hAst278DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst278Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst278Denominator hAst278DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst278Cross : equalCheck
    (mul hAst278Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst278Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst278Numerator) hAst278Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst278Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 7 (radialCosine z.1))*(z.1)^7)) :=
  hAst278Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst278Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst278Denominator)
    hAst278DenNonzero hAst278Cross

/-- Article: proposed exact numerator for hPowerReal7. -/
def hPowerReal7Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,7,0,-14,0,-7,0,-36,0,-7,0,-14,0,7]]
/-- Article: proposed positive denominator for hPowerReal7. -/
def hPowerReal7Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerReal7Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 7 (radialCosine z.1))*(z.1)^7)) :=
  (hAst278Code.congr (by
    intro z hz
    ring))
private theorem hPowerReal7Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebT 7 (radialCosine z.1))*(z.1)^7)=Source.powerReal z.1 7 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.powerReal]; ring
private theorem hPowerReal7DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerReal7Denominator=true := by kernel_decide
private theorem hPowerReal7DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal7Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerReal7Denominator hPowerReal7DenCheck hz.1 hz.2).ne'
private theorem hPowerReal7Cross : equalCheck
    (mul hPowerReal7Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal7Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal7Numerator) hPowerReal7Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerReal7. -/
def hPowerReal7Code : RationalCode Source.domain (fun z => Source.powerReal z.1 7) :=
  (hPowerReal7Raw.congr hPowerReal7Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal7Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal7Denominator)
    hPowerReal7DenNonzero hPowerReal7Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst279Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,18,0,1,0,28,0,1,0,18,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst279Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst279Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 6 (radialCosine z.1))*(z.1)^6)) :=
  (hU6Code.mul hAst122Code)
private theorem hAst279DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst279Denominator=true := by kernel_decide
private theorem hAst279DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst279Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst279Denominator hAst279DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst279Cross : equalCheck
    (mul hAst279Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst279Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst279Numerator) hAst279Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst279Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 6 (radialCosine z.1))*(z.1)^6)) :=
  hAst279Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst279Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst279Denominator)
    hAst279DenNonzero hAst279Cross

/-- Article: proposed exact numerator for hPowerImag7. -/
def hPowerImag7Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,-1,0,18,0,1,0,28,0,1,0,18,0,-1]]
/-- Article: proposed positive denominator for hPowerImag7. -/
def hPowerImag7Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,6,0,15,0,20,0,15,0,6,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerImag7Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebU 6 (radialCosine z.1))*(z.1)^6)) :=
  (hAst279Code.congr (by
    intro z hz
    ring))
private theorem hPowerImag7Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebU 6 (radialCosine z.1))*(z.1)^6)=Source.powerImag z.1 7 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rw [Source.powerImag,ite_eq_right (by decide)]; ring
private theorem hPowerImag7DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerImag7Denominator=true := by kernel_decide
private theorem hPowerImag7DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag7Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerImag7Denominator hPowerImag7DenCheck hz.1 hz.2).ne'
private theorem hPowerImag7Cross : equalCheck
    (mul hPowerImag7Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag7Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag7Numerator) hPowerImag7Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerImag7. -/
def hPowerImag7Code : RationalCode Source.domain (fun z => Source.powerImag z.1 7) :=
  (hPowerImag7Raw.congr hPowerImag7Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag7Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerImag7Denominator)
    hPowerImag7DenNonzero hPowerImag7Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst280Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,-7,0,14,0,7,0,36,0,7,0,14,0,-7],[0],[0,0,0,0,0,0,0,0,-7,0,14,0,7,0,36,0,7,0,14,0,-7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst280Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst280Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 7)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerReal7Code.mul hSRealCode)
private theorem hAst280DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst280Denominator=true := by kernel_decide
private theorem hAst280DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst280Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst280Denominator hAst280DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst280Cross : equalCheck
    (mul hAst280Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst280Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst280Numerator) hAst280Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst280Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 7)*(Source.multiplierReal z.1 z.2))) :=
  hAst280Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst280Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst280Denominator)
    hAst280DenNonzero hAst280Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst281Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-17,0,-18,0,-47,0,-30,0,-47,0,-18,0,-17,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst281Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst281Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))) :=
  (hAst002Code.mul hPowerImag7Code)
private theorem hAst281DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst281Denominator=true := by kernel_decide
private theorem hAst281DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst281Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst281Denominator hAst281DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst281Cross : equalCheck
    (mul hAst281Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst281Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst281Numerator) hAst281Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst281Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))) :=
  hAst281Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst281Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst281Denominator)
    hAst281DenNonzero hAst281Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst282Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-17,0,-18,0,-47,0,-30,0,-47,0,-18,0,-17,0,1],[0],[0,0,0,0,0,0,-1,0,17,0,18,0,47,0,30,0,47,0,18,0,17,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst282Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst282Raw : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))*(Source.multiplierImag z.1 z.2))) :=
  (hAst281Code.mul hSImagCode)
private theorem hAst282DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst282Denominator=true := by kernel_decide
private theorem hAst282DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst282Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst282Denominator hAst282DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst282Cross : equalCheck
    (mul hAst282Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst282Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst282Numerator) hAst282Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst282Code : RationalCode Source.domain (fun z => ((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))*(Source.multiplierImag z.1 z.2))) :=
  hAst282Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst282Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst282Denominator)
    hAst282DenNonzero hAst282Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst283Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-24,0,-4,0,-40,0,6,0,-40,0,-4,0,-24,0,1],[0],[0,0,0,0,0,0,-1,0,10,0,32,0,54,0,66,0,54,0,32,0,10,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst283Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst283Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 7)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))*(Source.multiplierImag z.1 z.2)))) :=
  (hAst280Code.add hAst282Code)
private theorem hAst283DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst283Denominator=true := by kernel_decide
private theorem hAst283DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst283Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst283Denominator hAst283DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst283Cross : equalCheck
    (mul hAst283Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst283Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst283Numerator) hAst283Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst283Code : RationalCode Source.domain (fun z => (((Source.powerReal z.1 7)*(Source.multiplierReal z.1 z.2))+((((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))*(Source.multiplierImag z.1 z.2)))) :=
  hAst283Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst283Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst283Denominator)
    hAst283DenNonzero hAst283Cross

/-- Article: proposed exact numerator for hGradientReal7. -/
def hGradientReal7Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-24,0,-4,0,-40,0,6,0,-40,0,-4,0,-24,0,1],[0],[0,0,0,0,0,0,-1,0,10,0,32,0,54,0,66,0,54,0,32,0,10,0,-1]]
/-- Article: proposed positive denominator for hGradientReal7. -/
def hGradientReal7Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientReal7Raw : RationalCode Source.domain (fun z => (((Source.powerReal z.1 7)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 7)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst283Code.congr (by
    intro z hz
    ring))
private theorem hGradientReal7Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerReal z.1 7)*(Source.multiplierReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 7)*(Source.multiplierImag z.1 z.2)))=Source.gradientReal z.1 z.2 7 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientReal]; ring
private theorem hGradientReal7DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientReal7Denominator=true := by kernel_decide
private theorem hGradientReal7DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal7Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientReal7Denominator hGradientReal7DenCheck hz.1 hz.2).ne'
private theorem hGradientReal7Cross : equalCheck
    (mul hGradientReal7Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal7Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal7Numerator) hGradientReal7Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientReal7. -/
def hGradientReal7Code : RationalCode Source.domain (fun z => Source.gradientReal z.1 z.2 7) :=
  (hGradientReal7Raw.congr hGradientReal7Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal7Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientReal7Denominator)
    hGradientReal7DenNonzero hGradientReal7Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst284Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-18,0,-1,0,-28,0,-1,0,-18,0,1],[0],[0,0,0,0,0,0,1,0,-18,0,-1,0,-28,0,-1,0,-18,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst284Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst284Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 7)*(Source.multiplierReal z.1 z.2))) :=
  (hPowerImag7Code.mul hSRealCode)
private theorem hAst284DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst284Denominator=true := by kernel_decide
private theorem hAst284DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst284Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst284Denominator hAst284DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst284Cross : equalCheck
    (mul hAst284Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst284Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst284Numerator) hAst284Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst284Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 7)*(Source.multiplierReal z.1 z.2))) :=
  hAst284Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst284Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst284Denominator)
    hAst284DenNonzero hAst284Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst285Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,7,0,-14,0,-7,0,-36,0,-7,0,-14,0,7],[0],[0,0,0,0,0,0,-7,0,14,0,7,0,36,0,7,0,14,0,-7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst285Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst285Raw : RationalCode Source.domain (fun z => ((Source.powerReal z.1 7)*(Source.multiplierImag z.1 z.2))) :=
  (hPowerReal7Code.mul hSImagCode)
private theorem hAst285DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst285Denominator=true := by kernel_decide
private theorem hAst285DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst285Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst285Denominator hAst285DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst285Cross : equalCheck
    (mul hAst285Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst285Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst285Numerator) hAst285Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst285Code : RationalCode Source.domain (fun z => ((Source.powerReal z.1 7)*(Source.multiplierImag z.1 z.2))) :=
  hAst285Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst285Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst285Denominator)
    hAst285DenNonzero hAst285Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst286Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,4,0,-16,0,-4,0,-32,0,-4,0,-16,0,4],[0],[0,0,0,0,0,0,-3,0,-2,0,3,0,4,0,3,0,-2,0,-3]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst286Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst286Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 7)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 7)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst284Code.add hAst285Code)
private theorem hAst286DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst286Denominator=true := by kernel_decide
private theorem hAst286DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst286Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst286Denominator hAst286DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst286Cross : equalCheck
    (mul hAst286Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst286Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst286Numerator) hAst286Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst286Code : RationalCode Source.domain (fun z => (((Source.powerImag z.1 7)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 7)*(Source.multiplierImag z.1 z.2)))) :=
  hAst286Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst286Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst286Denominator)
    hAst286DenNonzero hAst286Cross

/-- Article: proposed exact numerator for hGradientImag7. -/
def hGradientImag7Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,4,0,-16,0,-4,0,-32,0,-4,0,-16,0,4],[0],[0,0,0,0,0,0,-3,0,-2,0,3,0,4,0,3,0,-2,0,-3]]
/-- Article: proposed positive denominator for hGradientImag7. -/
def hGradientImag7Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hGradientImag7Raw : RationalCode Source.domain (fun z => (((Source.powerImag z.1 7)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 7)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst286Code.congr (by
    intro z hz
    ring))
private theorem hGradientImag7Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.powerImag z.1 7)*(Source.multiplierReal z.1 z.2))+((Source.powerReal z.1 7)*(Source.multiplierImag z.1 z.2)))=Source.gradientImag z.1 z.2 7 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.gradientImag]; ring
private theorem hGradientImag7DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hGradientImag7Denominator=true := by kernel_decide
private theorem hGradientImag7DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag7Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hGradientImag7Denominator hGradientImag7DenCheck hz.1 hz.2).ne'
private theorem hGradientImag7Cross : equalCheck
    (mul hGradientImag7Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag7Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag7Numerator) hGradientImag7Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hGradientImag7. -/
def hGradientImag7Code : RationalCode Source.domain (fun z => Source.gradientImag z.1 z.2 7) :=
  (hGradientImag7Raw.congr hGradientImag7Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag7Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hGradientImag7Denominator)
    hGradientImag7DenNonzero hGradientImag7Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst287Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-24,0,-4,0,-40,0,6,0,-40,0,-4,0,-24,0,1],[0],[-2,0,-15,0,-49,0,-92,0,-95,0,-45,0,19,0,57,0,53,0,32,0,10,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst287Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst287Raw : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  (hGradientReal7Code.add hAst009Code)
private theorem hAst287DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst287Denominator=true := by kernel_decide
private theorem hAst287DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst287Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst287Denominator hAst287DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst287Cross : equalCheck
    (mul hAst287Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst287Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst287Numerator) hAst287Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst287Code : RationalCode Source.domain (fun z => ((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))) :=
  hAst287Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst287Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst287Denominator)
    hAst287DenNonzero hAst287Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst288Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,7,0,21,0,36,0,11,0,17,0,-33,0,7,0,-40,0,-4,0,-24,0,1],[0],[-1,0,-8,0,-28,0,-57,0,-60,0,-24,0,26,0,58,0,53,0,32,0,10,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst288Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst288Raw : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  (hAst287Code.add hAst010Code)
private theorem hAst288DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst288Denominator=true := by kernel_decide
private theorem hAst288DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst288Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst288Denominator hAst288DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst288Cross : equalCheck
    (mul hAst288Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst288Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst288Numerator) hAst288Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst288Code : RationalCode Source.domain (fun z => (((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2)))) :=
  hAst288Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst288Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst288Denominator)
    hAst288DenNonzero hAst288Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst289Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,1,0,14,0,91,0,366,0,967,0,1700,0,1930,0,1058,0,-23,0,-2276,0,-1717,0,-4350,0,-835,0,-3596,0,2097,0,-1090,0,3162,0,-82,0,1950,0,112,0,568,0,-48,0,1],[0],[0,0,-2,0,-30,0,-210,0,-914,0,-2692,0,-5508,0,-7730,0,-6540,0,-1160,0,6564,0,12140,0,13368,0,10380,0,4800,0,-572,0,-4868,0,-6246,0,-5510,0,-3498,0,-1430,0,-408,0,68,0,-2],[0],[1,0,16,0,120,0,562,0,1816,0,4200,0,6941,0,7652,0,3846,0,-4244,0,-12656,0,-16200,0,-12660,0,-4452,0,3498,0,7452,0,7089,0,4500,0,1968,0,534,0,36,0,-20,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst289Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,64,0,480,0,2240,0,7280,0,17472,0,32032,0,45760,0,51480,0,45760,0,32032,0,17472,0,7280,0,2240,0,480,0,64,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst289Raw : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  (hAst288Code.pow 2)
private theorem hAst289DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst289Denominator=true := by kernel_decide
private theorem hAst289DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst289Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst289Denominator hAst289DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst289Cross : equalCheck
    (mul hAst289Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst289Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst289Numerator) hAst289Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst289Code : RationalCode Source.domain (fun z => ((((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2) :=
  hAst289Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst289Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst289Denominator)
    hAst289DenNonzero hAst289Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst290Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-14,0,-91,0,-366,0,-967,0,-1700,0,-1930,0,-1058,0,23,0,2276,0,1717,0,4350,0,835,0,3596,0,-2097,0,1090,0,-3162,0,82,0,-1950,0,-112,0,-568,0,48,0,-1],[0],[0,0,2,0,30,0,210,0,914,0,2692,0,5508,0,7730,0,6540,0,1160,0,-6564,0,-12140,0,-13368,0,-10380,0,-4800,0,572,0,4868,0,6246,0,5510,0,3498,0,1430,0,408,0,-68,0,2],[0],[-1,0,-16,0,-120,0,-562,0,-1816,0,-4200,0,-6941,0,-7652,0,-3846,0,4244,0,12656,0,16200,0,12660,0,4452,0,-3498,0,-7452,0,-7089,0,-4500,0,-1968,0,-534,0,-36,0,20,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst290Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,256,0,1920,0,8960,0,29120,0,69888,0,128128,0,183040,0,205920,0,183040,0,128128,0,69888,0,29120,0,8960,0,1920,0,256,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst290Raw : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  ((RationalCode.constant Source.domain (-1/4)).mul hAst289Code)
private theorem hAst290DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst290Denominator=true := by kernel_decide
private theorem hAst290DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst290Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst290Denominator hAst290DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst290Cross : equalCheck
    (mul hAst290Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst290Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst290Numerator) hAst290Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst290Code : RationalCode Source.domain (fun z => ((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)) :=
  hAst290Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst290Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst290Denominator)
    hAst290DenNonzero hAst290Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst291Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-7,0,-21,0,-35,0,-28,0,-35,0,-14,0,-37,0,-7,0,-14,0,7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst291Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,35,0,21,0,7,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst291Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7))) :=
  ((RationalCode.constant Source.domain (-1)).add hPowerReal7Code)
private theorem hAst291DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst291Denominator=true := by kernel_decide
private theorem hAst291DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst291Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst291Denominator hAst291DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst291Cross : equalCheck
    (mul hAst291Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst291Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst291Numerator) hAst291Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst291Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7))) :=
  hAst291Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst291Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst291Denominator)
    hAst291DenNonzero hAst291Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst292Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,14,0,91,0,364,0,987,0,1932,0,2919,0,3700,0,4354,0,4620,0,5075,0,4032,0,3864,0,1820,0,2153,0,420,0,889,0,-322,0,98,0,-196,0,49]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst292Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,14,0,91,0,364,0,1001,0,2002,0,3003,0,3432,0,3003,0,2002,0,1001,0,364,0,91,0,14,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst292Raw : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2) :=
  (hAst291Code.pow 2)
private theorem hAst292DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst292Denominator=true := by kernel_decide
private theorem hAst292DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst292Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst292Denominator hAst292DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst292Cross : equalCheck
    (mul hAst292Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst292Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst292Numerator) hAst292Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst292Code : RationalCode Source.domain (fun z => (((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2) :=
  hAst292Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst292Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst292Denominator)
    hAst292DenNonzero hAst292Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst293Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,14,0,91,0,364,0,987,0,1932,0,2919,0,3700,0,4354,0,4620,0,5075,0,4032,0,3864,0,1820,0,2153,0,420,0,889,0,-322,0,98,0,-196,0,49]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst293Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,56,0,364,0,1456,0,4004,0,8008,0,12012,0,13728,0,12012,0,8008,0,4004,0,1456,0,364,0,56,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst293Raw : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2)) :=
  ((RationalCode.constant Source.domain (1/4)).mul hAst292Code)
private theorem hAst293DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst293Denominator=true := by kernel_decide
private theorem hAst293DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst293Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst293Denominator hAst293DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst293Cross : equalCheck
    (mul hAst293Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst293Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst293Numerator) hAst293Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst293Code : RationalCode Source.domain (fun z => ((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2)) :=
  hAst293Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst293Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst293Denominator)
    hAst293DenNonzero hAst293Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst294Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,8,0,-32,0,-8,0,-64,0,-8,0,-32,0,8],[0],[-1,0,-7,0,-21,0,-35,0,-41,0,-25,0,-1,0,7,0,6,0,-4,0,-6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst294Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst294Raw : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  (hGradientImag7Code.add hAst018Code)
private theorem hAst294DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst294Denominator=true := by kernel_decide
private theorem hAst294DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst294Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst294Denominator hAst294DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst294Cross : equalCheck
    (mul hAst294Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst294Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst294Numerator) hAst294Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst294Code : RationalCode Source.domain (fun z => ((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))) :=
  hAst294Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst294Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst294Denominator)
    hAst294DenNonzero hAst294Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst295Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,-7,0,-21,0,-35,0,-27,0,-53,0,-15,0,-65,0,-8,0,-32,0,8],[0],[0,0,0,0,0,0,-6,0,-4,0,6,0,8,0,6,0,-4,0,-6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst295Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst295Raw : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  (hAst294Code.add hAst019Code)
private theorem hAst295DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst295Denominator=true := by kernel_decide
private theorem hAst295DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst295Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst295Denominator hAst295DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst295Cross : equalCheck
    (mul hAst295Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst295Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst295Numerator) hAst295Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst295Code : RationalCode Source.domain (fun z => (((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2)))) :=
  hAst295Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst295Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst295Denominator)
    hAst295DenNonzero hAst295Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst296Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,14,0,91,0,364,0,985,0,1954,0,3131,0,4456,0,5995,0,6818,0,8937,0,6892,0,9451,0,3966,0,7425,0,1152,0,3984,0,-528,0,896,0,-512,0,64],[0],[0,0,0,0,0,0,12,0,92,0,296,0,488,0,228,0,20,0,-464,0,-336,0,-204,0,-572,0,-408,0,-600,0,188,0,588,0,448,0,320,0,-96],[0],[0,0,0,0,0,0,0,0,0,0,0,0,36,0,48,0,-56,0,-144,0,-100,0,96,0,240,0,96,0,-100,0,-144,0,-56,0,48,0,36]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst296Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[4,0,56,0,364,0,1456,0,4004,0,8008,0,12012,0,13728,0,12012,0,8008,0,4004,0,1456,0,364,0,56,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst296Raw : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  (hAst295Code.pow 2)
private theorem hAst296DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst296Denominator=true := by kernel_decide
private theorem hAst296DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst296Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst296Denominator hAst296DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst296Cross : equalCheck
    (mul hAst296Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst296Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst296Numerator) hAst296Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst296Code : RationalCode Source.domain (fun z => ((((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2) :=
  hAst296Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst296Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst296Denominator)
    hAst296DenNonzero hAst296Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst297Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-15,0,-106,0,-469,0,-1440,0,-3303,0,-6070,0,-9541,0,-13582,0,-17269,0,-21750,0,-22647,0,-25280,0,-20309,0,-20842,0,-12543,0,-12561,0,-4608,0,-4352,0,144,0,-448,0,448,0,-64],[0],[0,0,0,0,0,0,0,0,-12,0,-104,0,-400,0,-876,0,-1012,0,-736,0,216,0,780,0,1004,0,1112,0,1184,0,1580,0,820,0,-176,0,-1224,0,-1356,0,-672,0,-224,0,96],[0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-36,0,-84,0,-28,0,152,0,300,0,148,0,-236,0,-432,0,-236,0,148,0,300,0,152,0,-28,0,-84,0,-36]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst297Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,256,0,1920,0,8960,0,29120,0,69888,0,128128,0,183040,0,205920,0,183040,0,128128,0,69888,0,29120,0,8960,0,1920,0,256,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst297Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  (hAst023Code.mul hAst296Code)
private theorem hAst297DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst297Denominator=true := by kernel_decide
private theorem hAst297DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst297Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst297Denominator hAst297DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst297Cross : equalCheck
    (mul hAst297Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst297Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst297Numerator) hAst297Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst297Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)) :=
  hAst297Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst297Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst297Denominator)
    hAst297DenNonzero hAst297Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst298Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,1,0,-36,0,322,0,-20,0,1007,0,56,0,1436,0,56,0,1007,0,-20,0,322,0,-36,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst298Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,12,0,66,0,220,0,495,0,792,0,924,0,792,0,495,0,220,0,66,0,12,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst298Raw : RationalCode Source.domain (fun z => ((Source.powerImag z.1 7))^2) :=
  (hPowerImag7Code.pow 2)
private theorem hAst298DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst298Denominator=true := by kernel_decide
private theorem hAst298DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst298Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst298Denominator hAst298DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst298Cross : equalCheck
    (mul hAst298Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst298Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst298Numerator) hAst298Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst298Code : RationalCode Source.domain (fun z => ((Source.powerImag z.1 7))^2) :=
  hAst298Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst298Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst298Denominator)
    hAst298DenNonzero hAst298Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst299Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-35,0,287,0,266,0,1309,0,1043,0,2499,0,1548,0,2499,0,1043,0,1309,0,266,0,287,0,-35,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst299Denominator : polyak.Numerics.IntegerBivariate.Source := [[4,0,56,0,364,0,1456,0,4004,0,8008,0,12012,0,13728,0,12012,0,8008,0,4004,0,1456,0,364,0,56,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst299Raw : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 7))^2)) :=
  (hAst026Code.mul hAst298Code)
private theorem hAst299DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst299Denominator=true := by kernel_decide
private theorem hAst299DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst299Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst299Denominator hAst299DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst299Cross : equalCheck
    (mul hAst299Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst299Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst299Numerator) hAst299Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst299Code : RationalCode Source.domain (fun z => (((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 7))^2)) :=
  hAst299Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst299Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst299Denominator)
    hAst299DenNonzero hAst299Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst300Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,0,-14,0,-91,0,-366,0,-967,0,-1700,0,-1930,0,-1058,0,23,0,2276,0,1717,0,4350,0,835,0,3596,0,-2097,0,1090,0,-3162,0,82,0,-1950,0,-112,0,-568,0,48,0,-1],[0],[4,0,66,0,510,0,2450,0,8138,0,19772,0,36588,0,53610,0,65232,0,69272,0,68112,0,63068,0,54644,0,43940,0,33828,0,26756,0,20396,0,13750,0,6882,0,2210,0,450,0,16,0,128,0,2],[0],[-1,0,-16,0,-120,0,-562,0,-1816,0,-4200,0,-6941,0,-7652,0,-3846,0,4244,0,12656,0,16200,0,12660,0,4452,0,-3498,0,-7452,0,-7089,0,-4500,0,-1968,0,-534,0,-36,0,20,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst300Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,256,0,1920,0,8960,0,29120,0,69888,0,128128,0,183040,0,205920,0,183040,0,128128,0,69888,0,29120,0,8960,0,1920,0,256,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst300Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2))) :=
  (hAst290Code.add hAst293Code)
private theorem hAst300DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst300Denominator=true := by kernel_decide
private theorem hAst300DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst300Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst300Denominator hAst300DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst300Cross : equalCheck
    (mul hAst300Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst300Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst300Numerator) hAst300Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst300Code : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2))) :=
  hAst300Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst300Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst300Denominator)
    hAst300DenNonzero hAst300Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst301Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-14,0,-91,0,-364,0,-987,0,-1932,0,-2919,0,-3701,0,-4319,0,-4907,0,-5341,0,-5341,0,-4907,0,-4319,0,-3701,0,-2919,0,-1932,0,-987,0,-364,0,-91,0,-14,0,-1],[0],[4,0,58,0,390,0,1612,0,4512,0,9032,0,13612,0,16478,0,17652,0,16754,0,17168,0,12758,0,12964,0,6366,0,9316,0,3338,0,5224,0,-212,0,858,0,-650,0,220,0,2],[0],[-1,0,-14,0,-91,0,-366,0,-993,0,-1848,0,-2252,0,-1336,0,994,0,3564,0,4686,0,3564,0,994,0,-1336,0,-2252,0,-1848,0,-993,0,-366,0,-91,0,-14,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst301Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,224,0,1456,0,5824,0,16016,0,32032,0,48048,0,54912,0,48048,0,32032,0,16016,0,5824,0,1456,0,224,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst301Raw : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  (hAst300Code.add hAst297Code)
private theorem hAst301DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst301Denominator=true := by kernel_decide
private theorem hAst301DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst301Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst301Denominator hAst301DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst301Cross : equalCheck
    (mul hAst301Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst301Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst301Numerator) hAst301Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst301Code : RationalCode Source.domain (fun z => ((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))) :=
  hAst301Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst301Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst301Denominator)
    hAst301DenNonzero hAst301Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst302Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-56,0,-70,0,-70,0,-95,0,-95,0,-70,0,-70,0,-56,0,-56,0,-28,0,-8,0,-1],[0],[4,0,34,0,126,0,266,0,286,0,272,0,272,0,270,0,360,0,190,0,294,0,226,0,278,0,144,0,44,0,6],[0],[-1,0,-8,0,-28,0,-58,0,-50,0,8,0,79,0,116,0,79,0,8,0,-50,0,-58,0,-28,0,-8,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst302Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst302Raw : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 7))^2))) :=
  (hAst301Code.add hAst299Code)
private theorem hAst302DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst302Denominator=true := by kernel_decide
private theorem hAst302DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst302Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst302Denominator hAst302DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst302Cross : equalCheck
    (mul hAst302Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst302Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst302Numerator) hAst302Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst302Code : RationalCode Source.domain (fun z => (((((((-1/4) : ℚ) : ℝ)*((((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2))+(((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2)))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2))+(((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*((Source.powerImag z.1 7))^2))) :=
  hAst302Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst302Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst302Denominator)
    hAst302DenNonzero hAst302Cross

/-- Article: proposed exact numerator for hRadius7. -/
def hRadius7Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-56,0,-70,0,-70,0,-95,0,-95,0,-70,0,-70,0,-56,0,-56,0,-28,0,-8,0,-1],[0],[4,0,34,0,126,0,266,0,286,0,272,0,272,0,270,0,360,0,190,0,294,0,226,0,278,0,144,0,44,0,6],[0],[-1,0,-8,0,-28,0,-58,0,-50,0,8,0,79,0,116,0,79,0,8,0,-50,0,-58,0,-28,0,-8,0,-1]]
/-- Article: proposed positive denominator for hRadius7. -/
def hRadius7Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hRadius7Raw : RationalCode Source.domain (fun z => (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 7))^2))) :=
  (hAst302Code.congr (by
    intro z hz
    ring))
private theorem hRadius7Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((((-1/4) : ℚ) : ℝ)*(((Source.gradientReal z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectReal z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierReal z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))^2)+((((-1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(((Source.gradientImag z.1 z.2 7)+((((-1) : ℚ) : ℝ)*(Source.defectImag z.1 z.2))+((((-1) : ℚ) : ℝ)*(Source.multiplierImag z.1 z.2))))^2)+((((1/4) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*((Source.powerImag z.1 7))^2))=Source.radius z.1 z.2 7 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.radius]; ring
private theorem hRadius7DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hRadius7Denominator=true := by kernel_decide
private theorem hRadius7DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hRadius7Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hRadius7Denominator hRadius7DenCheck hz.1 hz.2).ne'
private theorem hRadius7Cross : equalCheck
    (mul hRadius7Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hRadius7Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hRadius7Numerator) hRadius7Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hRadius7. -/
def hRadius7Code : RationalCode Source.domain (fun z => Source.radius z.1 z.2 7) :=
  (hRadius7Raw.congr hRadius7Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius7Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hRadius7Denominator)
    hRadius7DenNonzero hRadius7Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst303Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst303Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst303Raw : RationalCode Source.domain (fun z => (z.1)^14) :=
  ((RationalCode.first Source.domain).pow 14)
private theorem hAst303DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst303Denominator=true := by kernel_decide
private theorem hAst303DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst303Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst303Denominator hAst303DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst303Cross : equalCheck
    (mul hAst303Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst303Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst303Numerator) hAst303Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst303Code : RationalCode Source.domain (fun z => (z.1)^14) :=
  hAst303Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst303Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst303Denominator)
    hAst303DenNonzero hAst303Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst304Numerator : polyak.Numerics.IntegerBivariate.Source := [[-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst304Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst304Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^14)) :=
  ((RationalCode.constant Source.domain (-1)).add hAst303Code)
private theorem hAst304DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst304Denominator=true := by kernel_decide
private theorem hAst304DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst304Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst304Denominator hAst304DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst304Cross : equalCheck
    (mul hAst304Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst304Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst304Numerator) hAst304Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst304Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)+(z.1)^14)) :=
  hAst304Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst304Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst304Denominator)
    hAst304DenNonzero hAst304Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst305Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,1,0,2,0,1,0,0,0,0,0,0,0,0,0,-1,0,-2,0,-1],[0,2,-2,0,2,-2,0,0,0,0,0,0,0,0,0,-2,2,0,-2,2],[1,0,2,0,1,0,0,0,0,0,0,0,0,0,-1,0,-2,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst305Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,12,0,12,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst305Raw : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^14))) :=
  (hValueCode.mul hAst304Code)
private theorem hAst305DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst305Denominator=true := by kernel_decide
private theorem hAst305DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst305Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst305Denominator hAst305DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst305Cross : equalCheck
    (mul hAst305Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst305Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst305Numerator) hAst305Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst305Code : RationalCode Source.domain (fun z => ((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^14))) :=
  hAst305Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst305Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst305Denominator)
    hAst305DenNonzero hAst305Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst306Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-24,0,-4,0,-40,0,6,0,-40,0,-4,0,-24,0,1],[0],[2,0,15,0,49,0,90,0,115,0,109,0,89,0,75,0,55,0,32,0,10,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst306Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst306Raw : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7))) :=
  (hDRealCode.add hGradientReal7Code)
private theorem hAst306DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst306Denominator=true := by kernel_decide
private theorem hAst306DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst306Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst306Denominator hAst306DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst306Cross : equalCheck
    (mul hAst306Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst306Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst306Numerator) hAst306Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst306Code : RationalCode Source.domain (fun z => ((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7))) :=
  hAst306Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst306Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst306Denominator)
    hAst306DenNonzero hAst306Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst307Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-34,0,-59,0,-25,0,-47,0,5,0,-40,0,-4,0,-24,0,1],[0],[1,0,8,0,28,0,55,0,80,0,88,0,82,0,74,0,55,0,32,0,10,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst307Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst307Raw : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7))+(Source.multiplierReal z.1 z.2))) :=
  (hAst306Code.add hSRealCode)
private theorem hAst307DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst307Denominator=true := by kernel_decide
private theorem hAst307DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst307Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst307Denominator hAst307DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst307Cross : equalCheck
    (mul hAst307Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst307Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst307Numerator) hAst307Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst307Code : RationalCode Source.domain (fun z => (((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7))+(Source.multiplierReal z.1 z.2))) :=
  hAst307Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst307Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst307Denominator)
    hAst307DenNonzero hAst307Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst308Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,28,0,35,0,14,0,37,0,7,0,14,0,-7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst308Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst308Raw : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))) :=
  ((RationalCode.constant Source.domain (-1/2)).mul hAst291Code)
private theorem hAst308DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst308Denominator=true := by kernel_decide
private theorem hAst308DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst308Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst308Denominator hAst308DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst308Cross : equalCheck
    (mul hAst308Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst308Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst308Numerator) hAst308Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst308Code : RationalCode Source.domain (fun z => ((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))) :=
  hAst308Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst308Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst308Denominator)
    hAst308DenNonzero hAst308Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst309Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-14,0,-91,0,-363,0,-1011,0,-2118,0,-3498,0,-4736,0,-5269,0,-5905,0,-5230,0,-6172,0,-3907,0,-4763,0,-1418,0,-2796,0,-330,0,-1497,0,93,0,-301,0,182,0,-7],[0],[1,0,15,0,105,0,454,0,1361,0,3042,0,5381,0,7965,0,10235,0,11981,0,12811,0,12521,0,10991,0,8571,0,6119,0,3855,0,2136,0,832,0,96,0,-91,0,-84,0,7]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst309Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,60,0,420,0,1820,0,5460,0,12012,0,20020,0,25740,0,25740,0,20020,0,12012,0,5460,0,1820,0,420,0,60,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst309Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7))+(Source.multiplierReal z.1 z.2)))) :=
  (hAst308Code.mul hAst307Code)
private theorem hAst309DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst309Denominator=true := by kernel_decide
private theorem hAst309DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst309Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst309Denominator hAst309DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst309Cross : equalCheck
    (mul hAst309Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst309Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst309Numerator) hAst309Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst309Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7))+(Source.multiplierReal z.1 z.2)))) :=
  hAst309Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst309Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst309Denominator)
    hAst309DenNonzero hAst309Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst310Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,0,0,8,0,-32,0,-8,0,-64,0,-8,0,-32,0,8],[0],[1,0,7,0,21,0,35,0,29,0,17,0,13,0,9,0,6,0,-4,0,-6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst310Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0,0,2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst310Raw : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 7))) :=
  (hDImagCode.add hGradientImag7Code)
private theorem hAst310DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst310Denominator=true := by kernel_decide
private theorem hAst310DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst310Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst310Denominator hAst310DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst310Cross : equalCheck
    (mul hAst310Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst310Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst310Numerator) hAst310Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst310Code : RationalCode Source.domain (fun z => ((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 7))) :=
  hAst310Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst310Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst310Denominator)
    hAst310DenNonzero hAst310Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst311Numerator : polyak.Numerics.IntegerBivariate.Source := [[1,0,7,0,21,0,35,0,43,0,-11,0,-1,0,-63,0,-8,0,-32,0,8],[0],[0,0,0,0,0,0,-6,0,-4,0,6,0,8,0,6,0,-4,0,-6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst311Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[2,0,14,0,42,0,70,0,70,0,42,0,14,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst311Raw : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 7))+(Source.multiplierImag z.1 z.2))) :=
  (hAst310Code.add hSImagCode)
private theorem hAst311DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst311Denominator=true := by kernel_decide
private theorem hAst311DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst311Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst311Denominator hAst311DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst311Cross : equalCheck
    (mul hAst311Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst311Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst311Numerator) hAst311Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst311Code : RationalCode Source.domain (fun z => (((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 7))+(Source.multiplierImag z.1 z.2))) :=
  hAst311Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst311Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst311Denominator)
    hAst311DenNonzero hAst311Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst312Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-17,0,-18,0,-47,0,-30,0,-47,0,-18,0,-17,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst312Denominator : polyak.Numerics.IntegerBivariate.Source := [[2,0,16,0,56,0,112,0,140,0,112,0,56,0,16,0,2]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst312Raw : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))) :=
  (hAst040Code.mul hPowerImag7Code)
private theorem hAst312DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst312Denominator=true := by kernel_decide
private theorem hAst312DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst312Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst312Denominator hAst312DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst312Cross : equalCheck
    (mul hAst312Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst312Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst312Numerator) hAst312Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst312Code : RationalCode Source.domain (fun z => (((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))) :=
  hAst312Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst312Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst312Denominator)
    hAst312DenNonzero hAst312Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst313Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-10,0,-116,0,-495,0,-1289,0,-2616,0,-3210,0,-4049,0,-1833,0,-1386,0,2856,0,2255,0,4809,0,2100,0,2478,0,273,0,392,0,-168,0,8],[0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-6,0,98,0,182,0,260,0,130,0,-130,0,-306,0,-456,0,-306,0,-130,0,130,0,260,0,182,0,98,0,-6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst313Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,60,0,420,0,1820,0,5460,0,12012,0,20020,0,25740,0,25740,0,20020,0,12012,0,5460,0,1820,0,420,0,60,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst313Raw : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 7))+(Source.multiplierImag z.1 z.2)))) :=
  (hAst312Code.mul hAst311Code)
private theorem hAst313DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst313Denominator=true := by kernel_decide
private theorem hAst313DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst313Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst313Denominator hAst313DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst313Cross : equalCheck
    (mul hAst313Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst313Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst313Numerator) hAst313Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst313Code : RationalCode Source.domain (fun z => ((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 7))+(Source.multiplierImag z.1 z.2)))) :=
  hAst313Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst313Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst313Denominator)
    hAst313DenNonzero hAst313Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst314Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-10,0,-116,0,-495,0,-1305,0,-2280,0,-3994,0,-4593,0,-6809,0,-5818,0,-7752,0,-4849,0,-5799,0,-2332,0,-2498,0,-271,0,-392,0,168,0,-8],[0,2,-2,24,-22,130,-108,416,-308,858,-550,1144,-594,858,-264,-2,266,-882,616,-1274,658,-1274,616,-1274,658,-1274,616,-882,266,-2,-264,858,-594,1144,-550,858,-308,416,-108,130,-22,24,-2,2],[2,0,29,0,196,0,818,0,2362,0,5044,0,8384,0,11396,0,13224,0,13892,0,13448,0,11884,0,9080,0,5582,0,2688,0,852,0,134,0,-169,0,-268,0,-182,0,-98,0,6]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst314Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,60,0,420,0,1820,0,5460,0,12012,0,20020,0,25740,0,25740,0,20020,0,12012,0,5460,0,1820,0,420,0,60,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst314Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^14))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7))+(Source.multiplierReal z.1 z.2))))) :=
  (hAst305Code.add hAst309Code)
private theorem hAst314DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst314Denominator=true := by kernel_decide
private theorem hAst314DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst314Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst314Denominator hAst314DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst314Cross : equalCheck
    (mul hAst314Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst314Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst314Numerator) hAst314Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst314Code : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^14))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7))+(Source.multiplierReal z.1 z.2))))) :=
  hAst314Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst314Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst314Denominator)
    hAst314DenNonzero hAst314Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst315Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,2,0,-34,0,-36,0,-94,0,-60,0,-94,0,-36,0,-34,0,2],[0,2,-2,10,-8,18,-10,10,0,-10,10,-18,8,-10,2,-4,2,-10,8,-18,10,-10,0,10,-10,18,-8,10,-2,2],[2,0,15,0,49,0,90,0,108,0,116,0,110,0,118,0,98,0,53,0,17,0,-8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst315Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,32,0,112,0,224,0,280,0,224,0,112,0,32,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst315Raw : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^14))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 7))+(Source.multiplierImag z.1 z.2))))) :=
  (hAst314Code.add hAst313Code)
private theorem hAst315DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst315Denominator=true := by kernel_decide
private theorem hAst315DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst315Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst315Denominator hAst315DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst315Cross : equalCheck
    (mul hAst315Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst315Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst315Numerator) hAst315Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst315Code : RationalCode Source.domain (fun z => ((((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^14))+(((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7)))*(((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7))+(Source.multiplierReal z.1 z.2))))+((((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1))*(Source.powerImag z.1 7))*(((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 7))+(Source.multiplierImag z.1 z.2))))) :=
  hAst315Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst315Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst315Denominator)
    hAst315DenNonzero hAst315Cross

/-- Article: proposed exact numerator for hDiscrepancy7. -/
def hDiscrepancy7Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,2,0,-34,0,-36,0,-94,0,-60,0,-94,0,-36,0,-34,0,2],[0,2,-2,10,-8,18,-10,10,0,-10,10,-18,8,-10,2,-4,2,-10,8,-18,10,-10,0,10,-10,18,-8,10,-2,2],[2,0,15,0,49,0,90,0,108,0,116,0,110,0,118,0,98,0,53,0,17,0,-8]]
/-- Article: proposed positive denominator for hDiscrepancy7. -/
def hDiscrepancy7Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,32,0,112,0,224,0,280,0,224,0,112,0,32,0,4]]
/-- Article: composition of proved source-preserving rational operations. -/
def hDiscrepancy7Raw : RationalCode Source.domain (fun z => (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^14))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 7)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 7)+(Source.multiplierImag z.1 z.2))))) :=
  (hAst315Code.congr (by
    intro z hz
    ring))
private theorem hDiscrepancy7Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (((Source.valueConstant z.1 z.2)*((((-1) : ℚ) : ℝ)+(z.1)^14))+((((-1/2) : ℚ) : ℝ)*((((-1) : ℚ) : ℝ)+(Source.powerReal z.1 7))*((Source.defectReal z.1 z.2)+(Source.gradientReal z.1 z.2 7)+(Source.multiplierReal z.1 z.2)))+((((-1/2) : ℚ) : ℝ)*(Source.imaginarySquare z.1)*(Source.powerImag z.1 7)*((Source.defectImag z.1 z.2)+(Source.gradientImag z.1 z.2 7)+(Source.multiplierImag z.1 z.2))))=Source.discrepancy z.1 z.2 7 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.discrepancy]; ring
private theorem hDiscrepancy7DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hDiscrepancy7Denominator=true := by kernel_decide
private theorem hDiscrepancy7DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy7Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hDiscrepancy7Denominator hDiscrepancy7DenCheck hz.1 hz.2).ne'
private theorem hDiscrepancy7Cross : equalCheck
    (mul hDiscrepancy7Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy7Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy7Numerator) hDiscrepancy7Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hDiscrepancy7. -/
def hDiscrepancy7Code : RationalCode Source.domain (fun z => Source.discrepancy z.1 z.2 7) :=
  (hDiscrepancy7Raw.congr hDiscrepancy7Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy7Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hDiscrepancy7Denominator)
    hDiscrepancy7DenNonzero hDiscrepancy7Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst316Numerator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[0],[0],[0],[0],[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst316Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst316Raw : RationalCode Source.domain (fun z => (z.2)^8) :=
  ((RationalCode.second Source.domain).pow 8)
private theorem hAst316DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst316Denominator=true := by kernel_decide
private theorem hAst316DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst316Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst316Denominator hAst316DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst316Cross : equalCheck
    (mul hAst316Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst316Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst316Numerator) hAst316Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst316Code : RationalCode Source.domain (fun z => (z.2)^8) :=
  hAst316Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst316Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst316Denominator)
    hAst316DenNonzero hAst316Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst317Numerator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[0],[0],[0],[0],[0],[0],[-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst317Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst317Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(z.2)^8)) :=
  ((RationalCode.constant Source.domain (-1)).mul hAst316Code)
private theorem hAst317DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst317Denominator=true := by kernel_decide
private theorem hAst317DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst317Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst317Denominator hAst317DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst317Cross : equalCheck
    (mul hAst317Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst317Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst317Numerator) hAst317Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst317Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(z.2)^8)) :=
  hAst317Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst317Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst317Denominator)
    hAst317DenNonzero hAst317Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst318Numerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[0],[0],[0],[0],[0],[0],[-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst318Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst318Raw : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8))) :=
  ((RationalCode.constant Source.domain 1).add hAst317Code)
private theorem hAst318DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst318Denominator=true := by kernel_decide
private theorem hAst318DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst318Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst318Denominator hAst318DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst318Cross : equalCheck
    (mul hAst318Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst318Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst318Numerator) hAst318Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst318Code : RationalCode Source.domain (fun z => (((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8))) :=
  hAst318Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst318Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst318Denominator)
    hAst318DenNonzero hAst318Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst319Numerator : polyak.Numerics.IntegerBivariate.Source := [[1],[0],[0],[0],[0],[0],[0],[0],[-2],[0],[0],[0],[0],[0],[0],[0],[1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst319Denominator : polyak.Numerics.IntegerBivariate.Source := [[1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst319Raw : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2) :=
  (hAst318Code.pow 2)
private theorem hAst319DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst319Denominator=true := by kernel_decide
private theorem hAst319DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst319Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst319Denominator hAst319DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst319Cross : equalCheck
    (mul hAst319Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst319Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst319Numerator) hAst319Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst319Code : RationalCode Source.domain (fun z => ((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2) :=
  hAst319Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst319Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst319Denominator)
    hAst319DenNonzero hAst319Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst320Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,-2,0,34,0,36,0,94,0,60,0,94,0,36,0,34,0,-2],[0,-2,2,-10,8,-18,10,-10,0,10,-10,18,-8,10,-2,4,-2,10,-8,18,-10,10,0,-10,10,-18,8,-10,2,-2],[-2,0,-15,0,-49,0,-90,0,-108,0,-116,0,-110,0,-118,0,-98,0,-53,0,-17,0,8]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst320Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[4,0,32,0,112,0,224,0,280,0,224,0,112,0,32,0,4]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst320Raw : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 7))) :=
  ((RationalCode.constant Source.domain (-1)).mul hDiscrepancy7Code)
private theorem hAst320DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst320Denominator=true := by kernel_decide
private theorem hAst320DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst320Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst320Denominator hAst320DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst320Cross : equalCheck
    (mul hAst320Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst320Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst320Numerator) hAst320Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst320Code : RationalCode Source.domain (fun z => ((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 7))) :=
  hAst320Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst320Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst320Denominator)
    hAst320DenNonzero hAst320Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst321Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-56,0,-70,0,-70,0,-95,0,-95,0,-70,0,-70,0,-56,0,-56,0,-28,0,-8,0,-1],[0],[20,0,162,0,574,0,1162,0,1406,0,1168,0,720,0,398,0,376,0,190,0,294,0,226,0,278,0,144,0,44,0,6],[0],[-1,0,-8,0,-28,0,-58,0,-50,0,8,0,79,0,116,0,79,0,8,0,-50,0,-58,0,-28,0,-8,0,-1],[0],[0],[0],[0],[0],[-32,0,-256,0,-896,0,-1792,0,-2240,0,-1792,0,-896,0,-256,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst321Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst321Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 7)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)) :=
  (hRadius7Code.add hAst319Code)
private theorem hAst321DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst321Denominator=true := by kernel_decide
private theorem hAst321DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst321Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst321Denominator hAst321DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst321Cross : equalCheck
    (mul hAst321Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst321Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst321Numerator) hAst321Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst321Code : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 7)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)) :=
  hAst321Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst321Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst321Denominator)
    hAst321DenNonzero hAst321Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst322Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-56,0,-70,0,-70,0,-95,0,-95,0,-70,0,-70,0,-56,0,-56,0,-28,0,-8,0,-1],[0,0,0,0,0,0,0,0,-8,0,136,0,144,0,376,0,240,0,376,0,144,0,136,0,-8],[20,-8,170,-40,606,-72,1202,-40,1406,40,1128,72,688,40,390,16,368,40,158,72,254,40,226,-40,318,-72,176,-40,52,-8,6],[-8,0,-60,0,-196,0,-360,0,-432,0,-464,0,-440,0,-472,0,-392,0,-212,0,-68,0,32],[-1,0,-8,0,-28,0,-58,0,-50,0,8,0,79,0,116,0,79,0,8,0,-50,0,-58,0,-28,0,-8,0,-1],[0],[0],[0],[0],[0],[-32,0,-256,0,-896,0,-1792,0,-2240,0,-1792,0,-896,0,-256,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst322Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst322Raw : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 7)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 7)))) :=
  (hAst321Code.add hAst320Code)
private theorem hAst322DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst322Denominator=true := by kernel_decide
private theorem hAst322DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst322Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst322Denominator hAst322DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst322Cross : equalCheck
    (mul hAst322Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst322Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst322Numerator) hAst322Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst322Code : RationalCode Source.domain (fun z => (((Source.radius z.1 z.2 7)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 7)))) :=
  hAst322Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst322Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst322Denominator)
    hAst322DenNonzero hAst322Cross

/-- Article: proposed exact numerator for hPairLower7. -/
def hPairLower7Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-56,0,-70,0,-70,0,-95,0,-95,0,-70,0,-70,0,-56,0,-56,0,-28,0,-8,0,-1],[0,0,0,0,0,0,0,0,-8,0,136,0,144,0,376,0,240,0,376,0,144,0,136,0,-8],[20,-8,170,-40,606,-72,1202,-40,1406,40,1128,72,688,40,390,16,368,40,158,72,254,40,226,-40,318,-72,176,-40,52,-8,6],[-8,0,-60,0,-196,0,-360,0,-432,0,-464,0,-440,0,-472,0,-392,0,-212,0,-68,0,32],[-1,0,-8,0,-28,0,-58,0,-50,0,8,0,79,0,116,0,79,0,8,0,-50,0,-58,0,-28,0,-8,0,-1],[0],[0],[0],[0],[0],[-32,0,-256,0,-896,0,-1792,0,-2240,0,-1792,0,-896,0,-256,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: proposed positive denominator for hPairLower7. -/
def hPairLower7Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairLower7Raw : RationalCode Source.domain (fun z => ((Source.radius z.1 z.2 7)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 7)))) :=
  (hAst322Code.congr (by
    intro z hz
    ring))
private theorem hPairLower7Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.radius z.1 z.2 7)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2+((((-1) : ℚ) : ℝ)*(Source.discrepancy z.1 z.2 7)))=Source.pairSlack z.1 z.2 (-1) 7 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairLower7DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairLower7Denominator=true := by kernel_decide
private theorem hPairLower7DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairLower7Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairLower7Denominator hPairLower7DenCheck hz.1 hz.2).ne'
private theorem hPairLower7Cross : equalCheck
    (mul hPairLower7Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairLower7Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairLower7Numerator) hPairLower7Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairLower7. -/
def hPairLower7Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (-1) 7) :=
  (hPairLower7Raw.congr hPairLower7Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower7Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairLower7Denominator)
    hPairLower7DenNonzero hPairLower7Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst323Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-56,0,-70,0,-70,0,-95,0,-95,0,-70,0,-70,0,-56,0,-56,0,-28,0,-8,0,-1],[0,0,0,0,0,0,0,0,8,0,-136,0,-144,0,-376,0,-240,0,-376,0,-144,0,-136,0,8],[4,8,26,40,94,72,226,40,286,-40,312,-72,304,-40,278,-16,368,-40,222,-72,334,-40,226,40,238,72,112,40,36,8,6],[8,0,60,0,196,0,360,0,432,0,464,0,440,0,472,0,392,0,212,0,68,0,-32],[-1,0,-8,0,-28,0,-58,0,-50,0,8,0,79,0,116,0,79,0,8,0,-50,0,-58,0,-28,0,-8,0,-1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst323Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst323Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 7)+(Source.radius z.1 z.2 7))) :=
  (hDiscrepancy7Code.add hRadius7Code)
private theorem hAst323DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst323Denominator=true := by kernel_decide
private theorem hAst323DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst323Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst323Denominator hAst323DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst323Cross : equalCheck
    (mul hAst323Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst323Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst323Numerator) hAst323Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst323Code : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 7)+(Source.radius z.1 z.2 7))) :=
  hAst323Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst323Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst323Denominator)
    hAst323DenNonzero hAst323Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst324Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-56,0,-70,0,-70,0,-95,0,-95,0,-70,0,-70,0,-56,0,-56,0,-28,0,-8,0,-1],[0,0,0,0,0,0,0,0,8,0,-136,0,-144,0,-376,0,-240,0,-376,0,-144,0,-136,0,8],[20,8,154,40,542,72,1122,40,1406,-40,1208,-72,752,-40,406,-16,384,-40,222,-72,334,-40,226,40,238,72,112,40,36,8,6],[8,0,60,0,196,0,360,0,432,0,464,0,440,0,472,0,392,0,212,0,68,0,-32],[-1,0,-8,0,-28,0,-58,0,-50,0,8,0,79,0,116,0,79,0,8,0,-50,0,-58,0,-28,0,-8,0,-1],[0],[0],[0],[0],[0],[-32,0,-256,0,-896,0,-1792,0,-2240,0,-1792,0,-896,0,-256,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst324Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst324Raw : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 7)+(Source.radius z.1 z.2 7))+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)) :=
  (hAst323Code.add hAst319Code)
private theorem hAst324DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst324Denominator=true := by kernel_decide
private theorem hAst324DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst324Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst324Denominator hAst324DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst324Cross : equalCheck
    (mul hAst324Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst324Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst324Numerator) hAst324Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst324Code : RationalCode Source.domain (fun z => (((Source.discrepancy z.1 z.2 7)+(Source.radius z.1 z.2 7))+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)) :=
  hAst324Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst324Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst324Denominator)
    hAst324DenNonzero hAst324Cross

/-- Article: proposed exact numerator for hPairUpper7. -/
def hPairUpper7Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-56,0,-70,0,-70,0,-95,0,-95,0,-70,0,-70,0,-56,0,-56,0,-28,0,-8,0,-1],[0,0,0,0,0,0,0,0,8,0,-136,0,-144,0,-376,0,-240,0,-376,0,-144,0,-136,0,8],[20,8,154,40,542,72,1122,40,1406,-40,1208,-72,752,-40,406,-16,384,-40,222,-72,334,-40,226,40,238,72,112,40,36,8,6],[8,0,60,0,196,0,360,0,432,0,464,0,440,0,472,0,392,0,212,0,68,0,-32],[-1,0,-8,0,-28,0,-58,0,-50,0,8,0,79,0,116,0,79,0,8,0,-50,0,-58,0,-28,0,-8,0,-1],[0],[0],[0],[0],[0],[-32,0,-256,0,-896,0,-1792,0,-2240,0,-1792,0,-896,0,-256,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: proposed positive denominator for hPairUpper7. -/
def hPairUpper7Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPairUpper7Raw : RationalCode Source.domain (fun z => ((Source.discrepancy z.1 z.2 7)+(Source.radius z.1 z.2 7)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)) :=
  (hAst324Code.congr (by
    intro z hz
    ring))
private theorem hPairUpper7Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((Source.discrepancy z.1 z.2 7)+(Source.radius z.1 z.2 7)+((((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(z.2)^8)))^2)=Source.pairSlack z.1 z.2 (1) 7 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.pairSlack]; ring
private theorem hPairUpper7DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPairUpper7Denominator=true := by kernel_decide
private theorem hPairUpper7DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper7Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPairUpper7Denominator hPairUpper7DenCheck hz.1 hz.2).ne'
private theorem hPairUpper7Cross : equalCheck
    (mul hPairUpper7Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper7Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper7Numerator) hPairUpper7Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPairUpper7. -/
def hPairUpper7Code : RationalCode Source.domain (fun z => Source.pairSlack z.1 z.2 (1) 7) :=
  (hPairUpper7Raw.congr hPairUpper7Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper7Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPairUpper7Denominator)
    hPairUpper7DenNonzero hPairUpper7Cross

/-- Article: canonical numerator for one arithmetic source node. -/
def hAst325Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-24,0,-4,0,-40,0,6,0,-40,0,-4,0,-24,0,1]]
/-- Article: canonical positive denominator for the same real source node. -/
def hAst325Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def hAst325Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 8 (radialCosine z.1))*(z.1)^8)) :=
  (hT8Code.mul hAst169Code)
private theorem hAst325DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hAst325Denominator=true := by kernel_decide
private theorem hAst325DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hAst325Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hAst325Denominator hAst325DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem hAst325Cross : equalCheck
    (mul hAst325Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hAst325Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hAst325Numerator) hAst325Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def hAst325Code : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 8 (radialCosine z.1))*(z.1)^8)) :=
  hAst325Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode hAst325Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hAst325Denominator)
    hAst325DenNonzero hAst325Cross

/-- Article: proposed exact numerator for hPowerReal8. -/
def hPowerReal8Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,0,0,0,0,1,0,-24,0,-4,0,-40,0,6,0,-40,0,-4,0,-24,0,1]]
/-- Article: proposed positive denominator for hPowerReal8. -/
def hPowerReal8Denominator : polyak.Numerics.IntegerBivariate.Source := [[1,0,8,0,28,0,56,0,70,0,56,0,28,0,8,0,1]]
/-- Article: composition of proved source-preserving rational operations. -/
def hPowerReal8Raw : RationalCode Source.domain (fun z => ((polyak.Spectral.chebT 8 (radialCosine z.1))*(z.1)^8)) :=
  (hAst325Code.congr (by
    intro z hz
    ring))
private theorem hPowerReal8Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    ((polyak.Spectral.chebT 8 (radialCosine z.1))*(z.1)^8)=Source.powerReal z.1 8 := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    dsimp only [Source.powerReal]; ring
private theorem hPowerReal8DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients hPowerReal8Denominator=true := by kernel_decide
private theorem hPowerReal8DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal8Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    hPowerReal8Denominator hPowerReal8DenCheck hz.1 hz.2).ne'
private theorem hPowerReal8Cross : equalCheck
    (mul hPowerReal8Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal8Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal8Numerator) hPowerReal8Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for hPowerReal8. -/
def hPowerReal8Code : RationalCode Source.domain (fun z => Source.powerReal z.1 8) :=
  (hPowerReal8Raw.congr hPowerReal8Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal8Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode hPowerReal8Denominator)
    hPowerReal8DenNonzero hPowerReal8Cross

end
end polyak.Certificates.Startup.Codes
