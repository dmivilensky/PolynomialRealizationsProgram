import polyak.Certificates.Startup.Code15

/-! Article: exact source identities for initialized special-spiral data. -/
namespace polyak.Certificates.Startup.Codes
noncomputable section
open polyak.Numerics.BivariateBranch
open polyak.Realization.ExplicitSpiral
/-- Article: proposed exact numerator for check35. -/
def check35Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0,0,0,0,0,0,-8,0,56,0,72,0,144,0,72,0,56,0,-8],[20,8,114,24,294,16,464,-16,422,-24,246,-16,194,-24,170,-16,166,16,56,24,24,8,6],[8,0,44,0,104,0,132,0,64,0,4,0,-8,0,12,0,24],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1],[0],[0],[0],[32,0,192,0,480,0,640,0,480,0,192,0,32],[0],[0],[0],[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: proposed positive denominator for check35. -/
def check35Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check35Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 5)) :=
  (hPairUpper5Code.congr (by
    intro z hz
    ring))
private theorem check35Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (1) 5)=(Source.pairSlack z.1 z.2 (1) 5) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check35DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check35Denominator=true := by kernel_decide
private theorem check35DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check35Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check35Denominator check35DenCheck hz.1 hz.2).ne'
private theorem check35Cross : equalCheck
    (mul check35Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check35Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check35Numerator) check35Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check35. -/
def check35Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 5)) :=
  (check35Raw.congr check35Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check35Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check35Denominator)
    check35DenNonzero check35Cross

/-- Article: proposed exact numerator for check36. -/
def check36Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-37,0,-13,0,21,0,58,0,58,0,21,0,-13,0,-37,0,-21,0,-7,0,-1],[0,0,0,0,0,0,0,0,-48,0,16,0,-16,0,96,0,-16,0,16,0,-48],[20,-8,150,-32,456,-40,756,0,648,40,208,32,-170,16,-326,32,-122,40,36,0,210,-40,130,-32,46,-8,6],[-8,0,-52,0,-144,0,-204,0,-116,0,20,0,148,0,172,0,124,0,64,0,-4],[-1,0,-7,0,-21,0,-45,0,-55,0,-44,0,-38,0,-44,0,-55,0,-45,0,-21,0,-7,0,-1],[0],[0],[0],[32,0,224,0,672,0,1120,0,1120,0,672,0,224,0,32],[0],[0],[0],[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: proposed positive denominator for check36. -/
def check36Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check36Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 6)) :=
  (hPairLower6Code.congr (by
    intro z hz
    ring))
private theorem check36Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (-1) 6)=(Source.pairSlack z.1 z.2 (-1) 6) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check36DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check36Denominator=true := by kernel_decide
private theorem check36DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check36Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check36Denominator check36DenCheck hz.1 hz.2).ne'
private theorem check36Cross : equalCheck
    (mul check36Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check36Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check36Numerator) check36Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check36. -/
def check36Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 6)) :=
  (check36Raw.congr check36Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check36Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check36Denominator)
    check36DenNonzero check36Cross

/-- Article: proposed exact numerator for check37. -/
def check37Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-7,0,-21,0,-37,0,-13,0,21,0,58,0,58,0,21,0,-13,0,-37,0,-21,0,-7,0,-1],[0,0,0,0,0,0,0,0,48,0,-16,0,16,0,-96,0,16,0,-16,0,48],[20,8,134,32,408,40,724,0,680,-40,256,-32,-154,-16,-310,-32,-74,-40,68,0,178,40,82,32,30,8,6],[8,0,52,0,144,0,204,0,116,0,-20,0,-148,0,-172,0,-124,0,-64,0,4],[-1,0,-7,0,-21,0,-45,0,-55,0,-44,0,-38,0,-44,0,-55,0,-45,0,-21,0,-7,0,-1],[0],[0],[0],[32,0,224,0,672,0,1120,0,1120,0,672,0,224,0,32],[0],[0],[0],[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: proposed positive denominator for check37. -/
def check37Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,112,0,336,0,560,0,560,0,336,0,112,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check37Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 6)) :=
  (hPairUpper6Code.congr (by
    intro z hz
    ring))
private theorem check37Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (1) 6)=(Source.pairSlack z.1 z.2 (1) 6) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check37DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check37Denominator=true := by kernel_decide
private theorem check37DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check37Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check37Denominator check37DenCheck hz.1 hz.2).ne'
private theorem check37Cross : equalCheck
    (mul check37Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check37Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check37Numerator) check37Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check37. -/
def check37Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 6)) :=
  (check37Raw.congr check37Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check37Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check37Denominator)
    check37DenNonzero check37Cross

/-- Article: proposed exact numerator for check38. -/
def check38Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-56,0,-70,0,-70,0,-95,0,-95,0,-70,0,-70,0,-56,0,-56,0,-28,0,-8,0,-1],[0,0,0,0,0,0,0,0,-8,0,136,0,144,0,376,0,240,0,376,0,144,0,136,0,-8],[20,-8,170,-40,606,-72,1202,-40,1406,40,1128,72,688,40,390,16,368,40,158,72,254,40,226,-40,318,-72,176,-40,52,-8,6],[-8,0,-60,0,-196,0,-360,0,-432,0,-464,0,-440,0,-472,0,-392,0,-212,0,-68,0,32],[-1,0,-8,0,-28,0,-58,0,-50,0,8,0,79,0,116,0,79,0,8,0,-50,0,-58,0,-28,0,-8,0,-1],[0],[0],[0],[0],[0],[-32,0,-256,0,-896,0,-1792,0,-2240,0,-1792,0,-896,0,-256,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: proposed positive denominator for check38. -/
def check38Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check38Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 7)) :=
  (hPairLower7Code.congr (by
    intro z hz
    ring))
private theorem check38Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (-1) 7)=(Source.pairSlack z.1 z.2 (-1) 7) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check38DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check38Denominator=true := by kernel_decide
private theorem check38DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check38Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check38Denominator check38DenCheck hz.1 hz.2).ne'
private theorem check38Cross : equalCheck
    (mul check38Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check38Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check38Numerator) check38Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check38. -/
def check38Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 7)) :=
  (check38Raw.congr check38Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check38Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check38Denominator)
    check38DenNonzero check38Cross

/-- Article: proposed exact numerator for check39. -/
def check39Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-8,0,-28,0,-56,0,-56,0,-70,0,-70,0,-95,0,-95,0,-70,0,-70,0,-56,0,-56,0,-28,0,-8,0,-1],[0,0,0,0,0,0,0,0,8,0,-136,0,-144,0,-376,0,-240,0,-376,0,-144,0,-136,0,8],[20,8,154,40,542,72,1122,40,1406,-40,1208,-72,752,-40,406,-16,384,-40,222,-72,334,-40,226,40,238,72,112,40,36,8,6],[8,0,60,0,196,0,360,0,432,0,464,0,440,0,472,0,392,0,212,0,68,0,-32],[-1,0,-8,0,-28,0,-58,0,-50,0,8,0,79,0,116,0,79,0,8,0,-50,0,-58,0,-28,0,-8,0,-1],[0],[0],[0],[0],[0],[-32,0,-256,0,-896,0,-1792,0,-2240,0,-1792,0,-896,0,-256,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: proposed positive denominator for check39. -/
def check39Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,128,0,448,0,896,0,1120,0,896,0,448,0,128,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check39Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 7)) :=
  (hPairUpper7Code.congr (by
    intro z hz
    ring))
private theorem check39Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (1) 7)=(Source.pairSlack z.1 z.2 (1) 7) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check39DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check39Denominator=true := by kernel_decide
private theorem check39DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check39Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check39Denominator check39DenCheck hz.1 hz.2).ne'
private theorem check39Cross : equalCheck
    (mul check39Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check39Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check39Numerator) check39Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check39. -/
def check39Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 7)) :=
  (check39Raw.congr check39Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check39Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check39Denominator)
    check39DenNonzero check39Cross

/-- Article: proposed exact numerator for check40. -/
def check40Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0,0,0,0,0,0,0,0,0,0,64,0,-192,0,-256,0,-832,0,-640,0,-832,0,-256,0,-192,0,64],[20,-8,190,-48,776,-112,1808,-112,2662,0,2804,112,2124,112,1332,48,994,16,724,48,960,112,728,112,874,0,628,-112,492,-112,228,-48,58,-8,6],[-8,0,-68,0,-256,0,-560,0,-808,0,-820,0,-448,0,-96,0,168,0,116,0,-64,0,-112,0,-120,0,4],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1],[0],[0],[0],[0],[0],[-32,0,-288,0,-1152,0,-2688,0,-4032,0,-4032,0,-2688,0,-1152,0,-288,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: proposed positive denominator for check40. -/
def check40Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check40Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 8)) :=
  (hPairLower8Code.congr (by
    intro z hz
    ring))
private theorem check40Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (-1) 8)=(Source.pairSlack z.1 z.2 (-1) 8) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check40DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check40Denominator=true := by kernel_decide
private theorem check40DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check40Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check40Denominator check40DenCheck hz.1 hz.2).ne'
private theorem check40Cross : equalCheck
    (mul check40Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check40Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check40Numerator) check40Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check40. -/
def check40Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 8)) :=
  (check40Raw.congr check40Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check40Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check40Denominator)
    check40DenNonzero check40Cross

/-- Article: proposed exact numerator for check41. -/
def check41Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0,0,0,0,0,0,0,0,0,0,-64,0,192,0,256,0,832,0,640,0,832,0,256,0,192,0,-64],[20,8,174,48,696,112,1664,112,2582,0,2884,-112,2268,-112,1412,-48,1010,-16,740,-48,1040,-112,872,-112,954,0,548,112,348,112,148,48,42,8,6],[8,0,68,0,256,0,560,0,808,0,820,0,448,0,96,0,-168,0,-116,0,64,0,112,0,120,0,-4],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1],[0],[0],[0],[0],[0],[-32,0,-288,0,-1152,0,-2688,0,-4032,0,-4032,0,-2688,0,-1152,0,-288,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: proposed positive denominator for check41. -/
def check41Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check41Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 8)) :=
  (hPairUpper8Code.congr (by
    intro z hz
    ring))
private theorem check41Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (1) 8)=(Source.pairSlack z.1 z.2 (1) 8) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check41DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check41Denominator=true := by kernel_decide
private theorem check41DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check41Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check41Denominator check41DenCheck hz.1 hz.2).ne'
private theorem check41Cross : equalCheck
    (mul check41Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check41Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check41Numerator) check41Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check41. -/
def check41Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 8)) :=
  (check41Raw.congr check41Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check41Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check41Denominator)
    check41DenNonzero check41Cross

/-- Article: proposed exact numerator for check42. -/
def check42Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-120,0,-210,0,-270,0,-132,0,48,0,315,0,425,0,425,0,315,0,48,0,-132,0,-270,0,-210,0,-120,0,-45,0,-10,0,-1],[0,0,0,0,0,0,0,0,0,0,8,0,-248,0,-24,0,-288,0,528,0,48,0,528,0,-288,0,-24,0,-248,0,8],[20,-8,210,-56,966,-160,2584,-224,4480,-112,5376,112,4122,224,1638,160,-700,56,-2248,16,-2134,56,-1854,160,-232,224,536,112,1398,-112,1146,-224,720,-160,286,-56,64,-8,6],[-8,0,-76,0,-324,0,-816,0,-1348,0,-1460,0,-816,0,0,0,816,0,1100,0,1180,0,1008,0,540,0,244,0,-40],[-1,0,-10,0,-45,0,-120,0,-208,0,-296,0,-312,0,-264,0,-202,0,-156,0,-202,0,-264,0,-312,0,-296,0,-208,0,-120,0,-45,0,-10,0,-1],[0],[0],[0],[0],[0],[0],[0],[32,0,320,0,1440,0,3840,0,6720,0,8064,0,6720,0,3840,0,1440,0,320,0,32],[0],[0],[0],[0],[0],[0],[0],[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: proposed positive denominator for check42. -/
def check42Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check42Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 9)) :=
  (hPairLower9Code.congr (by
    intro z hz
    ring))
private theorem check42Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (-1) 9)=(Source.pairSlack z.1 z.2 (-1) 9) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check42DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check42Denominator=true := by kernel_decide
private theorem check42DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check42Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check42Denominator check42DenCheck hz.1 hz.2).ne'
private theorem check42Cross : equalCheck
    (mul check42Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check42Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check42Numerator) check42Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check42. -/
def check42Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (-1) 9)) :=
  (check42Raw.congr check42Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check42Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check42Denominator)
    check42DenNonzero check42Cross

/-- Article: proposed exact numerator for check43. -/
def check43Numerator : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-10,0,-45,0,-120,0,-210,0,-270,0,-132,0,48,0,315,0,425,0,425,0,315,0,48,0,-132,0,-270,0,-210,0,-120,0,-45,0,-10,0,-1],[0,0,0,0,0,0,0,0,0,0,-8,0,248,0,24,0,288,0,-528,0,-48,0,-528,0,288,0,24,0,248,0,-8],[20,8,194,56,870,160,2360,224,4256,112,5376,-112,4346,-224,1862,-160,-604,-56,-2232,-16,-2118,-56,-1758,-160,-8,-224,760,-112,1398,112,922,224,496,160,190,56,48,8,6],[8,0,76,0,324,0,816,0,1348,0,1460,0,816,0,0,0,-816,0,-1100,0,-1180,0,-1008,0,-540,0,-244,0,40],[-1,0,-10,0,-45,0,-120,0,-208,0,-296,0,-312,0,-264,0,-202,0,-156,0,-202,0,-264,0,-312,0,-296,0,-208,0,-120,0,-45,0,-10,0,-1],[0],[0],[0],[0],[0],[0],[0],[32,0,320,0,1440,0,3840,0,6720,0,8064,0,6720,0,3840,0,1440,0,320,0,32],[0],[0],[0],[0],[0],[0],[0],[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: proposed positive denominator for check43. -/
def check43Denominator : polyak.Numerics.IntegerBivariate.Source := [[0],[0],[16,0,160,0,720,0,1920,0,3360,0,4032,0,3360,0,1920,0,720,0,160,0,16]]
/-- Article: composition of proved source-preserving rational operations. -/
def check43Raw : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 9)) :=
  (hPairUpper9Code.congr (by
    intro z hz
    ring))
private theorem check43Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    (Source.pairSlack z.1 z.2 (1) 9)=(Source.pairSlack z.1 z.2 (1) 9) := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    rfl
private theorem check43DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients check43Denominator=true := by kernel_decide
private theorem check43DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode check43Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    check43Denominator check43DenCheck hz.1 hz.2).ne'
private theorem check43Cross : equalCheck
    (mul check43Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode check43Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode check43Numerator) check43Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for check43. -/
def check43Code : RationalCode Source.domain (fun z => (Source.pairSlack z.1 z.2 (1) 9)) :=
  (check43Raw.congr check43Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode check43Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode check43Denominator)
    check43DenNonzero check43Cross

end
end polyak.Certificates.Startup.Codes
