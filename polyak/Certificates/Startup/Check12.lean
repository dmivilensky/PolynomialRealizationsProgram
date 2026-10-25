import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign III.lower.norm on [6/5,1713/1000].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check12
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,196,0,952,448,1156,1088,704,0,640,512,-640,-512,896,512,-1152,-512,1408,512,-1664,-512,1660,1728,-4188,2560,0,1984,-3648,1344,1444,-448,-1540,512,1280,-512,-1024,512,768,-512,-512,512,256,-512,256],[0,0,0,0,-224,0,-880,-256,-928,-384,-528,-128,-128,0,0,0,0,0,0,0,0,0,0,-128,144,-384,352,-256,160,0,96,0,16],[0,0,28,0,160,32,232,32,144,-32,28,-32,-16,0,0,0,0,0,0,0,0,0,-8,-96,24,-416,112,-608,80,-352,-8,-64,-8],[0,0,-16,0,-40,0,-16,0,32,0,32,0,8,0,0,0,0,0,0,0,0,0,16,0,96,0,160,0,96,0,16],[1,0,2,0,-897,0,-3972,-1024,-5249,-2048,-3198,-1024,-1023,0,0,0,0,0,0,0,-4,0,-28,0,-64,-1024,960,-2048,996,-1024,-4],[0,0,0,0,512,0,1792,0,2304,0,1280,0,256],[0,0,-64,0,-192,0,-128,0,128,0,192,0,64],[0],[0,0,0,0,1472,0,6080,512,8768,1024,5696,512,1536,0,0,0,0,0,0,0,0,0,0,0,0,512,-512,1024,-512,512],[0,0,0,0,-256,0,-896,0,-1152,0,-640,0,-128],[0,0,32,0,96,0,64,0,-64,0,-96,0,-32],[0],[0,0,0,0,-1024,0,-4096,0,-6144,0,-4096,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1024,0,1536,0,1024,0,256]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨(6/5),(1713/1000),by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.split (.split (.split (.leaf ⟨(197630851/268435456),(800215675/1073741824),by norm_num⟩) (.leaf ⟨(100026959/134217728),(809841385/1073741824),by norm_num⟩)) (.leaf ⟨(404920691/536870912),(828897881/1073741824),by norm_num⟩)) (.split (.leaf ⟨(414448939/536870912),(847702629/1073741824),by norm_num⟩) (.leaf ⟨(423851313/536870912),(866265639/1073741824),by norm_num⟩))) (.split (.leaf ⟨(216566409/268435456),(902707089/1073741824),by norm_num⟩) (.leaf ⟨(451353543/536870912),(469151635/536870912),by norm_num⟩))) (.split (.leaf ⟨(938303267/1073741824),(1007271611/1073741824),by norm_num⟩) (.leaf ⟨(125908951/134217728),(1073749541/1073741824),by norm_num⟩))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check12
