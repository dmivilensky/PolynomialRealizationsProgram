import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign I.upper.norm on [33/100,1].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check14
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-64,832,-548,3328,-1476,6144,-1948,5312,-664,1792,68,64,28,-64,-4],[0,0,0,-128,336,-640,1712,-1664,3952,-2688,4928,-2560,3280,-1280,1040,-256,112],[0,0,20,32,96,32,252,-128,264,-192,-84,32,-336,160,-188,64,-24],[0,0,0,0,-56,0,-256,0,-472,0,-448,0,-232,0,-64,0,-8],[-3,0,-32,0,-1016,-1024,-4960,-4096,-12262,-6144,-17792,-4096,-14752,-1024,-6272,0,-1023],[0,0,0,0,-512,0,-2816,0,-6400,0,-7680,0,-5120,0,-1792,0,-256],[0,0,-64,0,-320,0,-576,0,-320,0,320,0,576,0,320,0,64],[0],[0,0,0,0,1472,512,8512,2048,21376,3072,29312,2048,22720,512,9280,0,1536],[0,0,0,0,256,0,1408,0,3200,0,3840,0,2560,0,896,0,128],[0,0,32,0,160,0,288,0,160,0,-160,0,-288,0,-160,0,-32],[0],[0,0,0,0,-1024,0,-6144,0,-15360,0,-20480,0,-15360,0,-6144,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨(33/100),1,by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.split (.leaf ⟨(184123041/1073741824),(241757185/1073741824),by norm_num⟩) (.leaf ⟨(120878591/536870912),(302139173/1073741824),by norm_num⟩)) (.split (.leaf ⟨(151069585/536870912),(91011757/268435456),by norm_num⟩) (.leaf ⟨(364047025/1073741824),(213161835/536870912),by norm_num⟩))) (.split (.split (.leaf ⟨(426323667/1073741824),(488005607/1073741824),by norm_num⟩) (.leaf ⟨(122001401/268435456),(548382123/1073741824),by norm_num⟩)) (.split (.split (.leaf ⟨(68547765/134217728),(577928923/1073741824),by norm_num⟩) (.leaf ⟨(72241115/134217728),(606996143/1073741824),by norm_num⟩)) (.split (.leaf ⟨(151749035/268435456),(317780217/536870912),by norm_num⟩) (.split (.leaf ⟨(635560431/1073741824),(649649601/1073741824),by norm_num⟩) (.leaf ⟨(324824799/536870912),(41475559/67108864),by norm_num⟩)))))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check14
