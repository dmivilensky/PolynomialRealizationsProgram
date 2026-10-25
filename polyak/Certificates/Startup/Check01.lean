import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign I.lower.norm on [33/100,1].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check01
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-64,768,-740,3968,-2436,8704,-3804,9408,-2648,5312,-956,1472,-100,64,-4],[0,0,0,-128,-80,-384,-944,-512,-2544,-640,-3008,-768,-1872,-512,-656,-128,-112],[0,0,20,-128,256,-672,796,-1504,1096,-1856,748,-1344,208,-544,-28,-96,-24],[0,0,0,0,56,0,256,0,472,0,448,0,232,0,64,0,8],[-3,0,-32,0,-1016,0,-5984,-1024,-14310,-4096,-17792,-6144,-12704,-4096,-5248,-1024,-1023],[0,0,0,0,512,0,2816,0,6400,0,7680,0,5120,0,1792,0,256],[0,0,-64,0,-320,0,-576,0,-320,0,320,0,576,0,320,0,64],[0],[0,0,0,0,1472,0,9024,512,22400,2048,29312,3072,21696,2048,8768,512,1536],[0,0,0,0,-256,0,-1408,0,-3200,0,-3840,0,-2560,0,-896,0,-128],[0,0,32,0,160,0,288,0,160,0,-160,0,-288,0,-160,0,-32],[0],[0,0,0,0,-1024,0,-6144,0,-15360,0,-20480,0,-15360,0,-6144,0,-1024],[0],[0],[0],[0,0,0,0,256,0,1536,0,3840,0,5120,0,3840,0,1536,0,256]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨(33/100),1,by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.split (.split (.split (.leaf ⟨(184123041/1073741824),(198209709/1073741824),by norm_num⟩) (.leaf ⟨(99104853/536870912),(106261267/536870912),by norm_num⟩)) (.leaf ⟨(212522531/1073741824),(241757185/1073741824),by norm_num⟩)) (.split (.leaf ⟨(120878591/536870912),(271680629/1073741824),by norm_num⟩) (.leaf ⟨(135840313/536870912),(302139173/1073741824),by norm_num⟩))) (.split (.split (.leaf ⟨(151069585/536870912),(83244513/268435456),by norm_num⟩) (.leaf ⟨(332978049/1073741824),(91011757/268435456),by norm_num⟩)) (.split (.leaf ⟨(364047025/1073741824),(49400629/134217728),by norm_num⟩) (.leaf ⟨(395205029/1073741824),(213161835/536870912),by norm_num⟩)))) (.split (.split (.split (.leaf ⟨(426323667/1073741824),(457289565/1073741824),by norm_num⟩) (.leaf ⟨(228644781/536870912),(488005607/1073741824),by norm_num⟩)) (.split (.split (.leaf ⟨(122001401/268435456),(251622063/536870912),by norm_num⟩) (.leaf ⟨(503244123/1073741824),(129597815/268435456),by norm_num⟩)) (.split (.leaf ⟨(518391257/1073741824),(133359865/268435456),by norm_num⟩) (.leaf ⟨(533439457/1073741824),(548382123/1073741824),by norm_num⟩)))) (.split (.split (.split (.leaf ⟨(68547765/134217728),(563213555/1073741824),by norm_num⟩) (.leaf ⟨(35200847/67108864),(577928923/1073741824),by norm_num⟩)) (.split (.leaf ⟨(72241115/134217728),(592524205/1073741824),by norm_num⟩) (.leaf ⟨(296262101/536870912),(606996143/1073741824),by norm_num⟩))) (.split (.split (.leaf ⟨(151749035/268435456),(77667773/134217728),by norm_num⟩) (.split (.leaf ⟨(621342181/1073741824),(314233689/536870912),by norm_num⟩) (.leaf ⟨(628467375/1073741824),(317780217/536870912),by norm_num⟩))) (.split (.split (.leaf ⟨(635560431/1073741824),(160655303/268435456),by norm_num⟩) (.leaf ⟨(642621209/1073741824),(649649601/1073741824),by norm_num⟩)) (.split (.leaf ⟨(324824799/536870912),(328322763/536870912),by norm_num⟩) (.leaf ⟨(656645523/1073741824),(41475559/67108864),by norm_num⟩))))))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check01
