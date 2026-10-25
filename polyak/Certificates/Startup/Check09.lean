import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign II.lower.2.discriminant on [1,6/5].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check09
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,-9,354,425,8020,-1491,49932,-23711,122420,-56110,153184,-70163,109724,-59680,43220,-34641,3612,-10701,-3490,-1510,-576,-9],[0,0,0,-480,-1360,-9100,4060,-39040,25360,-78960,52620,-90720,60640,-62280,43700,-24000,20400,-3440,5220,640,560,180],[0,60,170,1100,-2220,4110,-8610,5720,-14100,1280,-13990,-4960,-9580,-5500,-5670,-2040,-2860,20,-700,180,-40,30],[0,0,400,0,1100,0,1000,0,100,0,-800,0,-1100,0,-600,0,-100],[-25,0,-50,-960,-1895,-19520,1380,-96000,37145,-218880,101070,-269440,127975,-178560,90880,-49920,39680,6400,11520,6720,1920,960],[0],[0],[0],[0,0,0,480,960,9760,-640,48000,-18560,109440,-50560,134720,-64000,89280,-45440,24960,-19840,-3200,-5760,-3360,-960,-480]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨1,(6/5),by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.split (.leaf ⟨(663608941/1073741824),(680106463/1073741824),by norm_num⟩) (.leaf ⟨(170026615/268435456),(348209503/536870912),by norm_num⟩)) (.split (.leaf ⟨(696419003/1073741824),(89068477/134217728),by norm_num⟩) (.leaf ⟨(712547813/1073741824),(728494839/1073741824),by norm_num⟩))) (.split (.split (.split (.leaf ⟨(182123709/268435456),(736400957/1073741824),by norm_num⟩) (.leaf ⟨(368200477/536870912),(744262629/1073741824),by norm_num⟩)) (.split (.leaf ⟨(372131313/536870912),(376040127/536870912),by norm_num⟩) (.leaf ⟨(752080251/1073741824),(379927129/536870912),by norm_num⟩))) (.split (.split (.leaf ⟨(759854255/1073741824),(191896273/268435456),by norm_num⟩) (.split (.leaf ⟨(767585089/1073741824),(771434467/1073741824),by norm_num⟩) (.leaf ⟨(24107327/33554432),(775273229/1073741824),by norm_num⟩))) (.split (.split (.leaf ⟨(387636613/536870912),(3043365/4194304),by norm_num⟩) (.leaf ⟨(779101437/1073741824),(195729791/268435456),by norm_num⟩)) (.split (.leaf ⟨(782919161/1073741824),(12292601/16777216),by norm_num⟩) (.leaf ⟨(786726461/1073741824),(790523407/1073741824),by norm_num⟩)))))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check09
