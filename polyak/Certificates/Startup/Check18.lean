import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign II.upper.0.discriminant on [1,6/5].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check18
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,-9,414,1043,2872,1672,14154,-2798,23820,-12046,32530,-26253,25024,-12008,4102,-792,-516,-9],[0,0,0,120,440,-1060,2940,-3160,3440,-1300,-1440,2600,-3760,2420,-1500,440,-120,-60],[0,0,50,-460,80,-2270,-620,-4820,-1820,-5750,-1730,-4100,-620,-1610,-100,-220,-40,30],[0,0,-200,0,-1300,0,-3400,0,-4600,0,-3400,0,-1300,0,-200],[-25,0,-200,-960,-2570,-4800,-8780,-21440,2175,-56000,37900,-72000,47900,-42560,20480,-8000,1920,960],[0],[0],[0],[0,0,0,480,960,2400,3840,10720,-1600,28000,-19200,36000,-24000,21280,-10240,4000,-960,-480]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨1,(6/5),by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.leaf ⟨(663608941/1073741824),(348209503/536870912),by norm_num⟩) (.split (.leaf ⟨(696419003/1073741824),(89068477/134217728),by norm_num⟩) (.leaf ⟨(712547813/1073741824),(728494839/1073741824),by norm_num⟩))) (.split (.split (.leaf ⟨(182123709/268435456),(744262629/1073741824),by norm_num⟩) (.split (.leaf ⟨(372131313/536870912),(376040127/536870912),by norm_num⟩) (.leaf ⟨(752080251/1073741824),(379927129/536870912),by norm_num⟩))) (.split (.split (.leaf ⟨(759854255/1073741824),(191896273/268435456),by norm_num⟩) (.leaf ⟨(767585089/1073741824),(775273229/1073741824),by norm_num⟩)) (.split (.split (.leaf ⟨(387636613/536870912),(3043365/4194304),by norm_num⟩) (.leaf ⟨(779101437/1073741824),(195729791/268435456),by norm_num⟩)) (.split (.leaf ⟨(782919161/1073741824),(12292601/16777216),by norm_num⟩) (.leaf ⟨(786726461/1073741824),(790523407/1073741824),by norm_num⟩)))))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check18
