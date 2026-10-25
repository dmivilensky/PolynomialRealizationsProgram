import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign II.upper.beta on [1,6/5].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check15
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-1,96,-38,176,-26,64,10,-16,-1],[0,0,0,-32,28,-128,76,-160,44,-64,-4],[0,0,-2,0,-16,-16,-20,0,-32,16,-2],[0,0,-4,0,-20,0,-20,0,-4],[-1,0,-6,0,-10,0,-6,0,-1]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨1,(6/5),by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.split (.leaf ⟨(663608941/1073741824),(680106463/1073741824),by norm_num⟩) (.leaf ⟨(170026615/268435456),(348209503/536870912),by norm_num⟩)) (.split (.leaf ⟨(696419003/1073741824),(89068477/134217728),by norm_num⟩) (.leaf ⟨(712547813/1073741824),(728494839/1073741824),by norm_num⟩))) (.split (.split (.leaf ⟨(182123709/268435456),(744262629/1073741824),by norm_num⟩) (.leaf ⟨(372131313/536870912),(379927129/536870912),by norm_num⟩)) (.split (.leaf ⟨(759854255/1073741824),(775273229/1073741824),by norm_num⟩) (.split (.leaf ⟨(387636613/536870912),(195729791/268435456),by norm_num⟩) (.leaf ⟨(782919161/1073741824),(790523407/1073741824),by norm_num⟩))))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check15
