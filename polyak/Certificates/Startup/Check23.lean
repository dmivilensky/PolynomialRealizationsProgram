import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign III.upper.derivative on [6/5,1713/1000].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check23
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,0,0,-65,96,-425,464,-1103,880,-1463,800,-1047,320,-383,16,-57,-16,-1,0,0,0,0,0,0,0,0,0,0,0,256,-512,768,-512,256],[0,0,0,-32,28,-224,160,-640,356,-960,384,-800,196,-352,32,-64,-4],[0,0,-2,0,-22,-16,-74,-48,-142,-32,-174,32,-122,48,-38,16,-2],[0,0,-4,0,-32,0,-92,0,-128,0,-92,0,-32,0,-4],[-1,0,-9,0,-31,0,-55,0,-55,0,-31,0,-9,0,-1]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨(6/5),(1713/1000),by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.leaf ⟨(197630851/268435456),(866265639/1073741824),by norm_num⟩) (.leaf ⟨(216566409/268435456),(469151635/536870912),by norm_num⟩)) (.leaf ⟨(938303267/1073741824),(1073749541/1073741824),by norm_num⟩)

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check23
