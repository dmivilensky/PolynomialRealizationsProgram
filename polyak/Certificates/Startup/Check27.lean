import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign III.k1.upper on [6/5,1713/1000].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check27
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-10,0,-6,0,-1],[0,0,-8,0,-16,0,-16,0,-8],[20,8,64,-8,104,-8,32,8,4],[12,0,36,0,36,0,12],[32,0,96,0,96,0,32],[0],[16,0,48,0,48,0,16]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨(6/5),(1713/1000),by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.leaf ⟨(197630851/268435456),(866265639/1073741824),by norm_num⟩) (.leaf ⟨(216566409/268435456),(469151635/536870912),by norm_num⟩)) (.split (.leaf ⟨(938303267/1073741824),(1007271611/1073741824),by norm_num⟩) (.leaf ⟨(125908951/134217728),(1073749541/1073741824),by norm_num⟩))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check27
