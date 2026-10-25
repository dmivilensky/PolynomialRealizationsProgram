import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign III.k5.upper on [6/5,1713/1000].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check35
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-6,0,-15,0,-30,0,-25,0,-19,0,-19,0,-25,0,-30,0,-15,0,-6,0,-1],[0,0,0,0,0,0,-8,0,56,0,72,0,144,0,72,0,56,0,-8],[20,8,114,24,294,16,464,-16,422,-24,246,-16,194,-24,170,-16,166,16,56,24,24,8,6],[8,0,44,0,104,0,132,0,64,0,4,0,-8,0,12,0,24],[-1,0,-6,0,-13,0,-24,0,-34,0,-36,0,-34,0,-24,0,-13,0,-6,0,-1],[0],[0],[0],[32,0,192,0,480,0,640,0,480,0,192,0,32],[0],[0],[0],[0],[0],[16,0,96,0,240,0,320,0,240,0,96,0,16]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨(6/5),(1713/1000),by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.split (.leaf ⟨(197630851/268435456),(828897881/1073741824),by norm_num⟩) (.leaf ⟨(414448939/536870912),(866265639/1073741824),by norm_num⟩)) (.split (.leaf ⟨(216566409/268435456),(902707089/1073741824),by norm_num⟩) (.leaf ⟨(451353543/536870912),(469151635/536870912),by norm_num⟩))) (.split (.split (.leaf ⟨(938303267/1073741824),(486566551/536870912),by norm_num⟩) (.leaf ⟨(973133099/1073741824),(1007271611/1073741824),by norm_num⟩)) (.split (.leaf ⟨(125908951/134217728),(520394443/536870912),by norm_num⟩) (.leaf ⟨(1040788883/1073741824),(1073749541/1073741824),by norm_num⟩)))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check35
