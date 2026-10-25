import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign II.lower.0.derivative on [1,6/5].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check05
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,3,11,46,-34,0,29,-46,-6,-3],[0,0,20,0,50,0,40,0,10],[-5,0,-20,0,-25,0,-10]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨1,(6/5),by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.leaf ⟨(663608941/1073741824),(728494839/1073741824),by norm_num⟩) (.split (.leaf ⟨(182123709/268435456),(379927129/536870912),by norm_num⟩) (.leaf ⟨(759854255/1073741824),(790523407/1073741824),by norm_num⟩))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check05
