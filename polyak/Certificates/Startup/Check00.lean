import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign I.lower.constant on [33/100,1].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check00
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,14,0,48,16,34,16,16],[0,0,-8,0,-20,0,-16,0,-4],[1,0,2,0,0,0,-2,0,-1],[0],[0,0,-32,0,-96,0,-96,0,-32],[0],[0],[0],[0,0,16,0,48,0,48,0,16]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨(33/100),1,by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.leaf ⟨(184123041/1073741824),(302139173/1073741824),by norm_num⟩) (.leaf ⟨(151069585/536870912),(213161835/536870912),by norm_num⟩)) (.split (.leaf ⟨(426323667/1073741824),(548382123/1073741824),by norm_num⟩) (.split (.leaf ⟨(68547765/134217728),(606996143/1073741824),by norm_num⟩) (.leaf ⟨(151749035/268435456),(41475559/67108864),by norm_num⟩)))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check00
