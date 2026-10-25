import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign II.upper.1.discriminant on [1,6/5].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check20
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,-9,144,-712,3772,-318,10644,1172,16400,-6981,25240,-22448,22044,-13888,5572,-2012,-616,-4],[0,-60,-680,760,160,1440,5120,-1280,12040,-8220,13880,-8840,7120,-2760,880,-240,-120],[30,20,1040,50,3740,-420,5900,-1400,5180,-1200,2600,70,620,400,60,80,30],[0,200,0,500,0,200,0,-400,0,-400,0,-100],[0,-100,-960,-2420,-4800,-8705,-21440,2100,-56000,37750,-72000,47800,-42560,20455,-8000,1920,960],[0],[0],[0],[0,0,480,960,2400,3840,10720,-1600,28000,-19200,36000,-24000,21280,-10240,4000,-960,-480]]

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

end polyak.Certificates.Startup.Check20
