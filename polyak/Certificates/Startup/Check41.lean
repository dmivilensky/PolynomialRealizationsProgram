import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign III.k8.upper on [6/5,1713/1000].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check41
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-9,0,-36,0,-84,0,-124,0,-172,0,-140,0,-124,0,-78,0,-78,0,-124,0,-140,0,-172,0,-124,0,-84,0,-36,0,-9,0,-1],[0,0,0,0,0,0,0,0,0,0,-64,0,192,0,256,0,832,0,640,0,832,0,256,0,192,0,-64],[20,8,174,48,696,112,1664,112,2582,0,2884,-112,2268,-112,1412,-48,1010,-16,740,-48,1040,-112,872,-112,954,0,548,112,348,112,148,48,42,8,6],[8,0,68,0,256,0,560,0,808,0,820,0,448,0,96,0,-168,0,-116,0,64,0,112,0,120,0,-4],[-1,0,-9,0,-36,0,-84,0,-112,0,-126,0,-140,0,-165,0,-190,0,-165,0,-140,0,-126,0,-112,0,-84,0,-36,0,-9,0,-1],[0],[0],[0],[0],[0],[-32,0,-288,0,-1152,0,-2688,0,-4032,0,-4032,0,-2688,0,-1152,0,-288,0,-32],[0],[0],[0],[0],[0],[0],[0],[16,0,144,0,576,0,1344,0,2016,0,2016,0,1344,0,576,0,144,0,16]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨(6/5),(1713/1000),by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.split (.split (.leaf ⟨(197630851/268435456),(809841385/1073741824),by norm_num⟩) (.leaf ⟨(404920691/536870912),(828897881/1073741824),by norm_num⟩)) (.split (.leaf ⟨(414448939/536870912),(847702629/1073741824),by norm_num⟩) (.leaf ⟨(423851313/536870912),(866265639/1073741824),by norm_num⟩))) (.split (.split (.leaf ⟨(216566409/268435456),(884597065/1073741824),by norm_num⟩) (.leaf ⟨(442298531/536870912),(902707089/1073741824),by norm_num⟩)) (.split (.leaf ⟨(451353543/536870912),(115075729/134217728),by norm_num⟩) (.leaf ⟨(920605829/1073741824),(469151635/536870912),by norm_num⟩)))) (.split (.split (.split (.leaf ⟨(938303267/1073741824),(29869037/33554432),by norm_num⟩) (.leaf ⟨(955809181/1073741824),(486566551/536870912),by norm_num⟩)) (.split (.leaf ⟨(973133099/1073741824),(990284267/1073741824),by norm_num⟩) (.leaf ⟨(123785533/134217728),(1007271611/1073741824),by norm_num⟩))) (.split (.split (.leaf ⟨(125908951/134217728),(1024103733/1073741824),by norm_num⟩) (.leaf ⟨(512051865/536870912),(520394443/536870912),by norm_num⟩)) (.split (.leaf ⟨(1040788883/1073741824),(264333743/268435456),by norm_num⟩) (.leaf ⟨(1057334969/1073741824),(1073749541/1073741824),by norm_num⟩))))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check41
