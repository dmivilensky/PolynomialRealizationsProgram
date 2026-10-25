import polyak.Numerics.ComputedBivariate

/-!
Article: initialized-spiral sign III.k4.upper on [6/5,1713/1000].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.Check33
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

/-- Article: exact integer numerator of the independently specified source sign. -/
def numeratorSource : polyak.Numerics.IntegerBivariate.Source := [[0,0,-1,0,-5,0,-8,0,-16,0,-18,0,-18,0,-16,0,-8,0,-5,0,-1],[0,0,0,0,0,0,-32,0,-32,0,-64,0,-32,0,-32],[20,8,94,16,190,0,228,-16,162,-16,84,-16,74,0,20,16,18,8,6],[8,0,36,0,72,0,100,0,88,0,60,0,24,0,-4],[-1,0,-5,0,-4,0,5,0,10,0,5,0,-4,0,-5,0,-1],[0],[-32,0,-160,0,-320,0,-320,0,-160,0,-32],[0],[0],[0],[16,0,80,0,160,0,160,0,80,0,16]]

/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := polyak.Numerics.IntegerBivariate.rationalCode numeratorSource

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := ⟨(6/5),(1713/1000),by norm_num⟩

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := .split (.split (.split (.split (.split (.leaf ⟨(197630851/268435456),(800215675/1073741824),by norm_num⟩) (.leaf ⟨(100026959/134217728),(809841385/1073741824),by norm_num⟩)) (.split (.leaf ⟨(404920691/536870912),(409700859/536870912),by norm_num⟩) (.leaf ⟨(819401715/1073741824),(828897881/1073741824),by norm_num⟩))) (.split (.split (.leaf ⟨(414448939/536870912),(419165551/536870912),by norm_num⟩) (.leaf ⟨(838331099/1073741824),(847702629/1073741824),by norm_num⟩)) (.split (.split (.leaf ⟨(423851313/536870912),(852365649/1073741824),by norm_num⟩) (.leaf ⟨(426182823/536870912),(428506859/536870912),by norm_num⟩)) (.split (.leaf ⟨(857013715/1073741824),(861646995/1073741824),by norm_num⟩) (.leaf ⟨(53852937/67108864),(866265639/1073741824),by norm_num⟩))))) (.split (.split (.split (.split (.leaf ⟨(216566409/268435456),(54429363/67108864),by norm_num⟩) (.leaf ⟨(870869805/1073741824),(875459663/1073741824),by norm_num⟩)) (.split (.leaf ⟨(218864915/268435456),(440017681/536870912),by norm_num⟩) (.leaf ⟨(880035359/1073741824),(884597065/1073741824),by norm_num⟩))) (.split (.split (.leaf ⟨(442298531/536870912),(444572465/536870912),by norm_num⟩) (.leaf ⟨(889144927/1073741824),(893679117/1073741824),by norm_num⟩)) (.split (.leaf ⟨(446839557/536870912),(112274973/134217728),by norm_num⟩) (.leaf ⟨(898199781/1073741824),(902707089/1073741824),by norm_num⟩)))) (.split (.split (.split (.leaf ⟨(451353543/536870912),(453600595/536870912),by norm_num⟩) (.leaf ⟨(907201187/1073741824),(911682243/1073741824),by norm_num⟩)) (.leaf ⟨(14245035/16777216),(115075729/134217728),by norm_num⟩)) (.split (.leaf ⟨(920605829/1073741824),(929479097/1073741824),by norm_num⟩) (.leaf ⟨(464739547/536870912),(469151635/536870912),by norm_num⟩))))) (.split (.split (.split (.split (.leaf ⟨(938303267/1073741824),(473539783/536870912),by norm_num⟩) (.leaf ⟨(947079563/1073741824),(29869037/33554432),by norm_num⟩)) (.split (.leaf ⟨(955809181/1073741824),(964493307/1073741824),by norm_num⟩) (.leaf ⟨(120561663/134217728),(486566551/536870912),by norm_num⟩))) (.split (.split (.leaf ⟨(973133099/1073741824),(981729713/1073741824),by norm_num⟩) (.leaf ⟨(490864855/536870912),(990284267/1073741824),by norm_num⟩)) (.split (.leaf ⟨(123785533/134217728),(998797871/1073741824),by norm_num⟩) (.leaf ⟨(249699467/268435456),(1007271611/1073741824),by norm_num⟩)))) (.split (.split (.split (.leaf ⟨(125908951/134217728),(1015706551/1073741824),by norm_num⟩) (.leaf ⟨(253926637/268435456),(1024103733/1073741824),by norm_num⟩)) (.split (.leaf ⟨(512051865/536870912),(516232089/536870912),by norm_num⟩) (.leaf ⟨(1032464175/1073741824),(520394443/536870912),by norm_num⟩))) (.split (.split (.leaf ⟨(1040788883/1073741824),(65567427/67108864),by norm_num⟩) (.leaf ⟨(1049078829/1073741824),(264333743/268435456),by norm_num⟩)) (.split (.leaf ⟨(1057334969/1073741824),(1065558239/1073741824),by norm_num⟩) (.leaf ⟨(266389559/268435456),(1073749541/1073741824),by norm_num⟩)))))

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {r q : ℝ} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  polyak.Numerics.ComputedBivariate.check_sound witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.Check33
