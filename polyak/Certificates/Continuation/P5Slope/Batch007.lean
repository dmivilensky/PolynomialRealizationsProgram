import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch007
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 7. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch007
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-1046040421/1000000000),(2196704687/500000000),(1066425079/500000000),(-17362350419/1000000000),(-7523564881/1000000000),(-396670629/1000000000),(1611374401/1000000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-1506747671411/500000000000),(-1505530659787/500000000000),by norm_num⟩,⟨(8907019897/1000000000000),(2143451353/200000000000),by norm_num⟩,⟨(-274378205337/200000000000),(-1280828291081/1000000000000),by norm_num⟩,⟨(-423879205949/1000000000000),(-416986119333/1000000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-150240338461/25000000000),(-6004036053123/1000000000000),by norm_num⟩,⟨(1476647632389/250000000000),(1480751484207/250000000000),by norm_num⟩,⟨(-59310320421/100000000000),(39311487271/125000000000),by norm_num⟩,⟨(13822395697/3906250000),(3578937864467/1000000000000),by norm_num⟩,⟨(-2018865600001/500000000000),(-2016507399999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-117988837677/200000000000),(-7817390901/15625000000),by norm_num⟩,⟨(-5798056420853/500000000000),(-5763551654023/500000000000),by norm_num⟩,⟨(26863275228567/1000000000000),(1163123863309/40000000000),by norm_num⟩,⟨(893897830893/500000000000),(1915486045077/1000000000000),by norm_num⟩,⟨(-192238644429/15625000000),(-12265208377017/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-12731272547531/1000000000000),(-6305972579257/500000000000),by norm_num⟩,⟨(4831753325583/200000000000),(12107376791463/500000000000),by norm_num⟩,⟨(-7726471559889/125000000000),(-10892118939979/200000000000),by norm_num⟩,⟨(330673053759/250000000000),(835905037531/500000000000),by norm_num⟩,⟨(-10769679941159/500000000000),(-21343625755903/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(38646992471/62500000000),(144414456043/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-81189111877/250000000000),(41487700647/125000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-17769086105441/1000000000000),(-17179799966939/1000000000000),by norm_num⟩,⟨(-246894825163/125000000000),(-1505491250231/1000000000000),by norm_num⟩],![⟨(85934148947/200000000000),(497985736621/1000000000000),by norm_num⟩,⟨(112236901367/1000000000000),(67530834787/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1858064936733/500000000000),(-1810637329013/500000000000),by norm_num⟩,⟨(23163050626571/1000000000000),(23343495207977/1000000000000),by norm_num⟩],![⟨(116506982751/500000000000),(8876881487/31250000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(11844926134747/1000000000000),(7462622416273/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-48295836644581/1000000000000),(-4700467299311/100000000000),by norm_num⟩,⟨(-48884596008077/1000000000000),(-47087232538151/1000000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-192229402173/1000000000000),(-44361782831/500000000000),by norm_num⟩,⟨(-966470512779/1000000000000),(-8642153553/62500000000),by norm_num⟩,⟨(-17980517057993/250000000000),(-3374787712057/50000000000),by norm_num⟩,⟨(-6837048901803/50000000000),(-62550974352099/500000000000),by norm_num⟩,⟨(-537094214697/125000000000),(-2547676367101/1000000000000),by norm_num⟩,⟨(-40235325940481/1000000000000),(-9436093108133/250000000000),by norm_num⟩,⟨(13538480589381/500000000000),(33367324740757/1000000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch007.I0
        (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch007.I0
    (coordinateBox P5.Batch007.C0.center P5.Batch007.C0.radius)
    jacobianBox parameterBox {precision:=-80}=true := by
  simp only [derivativeEnclosureCheck,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro i j
    fin_cases i
    · exact row0.1 j
    · exact row1.1 j
    · exact row2.1 j
    · exact row3.1 j
    · exact row4.1 j
    · exact row5.1 j
    · exact row6.1 j
  · intro i
    fin_cases i
    · exact row0.2
    · exact row1.2
    · exact row2.2
    · exact row3.2
    · exact row4.2
    · exact row5.2
    · exact row6.2

theorem accepted : sourceSlopeCheck P5.Batch007.I0 P5.Batch007.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch007
