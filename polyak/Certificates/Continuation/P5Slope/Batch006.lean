import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch006
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 6. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch006
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-52719581/50000000),(4611016943/1000000000),(551094171/250000000),(-18003142771/1000000000),(-9559449/1250000),(-78684687/200000000),(1601439359/1000000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-752961393819/250000000000),(-1504746812439/500000000000),by norm_num⟩,⟨(3873527007/500000000000),(9527620279/1000000000000),by norm_num⟩,⟨(-2180537147/1562500000),(-1301755216781/1000000000000),by norm_num⟩,⟨(-423002924979/1000000000000),(-83184509617/200000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-1502011531573/250000000000),(-6003023413927/1000000000000),by norm_num⟩,⟨(2958393389927/500000000000),(2966442310031/500000000000),by norm_num⟩,⟨(-251863407577/500000000000),(86749050217/200000000000),by norm_num⟩,⟨(1766343782147/500000000000),(893510233357/250000000000),by norm_num⟩,⟨(-2016507400001/500000000000),(-4028298399997/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-51692897331/100000000000),(-214505762437/500000000000),by norm_num⟩,⟨(-2330630322397/200000000000),(-11585140223357/1000000000000),by norm_num⟩,⟨(2718741948841/100000000000),(5893008745297/200000000000),by norm_num⟩,⟨(1757910844153/1000000000000),(377781846107/200000000000),by norm_num⟩,⟨(-6132604188511/500000000000),(-152839849993/12500000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6315598162817/500000000000),(-6258293893049/500000000000),by norm_num⟩,⟨(24126638098477/1000000000000),(24177878200027/1000000000000),by norm_num⟩,⟨(-62497031890491/1000000000000),(-13739570562487/250000000000),by norm_num⟩,⟨(671824632087/500000000000),(170040806299/100000000000),by norm_num⟩,⟨(-5335906438977/250000000000),(-21148843593983/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(522330690033/1000000000000),(622767669939/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-12696971421/40000000000),(324830454461/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-8755618692009/500000000000),(-3382646664269/200000000000),by norm_num⟩,⟨(-1880708874491/1000000000000),(-280331581571/200000000000),by norm_num⟩],![⟨(363747350121/1000000000000),(21518524813/50000000000),by norm_num⟩,⟨(93567658067/1000000000000),(115006789351/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1812777116287/500000000000),(-1765766557651/500000000000),by norm_num⟩,⟨(5747967177939/250000000000),(9268021923/400000000),by norm_num⟩],![⟨(199031625277/1000000000000),(61907711381/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(2289588459893/200000000000),(14482325180749/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-48041891155881/1000000000000),(-23364681988351/500000000000),by norm_num⟩,⟨(-24240766816277/500000000000),(-46650820488167/1000000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-198255245727/1000000000000),(-90792312479/1000000000000),by norm_num⟩,⟨(-173291530711/200000000000),(-5173365663/1000000000000),by norm_num⟩,⟨(-72480474082857/1000000000000),(-67908433327103/1000000000000),by norm_num⟩,⟨(-3406286130581/25000000000),(-24882442644007/200000000000),by norm_num⟩,⟨(-879886605099/200000000000),(-106895060273/40000000000),by norm_num⟩,⟨(-9918663515029/250000000000),(-37204760348787/1000000000000),by norm_num⟩,⟨(1634408203961/62500000000),(32385345171721/1000000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch006.I0
        (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch006.I0
    (coordinateBox P5.Batch006.C0.center P5.Batch006.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch006.I0 P5.Batch006.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch006
