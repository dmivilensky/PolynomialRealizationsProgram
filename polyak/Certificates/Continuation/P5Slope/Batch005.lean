import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch005
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 5. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch005
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-53147361/50000000),(4845441543/1000000000),(2280247943/1000000000),(-4673681759/250000000),(-1944746993/250000000),(-19498207/50000000),(1591572437/1000000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-60203720593/20000000000),(-3007921418803/1000000000000),by norm_num⟩,⟨(3277178313/500000000000),(8302016133/1000000000000),by norm_num⟩,⟨(-284029698213/200000000000),(-1323444864047/1000000000000),by norm_num⟩,⟨(-422070968357/1000000000000),(-414791928931/1000000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-1501645148073/250000000000),(-1500536665321/250000000000),by norm_num⟩,⟨(5927348714613/1000000000000),(1188619738023/200000000000),by norm_num⟩,⟨(-410318513031/1000000000000),(111834412491/200000000000),by norm_num⟩,⟨(1763315206519/500000000000),(3568985637009/1000000000000),by norm_num⟩,⟨(-2014149200001/500000000000),(-2011790999999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-88749734849/200000000000),(-11176888763/31250000000),by norm_num⟩,⟨(-5855199697213/500000000000),(-11643451882391/1000000000000),by norm_num⟩,⟨(27519246010579/1000000000000),(29864104330601/1000000000000),by norm_num⟩,⟨(1726955617613/1000000000000),(930720544237/500000000000),by norm_num⟩,⟨(-2445437599889/200000000000),(-6094606055361/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-12533495228157/1000000000000),(-6211881821019/500000000000),by norm_num⟩,⟨(24097375938283/1000000000000),(3017949342237/125000000000),by norm_num⟩,⟨(-63214502742029/1000000000000),(-55475460214357/1000000000000),by norm_num⟩,⟨(683175176277/500000000000),(43278699131/25000000000),by norm_num⟩,⟨(-5287210898497/250000000000),(-20955010859329/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(3431364497/8000000000),(263055201951/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-310080273547/1000000000000),(318167723693/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-3450376993021/200000000000),(-16644614385639/1000000000000),by norm_num⟩,⟨(-222998274823/125000000000),(-1295097781291/1000000000000),by norm_num⟩],![⟨(9355392061/31250000000),(18216523189/50000000000),by norm_num⟩,⟨(94756639/1250000000),(47946066637/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1767668813453/500000000000),(-1721081381487/500000000000),by norm_num⟩,⟨(2282228038227/100000000000),(22998109937469/1000000000000),by norm_num⟩],![⟨(10330450533/62500000000),(42295263573/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(5528227675239/500000000000),(14045368857551/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-47785362876723/1000000000000),(-23225032560929/500000000000),by norm_num⟩,⟨(-48073148053361/1000000000000),(-23103537608261/500000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-102388025877/500000000000),(-93064711991/1000000000000),by norm_num⟩,⟨(-95111752087/125000000000),(136184888213/1000000000000),by norm_num⟩,⟨(-14612716765787/200000000000),(-34167397038437/500000000000),by norm_num⟩,⟨(-67872269430319/500000000000),(-12369100611687/100000000000),by norm_num⟩,⟨(-4500385588521/1000000000000),(-2794938168373/1000000000000),by norm_num⟩,⟨(-39118437950559/1000000000000),(-36669292428859/1000000000000),by norm_num⟩,⟨(25227018930933/1000000000000),(15703685898001/500000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch005.I0
        (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch005.I0
    (coordinateBox P5.Batch005.C0.center P5.Batch005.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch005.I0 P5.Batch005.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch005
