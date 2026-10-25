import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch014
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 14. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch014
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-496228753/500000000),(645282699/200000000),(1728068623/1000000000),(-13936942353/1000000000),(-3406719097/500000000),(-414699683/1000000000),(42058131/25000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-151239980331/50000000000),(-3021904563171/1000000000000),by norm_num⟩,⟨(3256291409/200000000000),(9117019033/500000000000),by norm_num⟩,⟨(-245651315157/200000000000),(-72014177633/62500000000),by norm_num⟩,⟨(-428704216159/1000000000000),(-52858955831/125000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-602334604243/100000000000),(-3007302212937/500000000000),by norm_num⟩,⟨(5843832820047/1000000000000),(5861864878431/1000000000000),by norm_num⟩,⟨(-562726583181/500000000000),(-380961535727/1000000000000),by norm_num⟩,⟨(3574752515699/1000000000000),(360969958141/100000000000),by norm_num⟩,⟨(-2035373000001/500000000000),(-2033014799999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-1097670741727/1000000000000),(-249608668079/250000000000),by norm_num⟩,⟨(-2240450533517/200000000000),(-11127617210797/1000000000000),by norm_num⟩,⟨(495616521431/20000000000),(26650863956969/1000000000000),by norm_num⟩,⟨(985799414209/500000000000),(2080167306007/1000000000000),by norm_num⟩,⟨(-6285486498259/500000000000),(-6266298354037/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-13495364054407/1000000000000),(-266928414821/20000000000),by norm_num⟩,⟨(4890793998657/200000000000),(24537430400429/1000000000000),by norm_num⟩,⟨(-28887905394257/500000000000),(-25711494693859/500000000000),by norm_num⟩,⟨(608819048369/500000000000),(304463793203/200000000000),by norm_num⟩,⟨(-2293636752327/100000000000),(-11366949176871/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(1366355437787/1000000000000),(186775991321/125000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-376093114937/1000000000000),(76668456517/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-9771364924067/500000000000),(-19002149395767/1000000000000),by norm_num⟩,⟨(-2581492324381/1000000000000),(-1083553381451/500000000000),by norm_num⟩],![⟨(936293802367/1000000000000),(508606567283/500000000000),by norm_num⟩,⟨(269864575739/1000000000000),(151667302863/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-2180970206693/500000000000),(-4261468592501/1000000000000),by norm_num⟩,⟨(12201509188871/500000000000),(12298609066927/500000000000),by norm_num⟩],![⟨(477764729999/1000000000000),(68385852221/125000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(14783968991177/1000000000000),(18198369228961/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-50021211162849/1000000000000),(-9769732976657/200000000000),by norm_num⟩,⟨(-25795392372089/500000000000),(-49982340340221/1000000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-80352550043/500000000000),(-78715343603/1000000000000),by norm_num⟩,⟨(-1542488122051/1000000000000),(-888700219961/1000000000000),by norm_num⟩,⟨(-8570666134529/125000000000),(-8115883905079/125000000000),by norm_num⟩,⟨(-69890895657473/500000000000),(-6462106495339/50000000000),by norm_num⟩,⟨(-3530221128499/1000000000000),(-808447640601/500000000000),by norm_num⟩,⟨(-44290303926689/1000000000000),(-41643828849111/1000000000000),by norm_num⟩,⟨(33661413598931/1000000000000),(40367588154723/1000000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch014.I0
        (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch014.I0
    (coordinateBox P5.Batch014.C0.center P5.Batch014.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch014.I0 P5.Batch014.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch014
