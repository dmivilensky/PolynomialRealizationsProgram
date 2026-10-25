import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch013
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 13. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch013
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-199929813/200000000),(420305623/125000000),(1777351009/1000000000),(-14336087857/1000000000),(-6901255391/1000000000),(-412544343/1000000000),(83603557/50000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-377901073409/125000000000),(-3020369493709/1000000000000),by norm_num⟩,⟨(15295924907/1000000000000),(8616775007/500000000000),by norm_num⟩,⟨(-623375055831/500000000000),(-1168924394247/1000000000000),by norm_num⟩,⟨(-428137434071/1000000000000),(-3377405183/8000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-3010547737791/500000000000),(-150318599567/25000000000),by norm_num⟩,⟨(5851986853033/1000000000000),(5869837642281/1000000000000),by norm_num⟩,⟨(-1058123088339/1000000000000),(-294252050823/1000000000000),by norm_num⟩,⟨(223124933379/62500000000),(901404798283/250000000000),by norm_num⟩,⟨(-2033014800001/500000000000),(-2030656599999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-1025413532783/1000000000000),(-231836927151/250000000000),by norm_num⟩,⟨(-1407246450683/125000000000),(-223680497843/20000000000),by norm_num⟩,⟨(25060396067201/1000000000000),(26971452383621/1000000000000),by norm_num⟩,⟨(1947735171327/1000000000000),(257333767343/125000000000),by norm_num⟩,⟨(-12532596708079/1000000000000),(-3123566227123/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-668980063909/50000000000),(-661729516847/50000000000),by norm_num⟩,⟨(24404949949239/1000000000000),(2448497659227/100000000000),by norm_num⟩,⟨(-29140376457609/500000000000),(-12952010988713/250000000000),by norm_num⟩,⟨(4914791233/4000000000),(1538901262853/1000000000000),by norm_num⟩,⟨(-22733898353747/1000000000000),(-22532398992411/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(1251131152129/1000000000000),(275080701863/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-23045867591/62500000000),(187982707097/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-19291924698659/1000000000000),(-2343187444991/125000000000),by norm_num⟩,⟨(-500021250307/200000000000),(-1039389247249/500000000000),by norm_num⟩],![⟨(858928068667/1000000000000),(937963733247/1000000000000),by norm_num⟩,⟨(244325321569/1000000000000),(69042959147/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-33346058297/7812500000),(-4168609691081/1000000000000),by norm_num⟩,⟨(12110806297819/500000000000),(24414022063693/1000000000000),by norm_num⟩],![⟨(44205029057/100000000000),(63578786259/125000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(14346445376329/1000000000000),(2213975712523/125000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-49778938249087/1000000000000),(-12148048446301/250000000000),by norm_num⟩,⟨(-51214174353449/1000000000000),(-12395680616589/250000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-164278392751/1000000000000),(-79748590437/1000000000000),by norm_num⟩,⟨(-735683040477/500000000000),(-398703343171/500000000000),by norm_num⟩,⟨(-68995101160511/1000000000000),(-65264154004297/1000000000000),by norm_num⟩,⟨(-69690978216201/500000000000),(-128711502818679/1000000000000),by norm_num⟩,⟨(-3644812334499/1000000000000),(-1755939046277/1000000000000),by norm_num⟩,⟨(-21848318838547/500000000000),(-10268301207453/250000000000),by norm_num⟩,⟨(32708787446801/1000000000000),(39352907595229/1000000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch013.I0
        (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch013.I0
    (coordinateBox P5.Batch013.C0.center P5.Batch013.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch013.I0 P5.Batch013.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch013
