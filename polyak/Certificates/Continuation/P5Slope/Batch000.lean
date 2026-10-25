import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch000
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 0. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch000
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-221856741/200000000),(3172549451/500000000),(685199661/250000000),(-5789316833/250000000),(-8580771239/1000000000),(-368718931/1000000000),(1543594811/1000000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-3001727189119/1000000000000),(-1499999999999/500000000000),by norm_num⟩,⟨(-1/500000000000),(379387711/250000000000),by norm_num⟩,⟨(-78013897753/50000000000),(-4516699757/3125000000),by norm_num⟩,⟨(-416435789289/1000000000000),(-25496896569/62500000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6000826279741/1000000000000),(-2999999999999/500000000000),by norm_num⟩,⟨(5986612287701/1000000000000),(3000000000001/500000000000),by norm_num⟩,⟨(4029389779/31250000000),(1299327494071/1000000000000),by norm_num⟩,⟨(1746218408521/500000000000),(3540782033493/1000000000000),by norm_num⟩,⟨(-2002358200001/500000000000),(-1999999999999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-9330488851/125000000000),(1/500000000000),by norm_num⟩,⟨(-6000000000001/500000000000),(-11939680628251/1000000000000),by norm_num⟩,⟨(29308977683063/1000000000000),(6415091033867/200000000000),by norm_num⟩,⟨(1553570044963/1000000000000),(854384187383/500000000000),by norm_num⟩,⟨(-12037753444431/1000000000000),(-5999999999999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-12082338361657/1000000000000),(-5999999999999/500000000000),by norm_num⟩,⟨(11999999999999/500000000000),(24015717521277/1000000000000),by norm_num⟩,⟨(-67366358162219/1000000000000),(-5838275987389/100000000000),by norm_num⟩,⟨(1509980716283/1000000000000),(30034114231/15625000000),by norm_num⟩,⟨(-20189123552789/1000000000000),(-9999999999999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-1/500000000000),(8142587697/100000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-17061534067/62500000000),(285198598787/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-15926693896861/1000000000000),(-3815751414317/250000000000),by norm_num⟩,⟨(-39422583799/31250000000),(-178820186263/250000000000),by norm_num⟩],![⟨(-1/500000000000),(1782054767/31250000000),by norm_num⟩,⟨(-1/500000000000),(3456163801/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-3088679150793/1000000000000),(-1499999999999/500000000000),by norm_num⟩,⟨(10999999999999/500000000000),(5540531523433/250000000000),by norm_num⟩],![⟨(-1/500000000000),(6926301869/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(1835721817077/200000000000),(1194760326117/100000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-11613051432987/250000000000),(-22488309651591/500000000000),by norm_num⟩,⟨(-45931850189949/1000000000000),(-43851497521761/1000000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-49373113677/200000000000),(-108244817437/1000000000000),by norm_num⟩,⟨(-65356599293/500000000000),(249849924003/250000000000),by norm_num⟩,⟨(-15287337261959/200000000000),(-70707833510143/1000000000000),by norm_num⟩,⟨(-66443523117089/500000000000),(-119490477798587/1000000000000),by norm_num⟩,⟨(-2489424294601/500000000000),(-843588606729/250000000000),by norm_num⟩,⟨(-36401468612079/1000000000000),(-6810207258979/200000000000),by norm_num⟩,⟨(20644176516229/1000000000000),(26570743335977/1000000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch000.I0
        (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch000.I0
    (coordinateBox P5.Batch000.C0.center P5.Batch000.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch000.I0 P5.Batch000.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch000
