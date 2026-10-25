import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch001
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 1. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch001
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-68717947/62500000),(1198528023/200000000),(2636023551/1000000000),(-22101982619/1000000000),(-4198616069/500000000),(-373582417/1000000000),(24265153/15625000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-600688384011/200000000000),(-1500795647367/500000000000),by norm_num⟩,⟨(700384897/500000000000),(1487554981/500000000000),by norm_num⟩,⟨(-1529652406523/1000000000000),(-1418947605761/1000000000000),by norm_num⟩,⟨(-208854098501/500000000000),(-409497339587/1000000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-600176274483/100000000000),(-15000270857/2500000000),by norm_num⟩,⟨(186680935337/31250000000),(2993876736711/500000000000),by norm_num⟩,⟨(1274997481/125000000000),(141738319183/125000000000),by norm_num⟩,⟨(3499879828097/1000000000000),(1773437595809/500000000000),by norm_num⟩,⟨(-2004716400001/500000000000),(-2002358199999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-74486742053/500000000000),(-71667090243/1000000000000),by norm_num⟩,⟨(-5970803935209/500000000000),(-11879749986023/1000000000000),by norm_num⟩,⟨(2893197678973/100000000000),(15800258119129/500000000000),by norm_num⟩,⟨(1591006573987/1000000000000),(1741558478899/1000000000000),by norm_num⟩,⟨(-6037775688859/500000000000),(-6018876722213/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-1520924898459/125000000000),(-754944221797/62500000000),by norm_num⟩,⟨(12006141170623/500000000000),(24034970348429/1000000000000),by norm_num⟩,⟨(-33225851016729/500000000000),(-28877754839811/500000000000),by norm_num⟩,⟨(738404549423/500000000000),(1878429691579/1000000000000),by norm_num⟩,⟨(-16303347113/800000000),(-1261820222049/62500000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(40396717587/500000000000),(82658577039/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-70118946859/250000000000),(14587639633/50000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-3239231001321/200000000000),(-7772653083897/500000000000),by norm_num⟩,⟨(-685852383689/500000000000),(-419087231603/500000000000),by norm_num⟩],![⟨(56942723621/1000000000000),(115502802853/1000000000000),by norm_num⟩,⟨(13481514827/1000000000000),(28491792221/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-3177525936283/1000000000000),(-1543951247799/500000000000),by norm_num⟩,⟨(22160836712273/1000000000000),(2232601228901/100000000000),by norm_num⟩],![⟨(16307262899/500000000000),(34749210267/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(4771927731117/500000000000),(3088947274063/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-5840860378481/125000000000),(-9056698830351/200000000000),by norm_num⟩,⟨(-23187759159989/500000000000),(-22171930970161/500000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-236942631377/1000000000000),(-13076530311/125000000000),by norm_num⟩,⟨(-136271976491/500000000000),(12533098397/15625000000),by norm_num⟩,⟨(-4730691338001/62500000000),(-70197101571403/1000000000000),by norm_num⟩,⟨(-133508755100969/1000000000000),(-120424023848717/1000000000000),by norm_num⟩,⟨(-2443354204529/500000000000),(-407884466969/125000000000),by norm_num⟩,⟨(-18468299452031/500000000000),(-8641783196149/250000000000),by norm_num⟩,⟨(10778532718449/500000000000),(3441458632931/125000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch001.I0
        (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch001.I0
    (coordinateBox P5.Batch001.C0.center P5.Batch001.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch001.I0 P5.Batch001.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch001
