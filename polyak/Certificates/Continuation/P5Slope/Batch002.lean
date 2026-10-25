import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch002
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 2. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch002
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-34061671/31250000),(113390031/20000000),(158637857/62500000),(-21138095457/1000000000),(-8226629169/1000000000),(-378108821/1000000000),(781234373/500000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-375643087727/125000000000),(-93849358723/31250000000),by norm_num⟩,⟨(1376445093/500000000000),(1094483251/250000000000),by norm_num⟩,⟨(-375108460663/250000000000),(-174204209289/125000000000),by norm_num⟩,⟨(-418902881821/1000000000000),(-41094829239/100000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6002807856881/1000000000000),(-6000384876531/1000000000000),by norm_num⟩,⟨(5961489030819/1000000000000),(2987984796603/500000000000),by norm_num⟩,⟨(-102677506007/1000000000000),(9779638571/10000000000),by norm_num⟩,⟨(175349635289/50000000000),(1776360640053/500000000000),by norm_num⟩,⟨(-2007074600001/500000000000),(-2004716399999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-223021431719/1000000000000),(-71631341253/500000000000),by norm_num⟩,⟨(-11883459363631/1000000000000),(-2955045686299/250000000000),by norm_num⟩,⟨(14282517294369/500000000000),(6228641405971/200000000000),by norm_num⟩,⟨(813486037513/500000000000),(1773151979677/1000000000000),by norm_num⟩,⟨(-12113393799863/1000000000000),(-12075551377713/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-2451021703999/200000000000),(-6080562990257/500000000000),by norm_num⟩,⟨(24028385183043/1000000000000),(1202877817139/50000000000),by norm_num⟩,⟨(-65582185377107/1000000000000),(-714400834457/12500000000),by norm_num⟩,⟨(144600033903/100000000000),(1837636168989/1000000000000),by norm_num⟩,⟨(-20570183537767/1000000000000),(-4075836778249/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(41013841787/250000000000),(15731361019/62500000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-11516945991/40000000000),(149162398843/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-4115799668991/250000000000),(-15824339951569/1000000000000),by norm_num⟩,⟨(-18485960691/12500000000),(-957386878761/1000000000000),by norm_num⟩],![⟨(115330985797/1000000000000),(2193141699/12500000000),by norm_num⟩,⟨(3473359723/125000000000),(44016316261/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-408322572997/125000000000),(-3176038888427/1000000000000),by norm_num⟩,⟨(22323549452901/1000000000000),(22491601987199/1000000000000),by norm_num⟩],![⟨(16361370729/250000000000),(20921832503/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(9914172813503/1000000000000),(255391748621/20000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-46997101365771/1000000000000),(-5697953805707/125000000000),by norm_num⟩,⟨(-23405383240393/500000000000),(-44824599551759/1000000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-56963669781/250000000000),(-10130762619/100000000000),by norm_num⟩,⟨(-101442417733/250000000000),(123690168777/200000000000),by norm_num⟩,⟨(-37492169208571/500000000000),(-34852869175441/500000000000),by norm_num⟩,⟨(-67051465756311/500000000000),(-60653003522877/500000000000),by norm_num⟩,⟨(-958555324119/200000000000),(-787360724591/250000000000),by norm_num⟩,⟨(-37475769797857/1000000000000),(-7017380575339/200000000000),by norm_num⟩,⟨(2247148945141/100000000000),(14247787686557/500000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch002.I0
        (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch002.I0
    (coordinateBox P5.Batch002.C0.center P5.Batch002.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch002.I0 P5.Batch002.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch002
