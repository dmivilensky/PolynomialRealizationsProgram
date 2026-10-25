import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch017
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 17. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch017
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-60729629/62500000),(716014121/250000000),(796777507/500000000),(-12871807473/1000000000),(-3285211761/500000000),(-84101381/200000000),(1713258217/1000000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-3029530769013/1000000000000),(-1513241463427/500000000000),by norm_num⟩,⟨(19128994887/1000000000000),(4223797677/200000000000),by norm_num⟩,⟨(-1176103121069/1000000000000),(-1104930596839/1000000000000),by norm_num⟩,⟨(-430200687371/1000000000000),(-42472103757/100000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6030657474499/1000000000000),(-376302361589/62500000000),by norm_num⟩,⟨(5820743213113/1000000000000),(5839250134369/1000000000000),by norm_num⟩,⟨(-65655668229/50000000000),(-124108625803/200000000000),by norm_num⟩,⟨(3588354812061/1000000000000),(1810725252437/500000000000),by norm_num⟩,⟨(-2042447600001/500000000000),(-2040089399999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-1314092180223/1000000000000),(-242327591427/200000000000),by norm_num⟩,⟨(-2207221431241/200000000000),(-438382889059/40000000000),by norm_num⟩,⟨(23972132198227/1000000000000),(6433113755333/250000000000),by norm_num⟩,⟨(1019581716183/500000000000),(2141214582257/1000000000000),by norm_num⟩,⟨(-6343184397493/500000000000),(-12647859039967/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6927709246741/500000000000),(-136951299971/10000000000),by norm_num⟩,⟨(2461320214159/100000000000),(6176560585579/250000000000),by norm_num⟩,⟨(-28190781907191/500000000000),(-12588623903071/250000000000),by norm_num⟩,⟨(148894237279/125000000000),(370149102031/250000000000),by norm_num⟩,⟨(-23549619505599/1000000000000),(-11672112766881/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(864741044207/500000000000),(467091055619/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-398277787399/1000000000000),(405584872119/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-2536481852931/125000000000),(-2470879517083/125000000000),by norm_num⟩,⟨(-2816708213629/1000000000000),(-2421597323161/1000000000000),by norm_num⟩],![⟨(589409674559/500000000000),(253112071427/200000000000),by norm_num⟩,⟨(352927031951/1000000000000),(48934790637/125000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-580742753229/125000000000),(-1135782457281/250000000000),by norm_num⟩,⟨(2495533232767/100000000000),(25154648622917/1000000000000),by norm_num⟩],![⟨(586432705883/1000000000000),(26570585547/40000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(252081826997/15625000000),(4924337040519/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-50742718921879/1000000000000),(-49608492079857/1000000000000),by norm_num⟩,⟨(-26352996461771/500000000000),(-1279008026301/25000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-1211177351/8000000000),(-19057263723/250000000000),by norm_num⟩,⟨(-869090258071/500000000000),(-284510058473/250000000000),by norm_num⟩,⟨(-16838789659259/250000000000),(-31982738335563/500000000000),by norm_num⟩,⟨(-70463465896481/500000000000),(-130739981760157/1000000000000),by norm_num⟩,⟨(-1588158584393/500000000000),(-11878537821/10000000000),by norm_num⟩,⟨(-4610118854229/100000000000),(-21692016894627/500000000000),by norm_num⟩,⟨(36546634572529/1000000000000),(43443770739/1000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch017.I0
        (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch017.I0
    (coordinateBox P5.Batch017.C0.center P5.Batch017.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch017.I0 P5.Batch017.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch017
