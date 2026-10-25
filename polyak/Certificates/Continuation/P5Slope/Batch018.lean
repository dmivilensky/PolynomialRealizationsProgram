import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch018
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 18. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch018
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-964991867/1000000000),(2756601659/1000000000),(1552683661/1000000000),(-2511011619/200000000),(-3247699479/500000000),(-211123149/500000000),(1723618287/1000000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-3031094738289/1000000000000),(-1514000193559/500000000000),by norm_num⟩,⟨(5011344673/250000000000),(5511437717/250000000000),by norm_num⟩,⟨(-579866288451/500000000000),(-272505873193/250000000000),by norm_num⟩,⟨(-430637147789/1000000000000),(-212632405423/500000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-3016639260533/500000000000),(-6023126407091/1000000000000),by norm_num⟩,⟨(1453367800931/250000000000),(233284678763/40000000000),by norm_num⟩,⟨(-1371304933751/1000000000000),(-347143594263/500000000000),by norm_num⟩,⟨(1796346494409/500000000000),(3625221878377/1000000000000),by norm_num⟩,⟨(-2044805800001/500000000000),(-4084895199997/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-138614321123/100000000000),(-160336950949/125000000000),by norm_num⟩,⟨(-1372631286591/125000000000),(-5451965107923/500000000000),by norm_num⟩,⟨(23711275854467/1000000000000),(12719793614931/500000000000),by norm_num⟩,⟨(2060447076981/1000000000000),(2160500560459/1000000000000),by norm_num⟩,⟨(-12724923038857/1000000000000),(-12686368794981/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-13979634995169/1000000000000),(-1381569712381/100000000000),by norm_num⟩,⟨(24670137639497/1000000000000),(6191540588351/250000000000),by norm_num⟩,⟨(-55953954156091/1000000000000),(-50025457082101/1000000000000),by norm_num⟩,⟨(1184393138207/1000000000000),(183644641711/125000000000),by norm_num⟩,⟨(-23755993547341/1000000000000),(-11774809752797/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(1856467903609/1000000000000),(999563497773/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-405748158939/1000000000000),(413047676483/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-5135181250407/250000000000),(-5005157034479/250000000000),by norm_num⟩,⟨(-57846906759/20000000000),(-625797344289/250000000000),by norm_num⟩],![⟨(1263213503407/1000000000000),(1351952777273/1000000000000),by norm_num⟩,⟨(95708227703/250000000000),(211574603963/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-474167272513/100000000000),(-4638084600731/1000000000000),by norm_num⟩,⟨(25142079710209/1000000000000),(1013721140409/40000000000),by norm_num⟩],![⟨(155791345117/250000000000),(8799241721/12500000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(8297434531881/500000000000),(10105186951233/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-50981858359343/1000000000000),(-49859133849317/1000000000000),by norm_num⟩,⟨(-26536783208403/500000000000),(-5154695357763/100000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-74354659473/500000000000),(-18895469717/250000000000),by norm_num⟩,⟨(-449529782981/250000000000),(-1213878911831/1000000000000),by norm_num⟩,⟨(-16743887382949/250000000000),(-63660034174089/1000000000000),by norm_num⟩,⟨(-35323104385599/250000000000),(-16401425889433/125000000000),by norm_num⟩,⟨(-763745260989/250000000000),(-260220742423/250000000000),by norm_num⟩,⟨(-23357476553737/500000000000),(-43973733285467/1000000000000),by norm_num⟩,⟨(37517821281887/1000000000000),(5560061743971/125000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch018.I0
        (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch018.I0
    (coordinateBox P5.Batch018.C0.center P5.Batch018.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch018.I0 P5.Batch018.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch018
