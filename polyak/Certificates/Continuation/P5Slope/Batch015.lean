import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch015
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 15. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch015
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-197080329/200000000),(774604467/250000000),(1681110663/1000000000),(-3390275823/250000000),(-3364603393/500000000),(-20837013/50000000),(846304743/500000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-3026383462507/1000000000000),(-1511717552581/500000000000),by norm_num⟩,⟨(2156007393/125000000000),(19214268173/1000000000000),by norm_num⟩,⟨(-605168871717/500000000000),(-568005477423/500000000000),by norm_num⟩,⟨(-214617920649/500000000000),(-84705286561/200000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-3012845223439/500000000000),(-3008287458921/500000000000),by norm_num⟩,⟨(5835914524547/1000000000000),(1463528897213/250000000000),by norm_num⟩,⟨(-238061437791/200000000000),(-232058712003/500000000000),by norm_num⟩,⟨(1789695666223/500000000000),(3613694465067/1000000000000),by norm_num⟩,⟨(-2037731200001/500000000000),(-2035372999999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-584931927997/500000000000),(-1069509195391/1000000000000),by norm_num⟩,⟨(-11146704780063/1000000000000),(-11071410014649/1000000000000),by norm_num⟩,⟨(4901311143303/200000000000),(5267550468267/200000000000),by norm_num⟩,⟨(997384758811/500000000000),(1050536314421/500000000000),by norm_num⟩,⟨(-1576174221727/125000000000),(-6285486498257/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-3403316685771/250000000000),(-6730235149153/500000000000),by norm_num⟩,⟨(4901012208423/200000000000),(12295914054343/500000000000),by norm_num⟩,⟨(-28645804640841/500000000000),(-10210549459193/200000000000),by norm_num⟩,⟨(1207728763381/1000000000000),(1507117571159/1000000000000),by norm_num⟩,⟨(-11569904530981/500000000000),(-4587273504653/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(148446384089/100000000000),(1615943951777/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-383468547643/1000000000000),(7814724329/20000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-19792932474909/1000000000000),(-9628944414327/500000000000),by norm_num⟩,⟨(-332667940451/125000000000),(-45072629417/20000000000),by norm_num⟩],![⟨(1015382455427/1000000000000),(1098213740093/1000000000000),by norm_num⟩,⟨(59292815211/200000000000),(10362267049/31250000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-2228043942619/500000000000),(-2177416677019/500000000000),by norm_num⟩,⟨(24585785594953/1000000000000),(24781730725173/1000000000000),by norm_num⟩],![⟨(256866381173/500000000000),(585843550783/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(3806891029303/250000000000),(9345718136423/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-50262512410691/1000000000000),(-49103418783111/1000000000000),by norm_num⟩,⟨(-25982403655589/500000000000),(-6297285265081/125000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-157379130123/1000000000000),(-19447307693/250000000000),by norm_num⟩,⟨(-201317096957/125000000000),(-975709451499/1000000000000),by norm_num⟩,⟨(-68149303487969/1000000000000),(-32299274707569/500000000000),by norm_num⟩,⟨(-1121377292173/8000000000),(-25951267829701/200000000000),by norm_num⟩,⟨(-3413941163203/1000000000000),(-1475860911221/1000000000000),by norm_num⟩,⟨(-22444457871243/500000000000),(-42219136934077/1000000000000),by norm_num⟩,⟨(34618494153227/1000000000000),(5173442046887/125000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch015.I0
        (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch015.I0
    (coordinateBox P5.Batch015.C0.center P5.Batch015.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch015.I0 P5.Batch015.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch015
