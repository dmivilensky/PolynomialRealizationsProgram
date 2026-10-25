import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch012
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 12. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch012
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-503491313/500000000),(3507219057/1000000000),(914564963/500000000),(-14760702989/1000000000),(-6992966441/1000000000),(-51283237/125000000),(207731267/125000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-3021610120493/1000000000000),(-3018829829727/1000000000000),by norm_num⟩,⟨(1786276701/125000000000),(16211406979/1000000000000),by norm_num⟩,⟨(-316462976133/250000000000),(-237225869473/200000000000),by norm_num⟩,⟨(-427533564551/1000000000000),(-105359013817/250000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-1504734902191/250000000000),(-1502748967983/250000000000),by norm_num⟩,⟨(1172077645673/200000000000),(183688879203/31250000000),by norm_num⟩,⟨(-98817201551/100000000000),(-203797870573/1000000000000),by norm_num⟩,⟨(3565122166547/1000000000000),(720289387113/200000000000),by norm_num⟩,⟨(-2030656600001/500000000000),(-4056596799997/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-95308285529/100000000000),(-856243921779/1000000000000),by norm_num⟩,⟨(-11313865550759/1000000000000),(-2810159962719/250000000000),by norm_num⟩,⟨(25345497656449/1000000000000),(13649966781957/500000000000),by norm_num⟩,⟨(1923142736421/1000000000000),(2036552165687/1000000000000),by norm_num⟩,⟨(-12494264908497/1000000000000),(-1556997199721/125000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-13265999043903/1000000000000),(-525000253701/40000000000),by norm_num⟩,⟨(12179035734291/500000000000),(2443452548473/100000000000),by norm_num⟩,⟨(-58807495332213/1000000000000),(-26104251091703/500000000000),by norm_num⟩,⟨(1240964406019/1000000000000),(311387175421/200000000000),by norm_num⟩,⟨(-704137468513/31250000000),(-11165933440633/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(569377231219/500000000000),(629746511877/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-361388218543/1000000000000),(184301501911/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-4760107321311/250000000000),(-18487830649253/1000000000000),by norm_num⟩,⟨(-483422633619/200000000000),(-994278939477/500000000000),by norm_num⟩],![⟨(783262793791/1000000000000),(86044284159/100000000000),by norm_num⟩,⟨(85869501/390625000),(250083573011/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-104378477913/25000000000),(-4076243395419/1000000000000),by norm_num⟩,⟨(6010397108857/250000000000),(12116079195989/500000000000),by norm_num⟩],![⟨(81317680573/200000000000),(94094382449/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(13914925019267/1000000000000),(1723167883221/100000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-49535549618907/1000000000000),(-24166902837489/500000000000),by norm_num⟩,⟨(-50834726809237/1000000000000),(-24589550334537/500000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-42029850793/250000000000),(-4044860349/50000000000),by norm_num⟩,⟨(-698478137669/500000000000),(-35074983883/50000000000),by norm_num⟩,⟨(-4339972161383/62500000000),(-13122053730991/200000000000),by norm_num⟩,⟨(-138971978378479/1000000000000),(-64081597968731/500000000000),by norm_num⟩,⟨(-3757713314149/1000000000000),(-1892981806547/1000000000000),by norm_num⟩,⟨(-43107862343179/1000000000000),(-40507205747757/1000000000000),by norm_num⟩,⟨(3176045355441/100000000000),(4792919476837/125000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch012.I0
        (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch012.I0
    (coordinateBox P5.Batch012.C0.center P5.Batch012.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch012.I0 P5.Batch012.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch012
