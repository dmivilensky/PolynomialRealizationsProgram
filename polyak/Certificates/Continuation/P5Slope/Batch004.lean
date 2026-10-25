import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch004
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 4. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch004
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-1071719843/1000000000),(2549265781/500000000),(295108129/125000000),(-9721509513/500000000),(-123729129/15625000),(-386273517/1000000000),(158178183/100000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-1504258156621/500000000000),(-3006344847509/1000000000000),by norm_num⟩,⟨(2663184173/500000000000),(1407494049/200000000000),by norm_num⟩,⟨(-361444216943/250000000000),(-672974419143/500000000000),by norm_num⟩,⟨(-421079692829/1000000000000),(-413589556959/1000000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6005218165577/1000000000000),(-6001410792319/1000000000000),by norm_num⟩,⟨(2969150465337/500000000000),(2976834344927/500000000000),by norm_num⟩,⟨(-39070136911/125000000000),(13825748593/20000000000),by norm_num⟩,⟨(1760171597789/500000000000),(1781878989107/500000000000),by norm_num⟩,⟨(-2011791000001/500000000000),(-2009432799999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-370384748397/1000000000000),(-143127506019/500000000000),by norm_num⟩,⟨(-11767862243239/1000000000000),(-11702052196677/1000000000000),by norm_num⟩,⟨(13929580066347/500000000000),(30276151784819/1000000000000),by norm_num⟩,⟨(1694863527461/1000000000000),(1833030130319/1000000000000),by norm_num⟩,⟨(-6094606055363/500000000000),(-12151280710861/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-12438213475001/1000000000000),(-6166766410243/500000000000),by norm_num⟩,⟨(481422621757/20000000000),(24112022850217/1000000000000),by norm_num⟩,⟨(-3198313756657/50000000000),(-28006461947461/500000000000),by norm_num⟩,⟨(278179828283/200000000000),(1764165071199/1000000000000),by norm_num⟩,⟨(-10477505429667/500000000000),(-5190531254421/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(84522722459/250000000000),(432067992271/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-2364994791/7812500000),(155765187661/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-8495437332991/500000000000),(-654949687993/40000000000),by norm_num⟩,⟨(-1684865278219/1000000000000),(-592825455323/500000000000),by norm_num⟩],![⟨(118262687573/500000000000),(74961129111/250000000000),by norm_num⟩,⟨(29466186497/500000000000),(19425036961/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-3445455085519/1000000000000),(-3353140608501/1000000000000),by norm_num⟩,⟨(22654330259587/1000000000000),(5706923533181/250000000000),by norm_num⟩],![⟨(131777323209/1000000000000),(175591644517/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(10670386330851/1000000000000),(13614306887647/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-47525950343257/1000000000000),(-46166342089741/1000000000000),by norm_num⟩,⟨(-47658936988859/1000000000000),(-1429853473269/31250000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-211842787191/1000000000000),(-95559891089/1000000000000),by norm_num⟩,⟨(-64929683981/100000000000),(286608154579/1000000000000),by norm_num⟩,⟨(-18418393324201/250000000000),(-68775766865479/1000000000000),by norm_num⟩,⟨(-16902337072239/125000000000),(-122935284212399/1000000000000),by norm_num⟩,⟨(-1149900379473/250000000000),(-2915328761499/1000000000000),by norm_num⟩,⟨(-19283302148333/500000000000),(-7227577232967/200000000000),by norm_num⟩,⟨(1215309110681/50000000000),(30433217489447/1000000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch004.I0
        (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch004.I0
    (coordinateBox P5.Batch004.C0.center P5.Batch004.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch004.I0 P5.Batch004.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch004
