import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch016
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 16. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch016
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-24461891/25000000),(2977822949/1000000000),(818160223/500000000),(-3301659093/250000000),(-3324142381/500000000),(-209336841/500000000),(212865157/125000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-378495053581/125000000000),(-3024961197499/1000000000000),by norm_num⟩,⟨(4549220877/250000000000),(5043881061/250000000000),by norm_num⟩,⟨(-298240686349/250000000000),(-1120252906167/1000000000000),by norm_num⟩,⟨(-17189364263/40000000000),(-212071106703/500000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6028127858131/1000000000000),(-1504663338351/250000000000),by norm_num⟩,⟨(1457055319443/250000000000),(5846580277689/1000000000000),by norm_num⟩,⟨(-125281919553/100000000000),(-135969934889/250000000000),by norm_num⟩,⟨(3583923081719/1000000000000),(1808804831589/500000000000),by norm_num⟩,⟨(-2040089400001/500000000000),(-2037731199999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-1242001613137/1000000000000),(-1140575562173/1000000000000),by norm_num⟩,⟨(-2772831038591/250000000000),(-11015396985537/1000000000000),by norm_num⟩,⟨(24237367442791/1000000000000),(1301586705033/50000000000),by norm_num⟩,⟨(2017280647543/1000000000000),(2121413238137/1000000000000),by norm_num⟩,⟨(-3161964759993/250000000000),(-12609393773811/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-13733290576873/1000000000000),(-13576714227599/1000000000000),by norm_num⟩,⟨(6139539574157/250000000000),(2464811546567/100000000000),by norm_num⟩,⟨(-56827165035277/1000000000000),(-50696758893603/1000000000000),by norm_num⟩,⟨(599458551407/500000000000),(59729226649/40000000000),by norm_num⟩,⟨(-23344225533767/1000000000000),(-23139809061957/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(321098697429/200000000000),(348129958721/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-390862633681/1000000000000),(12442176547/31250000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-20042614971863/1000000000000),(-609775606169/31250000000),by norm_num⟩,⟨(-2739727590587/1000000000000),(-292304463129/125000000000),by norm_num⟩],![⟨(2192433371/2000000000),(1180988447131/1000000000000),by norm_num⟩,⟨(324144544821/1000000000000),(180483333849/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-4550750972033/1000000000000),(-889743297479/200000000000),by norm_num⟩,⟨(24769895843169/1000000000000),(24967545312011/1000000000000),by norm_num⟩],![⟨(549955213727/1000000000000),(312451146479/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(3919324604183/250000000000),(153528588913/8000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-50502974379451/1000000000000),(-24678319262537/500000000000),by norm_num⟩,⟨(-10467294470657/200000000000),(-10154169918321/200000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-19285256503/125000000000),(-76962750533/1000000000000),by norm_num⟩,⟨(-104731740043/62500000000),(-1058732545219/1000000000000),by norm_num⟩,⟨(-67746172632757/1000000000000),(-64278152603781/1000000000000),by norm_num⟩,⟨(-70276843109409/500000000000),(-26051055159949/200000000000),by norm_num⟩,⟨(-3295973158383/1000000000000),(-133284467881/100000000000),by norm_num⟩,⟨(-22746263259919/500000000000),(-21399593286457/500000000000),by norm_num⟩,⟨(35580184777919/1000000000000),(10603221707799/250000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch016.I0
        (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch016.I0
    (coordinateBox P5.Batch016.C0.center P5.Batch016.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch016.I0 P5.Batch016.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch016
