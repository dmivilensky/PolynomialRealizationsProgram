import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch011
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 11. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch011
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-202893001/200000000),(915381033/250000000),(1883594857/1000000000),(-7606606747/500000000),(-3544457781/500000000),(-101963793/250000000),(103229097/62500000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-3020003911501/1000000000000),(-3017285517203/1000000000000),by norm_num⟩,⟨(132629667/10000000000),(3791521471/250000000000),by norm_num⟩,⟨(-642799253841/500000000000),(-601934777493/500000000000),by norm_num⟩,⟨(-426890530641/1000000000000),(-210325147563/500000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6016879338793/1000000000000),(-6009362579433/1000000000000),by norm_num⟩,⟨(2934524787251/500000000000),(1471623862529/250000000000),by norm_num⟩,⟨(-915442931929/1000000000000),(-21868908567/200000000000),by norm_num⟩,⟨(3560112983327/1000000000000),(1798587917559/500000000000),by norm_num⟩,⟨(-2028298400001/500000000000),(-2025940199999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-440334311641/500000000000),(-98139854327/125000000000),by norm_num⟩,⟨(-11369938644931/1000000000000),(-45189877657/4000000000),by norm_num⟩,⟨(5127275688417/200000000000),(3454594962711/125000000000),by norm_num⟩,⟨(474445770143/250000000000),(1006891215289/500000000000),by norm_num⟩,⟨(-12455977597773/1000000000000),(-6208867387951/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-65772900097/5000000000),(-13017698745757/1000000000000),by norm_num⟩,⟨(151958822039/6250000000),(24386140910209/1000000000000),by norm_num⟩,⟨(-59357182177729/1000000000000),(-26312495008233/500000000000),by norm_num⟩,⟨(39203079691/31250000000),(78824985691/50000000000),by norm_num⟩,⟨(-22331866881271/1000000000000),(-5533074866317/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(257297368031/250000000000),(229287876009/200000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-354053302943/1000000000000),(361252250229/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-9394075014181/500000000000),(-18229026151881/1000000000000),by norm_num⟩,⟨(-2332436162161/1000000000000),(-1896349904039/1000000000000),by norm_num⟩],![⟨(709275712489/1000000000000),(49039247901/62500000000),by norm_num⟩,⟨(98173161753/500000000000),(2813118779/12500000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-4082456554077/1000000000000),(-796871126501/200000000000),by norm_num⟩,⟨(23862968063633/1000000000000),(24051644484883/1000000000000),by norm_num⟩],![⟨(74275559519/200000000000),(54076169873/125000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(6744669481473/500000000000),(837896083207/50000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-24645444141327/500000000000),(-96146564051/2000000000),by norm_num⟩,⟨(-25226085869349/500000000000),(-48771118164073/1000000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-172250758471/1000000000000),(-20542564121/250000000000),by norm_num⟩,⟨(-1319023482371/1000000000000),(-600614859951/1000000000000),by norm_num⟩,⟨(-69899717873179/1000000000000),(-65965924802379/1000000000000),by norm_num⟩,⟨(-34637777941837/250000000000),(-25519163033139/200000000000),by norm_num⟩,⟨(-1934460898657/500000000000),(-202801133019/100000000000),by norm_num⟩,⟨(-42523921855399/1000000000000),(-4993221329347/125000000000),by norm_num⟩,⟨(6163248545871/200000000000),(9334697328351/250000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch011.I0
        (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch011.I0
    (coordinateBox P5.Batch011.C0.center P5.Batch011.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch011.I0 P5.Batch011.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch011
