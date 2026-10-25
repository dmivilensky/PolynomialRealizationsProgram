import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch009
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 9. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch009
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-128738299/125000000),(1000590691/250000000),(2001441521/1000000000),(-2026647697/125000000),(-7295118181/1000000000),(-80519083/200000000),(1631421157/1000000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-1508383514961/500000000000),(-3014182811927/1000000000000),by norm_num⟩,⟨(11137830329/1000000000000),(12999096233/1000000000000),by norm_num⟩,⟨(-663594794001/500000000000),(-1241079182799/1000000000000),by norm_num⟩,⟨(-26592364951/62500000000),(-104732221843/250000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6013049366543/1000000000000),(-3003225786109/500000000000),by norm_num⟩,⟨(5887208570419/1000000000000),(5904181714063/1000000000000),by norm_num⟩,⟨(-760954082661/1000000000000),(46353197521/500000000000),by norm_num⟩,⟨(709931161307/200000000000),(3588305722423/1000000000000),by norm_num⟩,⟨(-2023582000001/500000000000),(-4042447599997/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-735545051977/1000000000000),(-642786412681/1000000000000),by norm_num⟩,⟨(-717664992243/62500000000),(-5705902388461/500000000000),by norm_num⟩,⟨(26236554730607/1000000000000),(28337465966723/1000000000000),by norm_num⟩,⟨(1844593571043/1000000000000),(491538188629/250000000000),by norm_num⟩,⟨(-6189768221449/500000000000),(-12341382598743/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6469196838111/500000000000),(-12810048138141/1000000000000),by norm_num⟩,⟨(12115545930929/500000000000),(12147927604917/500000000000),by norm_num⟩,⟨(-30265222560263/500000000000),(-13377186711243/250000000000),by norm_num⟩,⟨(1285635256843/1000000000000),(1620553464877/1000000000000),by norm_num⟩,⟨(-10966847096177/500000000000),(-169812879011/7812500000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(818354273813/1000000000000),(464378596841/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-33940330623/100000000000),(173286698983/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-4570208281981/250000000000),(-8853750131791/500000000000),by norm_num⟩,⟨(-2157696287423/1000000000000),(-1705557100037/1000000000000),by norm_num⟩],![⟨(566248034621/1000000000000),(319013645629/500000000000),by norm_num⟩,⟨(30473603237/200000000000),(44516123841/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-974612082871/250000000000),(-1900977396759/500000000000),by norm_num⟩,⟨(23510038631171/1000000000000),(23694743823331/1000000000000),by norm_num⟩],![⟨(301704127641/1000000000000),(357760949409/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(12655689609477/1000000000000),(7914623910727/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-2439852298969/50000000000),(-23772423410897/500000000000),by norm_num⟩,⟨(-9935307672999/200000000000),(-47940478771823/1000000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-90744051237/500000000000),(-5320669347/62500000000),by norm_num⟩,⟨(-287881941629/250000000000),(-47781100739/125000000000),by norm_num⟩,⟨(-8858979059571/125000000000),(-33354059208817/500000000000),by norm_num⟩,⟨(-68836671444057/500000000000),(-25279496767573/200000000000),by norm_num⟩,⟨(-127695244053/31250000000),(-2291971362039/1000000000000),by norm_num⟩,⟨(-5171289111081/125000000000),(-19418168924149/500000000000),by norm_num⟩,⟨(2893947432271/100000000000),(1767200650317/50000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch009.I0
        (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch009.I0
    (coordinateBox P5.Batch009.C0.center P5.Batch009.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch009.I0 P5.Batch009.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch009
