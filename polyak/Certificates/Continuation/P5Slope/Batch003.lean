import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch003
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 3. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch003
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-1080723439/1000000000),(26862027/5000000),(2446680263/1000000000),(-20254840831/1000000000),(-1613504049/200000000),(-382329911/1000000000),(1572076969/1000000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-1503418007313/500000000000),(-1502382056009/500000000000),by norm_num⟩,⟨(2030129543/500000000000),(1146134751/200000000000),by norm_num⟩,⟨(-294501766823/200000000000),(-273864818489/200000000000),by norm_num⟩,⟨(-420025117493/1000000000000),(-412310251831/1000000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-600396013611/100000000000),(-6000821419729/1000000000000),by norm_num⟩,⟨(1487417706391/250000000000),(3727885807/625000000),by norm_num⟩,⟨(-210132799853/1000000000000),(207667097863/250000000000),by norm_num⟩,⟨(54903204321/15625000000),(711668469221/200000000000),by norm_num⟩,⟨(-2009432800001/500000000000),(-4014149199997/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-59363327233/200000000000),(-10739529317/50000000000),by norm_num⟩,⟨(-11825546606187/1000000000000),(-5880478342419/500000000000),by norm_num⟩,⟨(14103799497311/500000000000),(7675539424377/250000000000),by norm_num⟩,⟨(1661562096177/1000000000000),(901810298279/500000000000),by norm_num⟩,⟨(-6075640355433/500000000000),(-6056696899929/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-246907998009/20000000000),(-12245962122573/1000000000000),by norm_num⟩,⟨(192384572747/8000000000),(1204164731853/50000000000),by norm_num⟩,⟨(-64754653102159/1000000000000),(-14142876052601/250000000000),by norm_num⟩,⟨(56696330629/40000000000),(1799607187401/1000000000000),by norm_num⟩,⟨(-20762125017689/1000000000000),(-10285091768881/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(249812027173/1000000000000),(21288045993/62500000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1153655709/3906250000),(76229169389/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-522751237241/31250000000),(-8050198710429/500000000000),by norm_num⟩,⟨(-1583210896657/1000000000000),(-134142952061/125000000000),by norm_num⟩],![⟨(175185057363/1000000000000),(236891721721/1000000000000),by norm_num⟩,⟨(42931772961/1000000000000),(15103435583/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-335587935589/100000000000),(-3264441703447/1000000000000),by norm_num⟩,⟨(140550425519/6250000000),(22658844462567/1000000000000),by norm_num⟩],![⟨(12312270737/125000000000),(139971302133/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(2572413422419/250000000000),(3297267443787/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-23631659948687/500000000000),(-22938855433359/500000000000),by norm_num⟩,⟨(-11809586736983/250000000000),(-9058953579229/200000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-43902703511/200000000000),(-49149701549/500000000000),by norm_num⟩,⟨(-16597654747/31250000000),(111753584621/250000000000),by norm_num⟩,⟨(-74312897597203/1000000000000),(-17308093366967/250000000000),by norm_num⟩,⟨(-26934431591163/200000000000),(-4885663798973/40000000000),by norm_num⟩,⟨(-469706948523/100000000000),(-3033511127631/1000000000000),by norm_num⟩,⟨(-594048057131/15625000000),(-17805227028801/500000000000),by norm_num⟩,⟨(11693881922783/500000000000),(29462686817261/1000000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch003.I0
        (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch003.I0
    (coordinateBox P5.Batch003.C0.center P5.Batch003.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch003.I0 P5.Batch003.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch003
