import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch019
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 19. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch019
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-479212171/500000000),(106199627/40000000),(756793321/500000000),(-12254984269/1000000000),(-6423008589/1000000000),(-211948853/500000000),(216749951/125000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-1516326291157/500000000000),(-605902735601/200000000000),by norm_num⟩,⟨(20946948279/1000000000000),(918272757/40000000000),by norm_num⟩,⟨(-57191338701/50000000000),(-1075512481519/1000000000000),by norm_num⟩,⟨(-210471167/488281250),(-53221913501/125000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-6035990247551/1000000000000),(-6025517536493/1000000000000),by norm_num⟩,⟨(2903198395031/500000000000),(5825173155521/1000000000000),by norm_num⟩,⟨(-89218813543/62500000000),(-765277440827/1000000000000),by norm_num⟩,⟨(1798471776013/500000000000),(1814464137157/500000000000),by norm_num⟩,⟨(-2047164000001/500000000000),(-2044805799999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-1458161897283/1000000000000),(-338435919297/250000000000),by norm_num⟩,⟨(-2731537550243/250000000000),(-2712116441887/250000000000),by norm_num⟩,⟨(23455032107863/1000000000000),(12576413327501/500000000000),by norm_num⟩,⟨(260144867879/125000000000),(435858728689/200000000000),by norm_num⟩,⟨(-6381760885793/500000000000),(-3181230759713/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-2821185204559/200000000000),(-871149812211/62500000000),by norm_num⟩,⟨(12364457042097/500000000000),(24827832521083/1000000000000),by norm_num⟩,⟨(-216971084621/3906250000),(-49709169264371/1000000000000),by norm_num⟩,⟨(294647940239/250000000000),(1458859010449/1000000000000),by norm_num⟩,⟨(-23963350231843/1000000000000),(-2969499193417/125000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(248311223813/125000000000),(1066488764717/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-206622168803/500000000000),(420536774401/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-20789294322987/1000000000000),(-10136839525699/500000000000),by norm_num⟩,⟨(-1483347723347/500000000000),(-2583280494299/1000000000000),by norm_num⟩],![⟨(1349422407759/1000000000000),(180023652667/125000000000),by norm_num⟩,⟨(51735484831/125000000000),(456001340051/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-967590827197/200000000000),(-4733591462361/1000000000000),by norm_num⟩,⟨(12665061986859/500000000000),(12766336895949/500000000000),by norm_num⟩],![⟨(330076856577/500000000000),(74392088781/100000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(17062836903633/1000000000000),(2073017430287/100000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-51220496373891/1000000000000),(-12527176498077/250000000000),by norm_num⟩,⟨(-26719687992469/500000000000),(-51930985023869/1000000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-73102351803/500000000000),(-75015479047/1000000000000),by norm_num⟩,⟨(-927837333791/500000000000),(-160809164817/125000000000),by norm_num⟩,⟨(-66606692290343/1000000000000),(-63361302030557/1000000000000),by norm_num⟩,⟨(-141650620639873/1000000000000),(-1028675157519/7812500000),by norm_num⟩,⟨(-1465977657561/500000000000),(-111493480361/125000000000),by norm_num⟩,⟨(-47333870638023/1000000000000),(-22284169306821/500000000000),by norm_num⟩,⟨(38494048319393/1000000000000),(45523000869203/1000000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch019.I0
        (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch019.I0
    (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch019.I0 P5.Batch019.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch019
