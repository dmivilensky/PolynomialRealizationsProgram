import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch010
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 10. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch010
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-511051793/500000000),(1913121097/500000000),(485238731/250000000),(-245255427/15625000),(-7189488393/1000000000),(-202651033/500000000),(820760571/500000000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-603677930817/200000000000),(-1507868258893/500000000000),by norm_num⟩,⟨(12212708469/1000000000000),(14095922847/1000000000000),by norm_num⟩,⟨(-261205967357/200000000000),(-152771902977/125000000000),by norm_num⟩,⟨(-21310304709/50000000000),(-104953895117/250000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-601491559983/100000000000),(-3003923410279/500000000000),by norm_num⟩,⟨(5877984666937/1000000000000),(736900452399/125000000000),by norm_num⟩,⟨(-209941352209/250000000000),(-10612970421/1000000000000),by norm_num⟩,⟨(3554961248197/1000000000000),(359279823699/100000000000),by norm_num⟩,⟨(-2025940200001/500000000000),(-2023581999999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-161631990227/200000000000),(-713967880683/1000000000000),by norm_num⟩,⟨(-2285239046307/200000000000),(-11354521515593/1000000000000),by norm_num⟩,⟨(25933303063767/1000000000000),(27982423569909/1000000000000),by norm_num⟩,⟨(233951858361/125000000000),(995163899561/500000000000),by norm_num⟩,⟨(-12417734775907/1000000000000),(-6189768221447/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-13045369108877/1000000000000),(-6456350278301/500000000000),by norm_num⟩,⟨(4854210853091/200000000000),(6084973070131/250000000000),by norm_num⟩,⟨(-59931051348351/1000000000000),(-53058170696969/1000000000000),by norm_num⟩,⟨(634682720799/500000000000),(1597675713273/1000000000000),by norm_num⟩,⟨(-22132299465273/1000000000000),(-21933694192349/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(922400933239/1000000000000),(259051517709/250000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-69345218761/200000000000),(17695506769/50000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-3706997392653/200000000000),(-3593792183803/200000000000),by norm_num⟩,⟨(-2245993125923/1000000000000),(-1802052744021/1000000000000),by norm_num⟩],![⟨(63694475291/100000000000),(142099362903/200000000000),by norm_num⟩,⟨(17386681029/100000000000),(100524835721/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1995115971787/500000000000),(-778586284977/200000000000),by norm_num⟩,⟨(11842887925639/500000000000),(11936249676173/500000000000),by norm_num⟩],![⟨(16820848141/50000000000),(197520007271/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(13069617417251/1000000000000),(16290467090761/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-24522391433811/500000000000),(-2390519169073/50000000000),by norm_num⟩,⟨(-50066215451889/1000000000000),(-12089596474943/250000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-88348815261/500000000000),(-83577737597/1000000000000),by norm_num⟩,⟨(-1237309025643/1000000000000),(-123586975031/250000000000),by norm_num⟩,⟨(-7037672555899/100000000000),(-33165837405497/500000000000),by norm_num⟩,⟨(-69059267781133/500000000000),(-63503908132423/500000000000),by norm_num⟩,⟨(-3978434650199/1000000000000),(-2161013355027/1000000000000),by norm_num⟩,⟨(-2097237926861/50000000000),(-19694418227827/500000000000),by norm_num⟩,⟨(933624315181/31250000000),(36339059636311/1000000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch010.I0
        (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch010.I0
    (coordinateBox P5.Batch010.C0.center P5.Batch010.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch010.I0 P5.Batch010.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch010
