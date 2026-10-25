import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.Batch008
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab 8. -/
namespace polyak.Certificates.Continuation.P5.Slope.Batch008
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![(-518941079/500000000),(4190999413/1000000000),(1032655689/500000000),(-4191799543/250000000),(-3703146547/500000000),(-399722849/1000000000),(101335651/62500000)]
def radius : Fin 7 → ℚ := ![213/250,321/25,21/5,144/5,6,87/250,21/125]

def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := ![![⟨(-603027141563/200000000000),(-120504976103/40000000000),by norm_num⟩,⟨(2509143813/250000000000),(1187360713/100000000000),by norm_num⟩,⟨(-134912572201/100000000000),(-1260617190991/1000000000000),by norm_num⟩,⟨(-424703153247/1000000000000),(-417986927943/1000000000000),by norm_num⟩,⟨(499999999999/500000000000),(500000000001/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-375705103591/62500000000),(-300259005511/50000000000),by norm_num⟩,⟨(1474184450871/250000000000),(5913443972131/1000000000000),by norm_num⟩,⟨(-339403457999/500000000000),(25118818233/125000000000),by norm_num⟩,⟨(354418435623/100000000000),(1791844506833/500000000000),by norm_num⟩,⟨(-2021223800001/500000000000),(-2018865599999/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-662811119299/1000000000000),(-571569714439/1000000000000),by norm_num⟩,⟨(-2884819346741/250000000000),(-11469328605633/1000000000000),by norm_num⟩,⟨(13273218457751/500000000000),(28702475024583/1000000000000),by norm_num⟩,⟨(1816671149271/1000000000000),(485304792151/250000000000),by norm_num⟩,⟨(-3085345649687/250000000000),(-12303273243451/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(-513347351901/40000000000),(-12709781585133/1000000000000),by norm_num⟩,⟨(12096812760043/500000000000),(12127056112813/500000000000),by norm_num⟩,⟨(-3822301396331/62500000000),(-53977465131499/1000000000000),by norm_num⟩,⟨(1303383633419/1000000000000),(822614949921/500000000000),by norm_num⟩,⟨(-21736048513413/1000000000000),(-21539359882313/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩],![⟨(358507814699/500000000000),(32962298887/40000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-66416276137/200000000000),(2650300803/7812500000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-563299183633/31250000000),(-17444498937481/1000000000000),by norm_num⟩,⟨(-1033725844249/500000000000),(-803372728941/500000000000),by norm_num⟩],![⟨(248581933269/500000000000),(283598749593/500000000000),by norm_num⟩,⟨(131830929301/1000000000000),(156074767119/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-951771877821/250000000000),(-1855704323717/500000000000),by norm_num⟩,⟨(5833946498369/250000000000),(4703680148951/200000000000),by norm_num⟩],![⟨(16702327743/62500000000),(2506006983/7812500000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(2449496722183/200000000000),(15374196335363/1000000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-1/500000000000),(1/500000000000),by norm_num⟩,⟨(-24273736168469/500000000000),(-47276383042811/1000000000000),by norm_num⟩,⟨(-24641396036073/500000000000),(-11879232820337/250000000000),by norm_num⟩]]

def parameterBox : Fin 7 → IntervalRat := ![⟨(-186653600163/1000000000000),(-1356897469/15625000000),by norm_num⟩,⟨(-1061364620989/1000000000000),(-32976909521/125000000000),by norm_num⟩,⟨(-35693215254601/500000000000),(-67095907950817/1000000000000),by norm_num⟩,⟨(-137214529138519/1000000000000),(-125762906674533/1000000000000),by norm_num⟩,⟨(-1048089053081/250000000000),(-302608289497/125000000000),by norm_num⟩,⟨(-20400261667937/500000000000),(-38288206825661/1000000000000),by norm_num⟩,⟨(28006536911647/1000000000000),(8588372481369/250000000000),by norm_num⟩]

theorem row0 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 0 j)=true) ∧
    derivativeEntryCheck (P5.system 0)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      0 {precision:=-80} (parameterBox 0)=true := by kernel_decide

theorem row1 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 1 j)=true) ∧
    derivativeEntryCheck (P5.system 1)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      0 {precision:=-80} (parameterBox 1)=true := by kernel_decide

theorem row2 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 2 j)=true) ∧
    derivativeEntryCheck (P5.system 2)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      0 {precision:=-80} (parameterBox 2)=true := by kernel_decide

theorem row3 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 3 j)=true) ∧
    derivativeEntryCheck (P5.system 3)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      0 {precision:=-80} (parameterBox 3)=true := by kernel_decide

theorem row4 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 4 j)=true) ∧
    derivativeEntryCheck (P5.system 4)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      0 {precision:=-80} (parameterBox 4)=true := by kernel_decide

theorem row5 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 5 j)=true) ∧
    derivativeEntryCheck (P5.system 5)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      0 {precision:=-80} (parameterBox 5)=true := by kernel_decide

theorem row6 :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      j.succ.val {precision:=-80} (jacobianBox 6 j)=true) ∧
    derivativeEntryCheck (P5.system 6)
      (LeanCert.Engine.finBoxEnv (box P5.Batch008.I0
        (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)))
      0 {precision:=-80} (parameterBox 6)=true := by kernel_decide

theorem derivatives : derivativeEnclosureCheck P5.system P5.Batch008.I0
    (coordinateBox P5.Batch008.C0.center P5.Batch008.C0.radius)
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

theorem accepted : sourceSlopeCheck P5.Batch008.I0 P5.Batch008.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.Batch008
