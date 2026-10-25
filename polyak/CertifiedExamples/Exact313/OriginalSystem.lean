import polyak.CertifiedExamples.Exact313.LiteralJacobian
import polyak.ModeLocking.TwoLag.Extension

/-! The checked contact equations are precisely the source three-equation
 system in the original tuning coordinates. Their isolated solution lies in
 a genuine open neighbourhood in the admissible parameter domain. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag Set Filter
open scoped Topology

def tuningCoefficients (q : Tuning) : CoefficientVector :=
  ![(Chart.coefficients q).c0,(Chart.coefficients q).c1,(Chart.coefficients q).c2]

theorem tuningCoefficients_Xi (q : Tuning) (c : ℝ) : vectorXi (tuningCoefficients q) c=q.Xi c :=
  Chart.eval_coefficients q c

theorem sourceRadius_actual (q : Tuning) (x : ℝ) : sourceRadius (tuningCoefficients q) x=q.angleRadius x := by
  dsimp [sourceRadius,Tuning.angleRadius]
  rw [tuningCoefficients_Xi]

theorem rawNumerator_actual (q : Tuning) (n : ℤ) (x : ℝ) :
    rawNumerator (tuningCoefficients q) n x=rawLag q n x := by
  dsimp [rawNumerator,rawLag]
  rw [tuningCoefficients_Xi]

def firstFrequency : Frequency := ⟨u,u_interior.1.le,u_interior.2.le⟩
def sourceLeftA (q : Tuning) : ℝ := -(tuningCurve q).lag (-4) firstFrequency
def sourceLeftB (q : Tuning) : ℝ := (tuningCurve q).lag 1 firstFrequency
def sourceSymbol (q : Tuning) : ℝ→ℝ := extension q 0 4 (sourceLeftA q) (sourceLeftB q)
def sourceContactSystem (q : Tuning) : CoefficientVector :=
  ![sourceSymbol q v,deriv (sourceSymbol q) u,deriv (sourceSymbol q) v]

theorem sourceSymbol_eq (q : Tuning) {x : ℝ} (hx : x∈Ioo 0 Real.pi) :
    sourceSymbol q x=literalSymbol (tuningCoefficients q) x := by
  let ω : Frequency := ⟨x,hx.1.le,hx.2.le⟩
  change extension q 0 4 (sourceLeftA q) (sourceLeftB q) ω=_
  rw [extension_actual,Geometry.shiftedCurve_zero]
  dsimp [sourceLeftA,sourceLeftB]
  rw [lag_eq_raw,lag_eq_raw,lag_eq_raw,lag_eq_raw]
  dsimp only [literalSymbol]
  simp only [sourceRadius_actual,rawNumerator_actual]
  dsimp only [firstFrequency,ω]
  ring

theorem sourceSymbol_eventually_eq (q : Tuning) {x : ℝ} (hx : x∈Ioo 0 Real.pi) :
    sourceSymbol q =ᶠ[𝓝 x] literalSymbol (tuningCoefficients q) := by
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact sourceSymbol_eq q hy

theorem sourceContactSystem_eq (q : Tuning) :
    sourceContactSystem q=literalContactSystem (tuningCoefficients q) := by
  ext i
  fin_cases i
  · exact sourceSymbol_eq q v_interior
  · exact (sourceSymbol_eventually_eq q u_interior).deriv_eq
  · exact (sourceSymbol_eventually_eq q v_interior).deriv_eq

theorem originalContactSystem_actual (q : Tuning) :
    originalContactSystem (ChartJacobian.originalPoint q)=sourceContactSystem q := by
  rw [sourceContactSystem_eq]
  exact congrArg literalContactSystem (ChartJacobian.coefficientMap_actual q)

theorem sourceContactSystem_zero : sourceContactSystem qStar=0 := by
  rw [←originalContactSystem_actual]
  exact originalContactSystem_zero

theorem source_jacobian_invertible :
    (fderiv ℝ originalContactSystem (ChartJacobian.originalPoint qStar)).IsInvertible :=
  originalContactSystem_jacobian_invertible

theorem continuous_tuningCoefficients : Continuous tuningCoefficients := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Chart.Coefficients.continuous_c0.comp Chart.continuous_coefficients
  · exact Chart.Coefficients.continuous_c1.comp Chart.continuous_coefficients
  · exact Chart.Coefficients.continuous_c2.comp Chart.continuous_coefficients

theorem sourceContactSystem_locally_unique : ∃U : Set Tuning,
    IsOpen U ∧ qStar∈U ∧ ∀q∈U,sourceContactSystem q=0→q=qStar := by
  obtain ⟨V,hV,hstar,hunique⟩ := contactSystem_locally_unique
  refine ⟨{q | 0<q.beta ∧ tuningCoefficients q∈V},?_,?_,?_⟩
  · exact (isOpen_lt continuous_const Tuning.continuous_beta).inter
      (hV.preimage continuous_tuningCoefficients)
  · constructor
    · exact qStar_positive_beta
    · have he : tuningCoefficients qStar=coefficientVector := by
        change ![(Chart.coefficients qStar).c0,(Chart.coefficients qStar).c1,(Chart.coefficients qStar).c2]=_
        rw [qStar_coefficients]
        rfl
      rw [he]
      exact hstar
  · intro q hq hz
    have h := hunique (tuningCoefficients q) hq.2
      ((literalContactSystem_zero_iff _).mp ((sourceContactSystem_eq q).symm.trans hz))
    apply Chart.coefficients_injective hq.1 qStar_positive_beta
    rw [qStar_coefficients]
    apply Chart.Coefficients.ext
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2

end polyak.CertifiedExamples.Exact313
