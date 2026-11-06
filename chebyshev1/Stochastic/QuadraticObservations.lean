import chebyshev1.Stochastic.QuadraticCovariance
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
Scalar quadratic observations without any common Kraus factorization.
Every finite-dimensional quadratic form is controlled by its associated
continuous bilinear form, which also gives the exact mean decomposition.
-/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Matrix

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- The associated continuous bilinear form of an arbitrary scalar quadratic form. -/
def quadraticBilin (Q : QuadraticForm ℝ E) : E →L[ℝ] E →L[ℝ] ℝ :=
  Q.associated.toContinuousBilinearMap

@[simp] theorem quadraticBilin_diag (Q : QuadraticForm ℝ E) (x : E) :
    quadraticBilin Q x x = Q x := by
  exact QuadraticMap.associated_eq_self_apply ℝ Q x

theorem quadraticForm_continuous (Q : QuadraticForm ℝ E) : Continuous Q := by
  have h : Continuous (fun x => quadraticBilin Q x x) := by fun_prop
  simpa only [quadraticBilin_diag] using h

theorem quadraticForm_norm_le (Q : QuadraticForm ℝ E) (x : E) :
    ‖Q x‖ ≤ ‖quadraticBilin Q‖ * ‖x‖^2 := by
  rw [← quadraticBilin_diag Q x]
  calc
    ‖quadraticBilin Q x x‖ ≤ ‖quadraticBilin Q x‖ * ‖x‖ :=
      (quadraticBilin Q x).le_opNorm x
    _ ≤ (‖quadraticBilin Q‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right ((quadraticBilin Q).le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

variable [MeasurableSpace Ω] {μ : Measure Ω}

theorem quadraticForm_integrable (Q : QuadraticForm ℝ E) {X : Ω → E}
    (hX : MemLp X 2 μ) : Integrable (fun ω => Q (X ω)) μ := by
  exact ((hX.integrable_norm_pow (by norm_num)).const_mul ‖quadraticBilin Q‖).mono'
    ((quadraticForm_continuous Q).comp_aestronglyMeasurable hX.aestronglyMeasurable)
    (Eventually.of_forall fun ω => quadraticForm_norm_le Q (X ω))

theorem quadraticForm_integral_le (Q : QuadraticForm ℝ E) {X : Ω → E}
    (hX : MemLp X 2 μ) :
    (∫ ω, Q (X ω) ∂μ) ≤ ‖quadraticBilin Q‖ * (∫ ω, ‖X ω‖^2 ∂μ) := by
  rw [← integral_const_mul]
  apply integral_mono (quadraticForm_integrable Q hX)
    ((hX.integrable_norm_pow (by norm_num)).const_mul _)
  intro ω
  exact (le_abs_self _).trans (quadraticForm_norm_le Q (X ω))

variable [IsProbabilityMeasure μ] [CompleteSpace E]

/-- The mean decomposition for every scalar quadratic form, without positivity or factorization. -/
theorem quadraticForm_mean_decomposition (Q : QuadraticForm ℝ E) {X : Ω → E}
    (hX : MemLp X 2 μ) (a : E) (hmean : (∫ ω, X ω ∂μ) = a) :
    (∫ ω, Q (X ω) ∂μ) = Q a + (∫ ω, Q (X ω - a) ∂μ) := by
  let B := quadraticBilin Q
  have hiX : Integrable X μ := hX.integrable (by norm_num)
  have hdiff : MemLp (fun ω => X ω-a) 2 μ := hX.sub (memLp_const a)
  have hidiff : Integrable (fun ω => X ω-a) μ := hdiff.integrable (by norm_num)
  have hdiffmean : (∫ ω, X ω-a ∂μ) = 0 := by
    rw [integral_sub hiX (integrable_const _), hmean]
    simp
  have hl : (∫ ω, B a (X ω-a) ∂μ) = 0 := by
    rw [(B a).integral_comp_comm hidiff, hdiffmean, map_zero]
  have hr : (∫ ω, B (X ω-a) a ∂μ) = 0 := by
    have h := (B.flip a).integral_comp_comm hidiff
    simpa only [ContinuousLinearMap.flip_apply, hdiffmean, map_zero] using h
  have hil : Integrable (fun ω => B a (X ω-a)) μ := (B a).integrable_comp hidiff
  have hir : Integrable (fun ω => B (X ω-a) a) μ := (B.flip a).integrable_comp hidiff
  have hiQ := quadraticForm_integrable Q hdiff
  have heq : (fun ω => Q (X ω)) =
      (fun ω => Q a + Q (X ω-a) + B a (X ω-a) + B (X ω-a) a) := by
    funext ω
    rw [← quadraticBilin_diag Q (X ω), ← quadraticBilin_diag Q a,
      ← quadraticBilin_diag Q (X ω-a)]
    dsimp [B]
    simp only [map_sub, sub_apply]
    ring
  have hiA : Integrable (fun ω => Q a + Q (X ω-a)) μ := (integrable_const _).add hiQ
  have hiB : Integrable (fun ω => Q a + Q (X ω-a) + B a (X ω-a)) μ := hiA.add hil
  rw [heq, integral_add hiB hir, integral_add hiA hil,
    integral_add (integrable_const _) hiQ, hl, hr]
  simp

end
end chebyshev1.Stochastic

namespace chebyshev1.Stochastic
noncomputable section
open scoped BigOperators Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The scalar observation `trace(T A Tᵀ)` of an arbitrary covariance matrix. -/
def covarianceObservationLinear (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    Matrix d d ℝ →ₗ[ℝ] ℝ where
  toFun A := let M := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).symm T
    Matrix.trace (M * A * Mᵀ)
  map_add' := by intro A B; simp [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' := by intro c A; simp [Matrix.trace_smul]

/-- A matrix-valued quadratic covariance gives a scalar quadratic form for every observation. -/
def covarianceObservation (C : QuadraticMap ℝ (EuclideanSpace ℝ d) (Matrix d d ℝ))
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    QuadraticForm ℝ (EuclideanSpace ℝ d) :=
  (covarianceObservationLinear T).compQuadraticMap C

@[simp] theorem covarianceObservation_apply
    (C : QuadraticMap ℝ (EuclideanSpace ℝ d) (Matrix d d ℝ))
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) (x : EuclideanSpace ℝ d) :
    covarianceObservation C T x = covarianceObservationLinear T (C x) := rfl

theorem covarianceObservation_nonneg
    (C : QuadraticMap ℝ (EuclideanSpace ℝ d) (Matrix d d ℝ))
    (hC : ∀ x, (C x).PosSemidef)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) (x : EuclideanSpace ℝ d) :
    0 ≤ covarianceObservation C T x := by
  let M := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).symm T
  have hMt : Mᴴ = Mᵀ := by ext i j; simp
  change 0 ≤ Matrix.trace (M * C x * Mᵀ)
  rw [← hMt]
  exact ((hC x).mul_mul_conjTranspose_same M).trace_nonneg

/-- The covariance observation of an outer product is its actual observed squared norm. -/
theorem covarianceObservationLinear_outer
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) (x : EuclideanSpace ℝ d) :
    covarianceObservationLinear T (Matrix.vecMulVec (WithLp.ofLp x) (WithLp.ofLp x)) =
      ‖T x‖^2 := by
  let M := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).symm T
  have hM : Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) M = T :=
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).apply_symm_apply T
  change Matrix.trace (M * Matrix.vecMulVec (WithLp.ofLp x) (WithLp.ofLp x) * Mᵀ) = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
    Matrix.trace_vecMulVec]
  rw [← hM]
  change dotProduct (M.mulVec (WithLp.ofLp x)) (M.mulVec (WithLp.ofLp x)) =
    ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp x))‖^2
  simp [dotProduct, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  simp [pow_two]

end
end chebyshev1.Stochastic
