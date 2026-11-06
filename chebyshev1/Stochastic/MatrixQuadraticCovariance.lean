import chebyshev1.Stochastic.GeneralQuadraticCovariance
import Mathlib.MeasureTheory.SpecificCodomains.Pi

set_option backward.isDefEq.respectTransparency false

/-!
The full PSD matrix-valued quadratic covariance model. Scalar observations are
derived from the conditional outer-product identity; no common Kraus
factorization of the matrix-valued quadratic map is imposed.
-/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Elementwise
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
variable {μ : Measure Ω}

omit [DecidableEq d] in
theorem outerProduct_integrable {X : Ω → EuclideanSpace ℝ d} (hX : MemLp X 2 μ) :
    Integrable (fun ω => Matrix.vecMulVec (WithLp.ofLp (X ω)) (WithLp.ofLp (X ω))) μ := by
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  have hi : MemLp (fun ω => WithLp.ofLp (X ω) i) 2 μ :=
    hX.continuousLinearMap_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) i)
  have hj : MemLp (fun ω => WithLp.ofLp (X ω) j) 2 μ :=
    hX.continuousLinearMap_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) j)
  exact hi.integrable_mul hj

end
end chebyshev1.Stochastic

namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology Matrix.Norms.Elementwise

variable {d Ω : Type*} [Fintype d] [DecidableEq d]
variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A general PSD matrix-valued homogeneous quadratic conditional covariance. -/
structure MatrixQuadraticOracle (S : TwoTerm) (H : Matrix d d ℝ)
    (e0 : EuclideanSpace ℝ d) (eta : ℕ → Ω → EuclideanSpace ℝ d) (N : ℕ)
    (C : ℕ → QuadraticMap ℝ (EuclideanSpace ℝ d) (Matrix d d ℝ)) (q : ℝ) where
  filtration : ℕ → MeasurableSpace Ω
  le : ∀ s, filtration s ≤ mΩ
  mono : Monotone filtration
  adapted : ∀ s < N, StronglyMeasurable[filtration (s+1)] (eta s)
  squareIntegrable : ∀ s < N, MemLp (eta s) 2 μ
  centered : ∀ s < N, μ[eta s | filtration s] =ᵐ[μ] 0
  positiveSemidefinite : ∀ s < N, ∀ x, (C s x).PosSemidef
  covariance : ∀ s < N,
    μ[fun ω => Matrix.vecMulVec (WithLp.ofLp (eta s ω)) (WithLp.ofLp (eta s ω)) |
      filtration s] =ᵐ[μ]
      (fun ω => q • C s (S.stochasticError H e0 eta (fun _ _ => 0) s ω))

variable (S : TwoTerm) (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
variable (C : ℕ → QuadraticMap ℝ (EuclideanSpace ℝ d) (Matrix d d ℝ))

/-- Scalar observations of the prescribed matrix-valued covariance. -/
def matrixCovarianceObservations (s : ℕ)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    QuadraticForm ℝ (EuclideanSpace ℝ d) := Stochastic.covarianceObservation (C s) T

def matrixNoiseGamma : ℝ :=
  S.observationNoiseGamma H e0 N (matrixCovarianceObservations C)

def matrixNoiseRemainder (eta : ℕ → Ω → EuclideanSpace ℝ d) (q : ℝ) : ℝ :=
  S.observationNoiseRemainder (μ := μ) H e0 N (matrixCovarianceObservations C) eta q

namespace MatrixQuadraticOracle
variable {S H e0 N C} {eta : ℕ → Ω → EuclideanSpace ℝ d} {q : ℝ}
variable (R : MatrixQuadraticOracle (μ := μ) S H e0 eta N C q)

/-- The general matrix conditional covariance implies every scalar observation identity. -/
def toObservationOracle : QuadraticObservationOracle (μ := μ) S H e0 eta N
    (matrixCovarianceObservations C) q where
  filtration := R.filtration
  le := R.le
  mono := R.mono
  adapted := R.adapted
  squareIntegrable := R.squareIntegrable
  centered := R.centered
  nonnegative := fun s hs T x =>
    Stochastic.covarianceObservation_nonneg (C s) (R.positiveSemidefinite s hs) T x
  covariance := by
    intro s hs T
    let L : Matrix d d ℝ →L[ℝ] ℝ :=
      (Stochastic.covarianceObservationLinear T).toContinuousLinearMap
    have hint := Stochastic.outerProduct_integrable (R.squareIntegrable s hs)
    have hcomm := L.comp_condExp_comm (m := R.filtration s) hint
    change (fun ω => L (μ[fun ω => Matrix.vecMulVec
      (WithLp.ofLp (eta s ω)) (WithLp.ofLp (eta s ω)) | R.filtration s] ω)) =ᵐ[μ]
      μ[fun ω => L (Matrix.vecMulVec (WithLp.ofLp (eta s ω)) (WithLp.ofLp (eta s ω))) |
        R.filtration s] at hcomm
    have hobs : (fun ω => L (Matrix.vecMulVec (WithLp.ofLp (eta s ω))
        (WithLp.ofLp (eta s ω)))) = (fun ω => ‖T (eta s ω)‖^2) := by
      funext ω
      exact Stochastic.covarianceObservationLinear_outer T (eta s ω)
    rw [hobs] at hcomm
    filter_upwards [hcomm, R.covariance s hs] with ω hc hcov
    rw [← hc, hcov]
    change (Stochastic.covarianceObservationLinear T)
      (q • C s (S.stochasticError H e0 eta (fun _ _ => 0) s ω)) = _
    simp only [map_smul, smul_eq_mul, matrixCovarianceObservations,
      Stochastic.covarianceObservation_apply]

include R

/-- Proposition 8.1's matrix-valued quadratic model has the exact leading variance and remainder. -/
theorem variance_expansion :
    (∫ ω, ‖S.stochasticError H e0 eta (fun _ _ => 0) N ω -
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) N)‖^2 ∂μ) =
      q * S.matrixNoiseGamma H e0 N C + S.matrixNoiseRemainder (μ := μ) H e0 N C eta q := by
  exact R.toObservationOracle.variance_expansion

omit [IsProbabilityMeasure μ] in
theorem remainder_nonneg (hq : 0 ≤ q) :
    0 ≤ S.matrixNoiseRemainder (μ := μ) H e0 N C eta q :=
  R.toObservationOracle.remainder_nonneg hq

theorem remainder_bound (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    S.matrixNoiseRemainder (μ := μ) H e0 N C eta q ≤
      q^2 * S.observationRemainderBound H e0 N (matrixCovarianceObservations C) :=
  R.toObservationOracle.remainder_bound hq hq1

end MatrixQuadraticOracle

/-- At fixed method, horizon, initial error, and quadratic covariance data, the remainder is `O(σ⁴)`. -/
theorem matrixNoiseRemainder_isBigO (eta : ℝ → ℕ → Ω → EuclideanSpace ℝ d)
    (models : ∀ σ, MatrixQuadraticOracle (μ := μ) S H e0 (eta σ) N C (σ^2)) :
    (fun σ => S.matrixNoiseRemainder (μ := μ) H e0 N C (eta σ) (σ^2)) =O[𝓝 0]
      (fun σ : ℝ => σ^4) := by
  exact S.observationNoiseRemainder_isBigO H e0 N (matrixCovarianceObservations C)
    eta (fun σ => (models σ).toObservationOracle)

/-- The matrix covariance model need only hold for sufficiently small noise. -/
theorem matrixNoiseRemainder_isBigO_of_eventually
    (eta : ℝ → ℕ → Ω → EuclideanSpace ℝ d)
    (models : ∀ᶠ σ in 𝓝 (0 : ℝ),
      Nonempty (MatrixQuadraticOracle (μ := μ) S H e0 (eta σ) N C (σ^2))) :
    (fun σ => S.matrixNoiseRemainder (μ := μ) H e0 N C (eta σ) (σ^2)) =O[𝓝 0]
      (fun σ : ℝ => σ^4) := by
  apply S.observationNoiseRemainder_isBigO_of_eventually H e0 N
    (matrixCovarianceObservations C) eta
  filter_upwards [models] with σ hσ
  exact hσ.map (fun R => R.toObservationOracle)

end
end chebyshev1.TwoTerm
