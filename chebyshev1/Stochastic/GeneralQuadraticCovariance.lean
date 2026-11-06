import chebyshev1.Stochastic.QuadraticObservations
import chebyshev1.Stochastic.QuadraticCovarianceBounds

/-!
General quadratic conditional covariance observed through scalar quadratic forms.
The forms may depend on the observation; a common Kraus factorization is neither
assumed nor constructed.
-/
namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology

variable {d Ω : Type*} [Fintype d] [DecidableEq d]
variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- General nonnegative scalar quadratic observations of a conditional covariance. -/
structure QuadraticObservationOracle (S : TwoTerm) (H : Matrix d d ℝ)
    (e0 : EuclideanSpace ℝ d) (eta : ℕ → Ω → EuclideanSpace ℝ d) (N : ℕ)
    (Q : ℕ → (EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) →
      QuadraticForm ℝ (EuclideanSpace ℝ d)) (q : ℝ) where
  filtration : ℕ → MeasurableSpace Ω
  le : ∀ s, filtration s ≤ mΩ
  mono : Monotone filtration
  adapted : ∀ s < N, StronglyMeasurable[filtration (s+1)] (eta s)
  squareIntegrable : ∀ s < N, MemLp (eta s) 2 μ
  centered : ∀ s < N, μ[eta s | filtration s] =ᵐ[μ] 0
  nonnegative : ∀ s < N, ∀ T x, 0 ≤ Q s T x
  covariance : ∀ s < N, ∀ T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d,
    μ[fun ω => ‖T (eta s ω)‖^2 | filtration s] =ᵐ[μ]
      (fun ω => q * Q s T (S.stochasticError H e0 eta (fun _ _ => 0) s ω))

variable (S : TwoTerm) (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
variable (Q : ℕ → (EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) →
  QuadraticForm ℝ (EuclideanSpace ℝ d))

/-- Leading variance evaluated along the deterministic trajectory. -/
def observationNoiseGamma : ℝ :=
  ∑ s ∈ Finset.range N, (S.gamma s)^2 *
    Q s (S.forcingTailCLM H N s)
      (WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s))

/-- The exact correction evaluated on centered iterates. -/
def observationNoiseRemainder (eta : ℕ → Ω → EuclideanSpace ℝ d) (q : ℝ) : ℝ :=
  q * ∑ s ∈ Finset.range N, (S.gamma s)^2 * ∫ ω,
    Q s (S.forcingTailCLM H N s)
      (S.stochasticError H e0 eta (fun _ _ => 0) s ω -
        WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s)) ∂μ

/-- A finite observation bound obtained from associated bilinear operator norms. -/
def observationOperatorBound : ℝ :=
  ∑ t ∈ Finset.range (N+1), ∑ s ∈ Finset.range t,
    (S.gamma s)^2 * ‖Stochastic.quadraticBilin (Q s (S.forcingTailCLM H t s))‖

def observationRemainderBound : ℝ :=
  (S.observationOperatorBound H N Q)^2 * (N:ℝ)^2 * S.covarianceMeanBound H e0 N *
    (1 + S.observationOperatorBound H N Q)^N

/-- The fixed-Hessian prefix as a linear operator on the initial error. -/
def quadraticPrefixCLM (t : ℕ) : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (S.realization.operatorTransfer t (fun _ => H))

theorem quadraticPrefixCLM_apply (t : ℕ) (x : EuclideanSpace ℝ d) :
    S.quadraticPrefixCLM H t x =
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp x) t) := by
  rw [S.quadraticError_eq_transfer]
  rfl

/-- Initial-state-independent bound for all fixed prefix operator norms. -/
def quadraticMeanOperatorBound : ℝ :=
  ∑ t ∈ Finset.range (N+1), ‖S.quadraticPrefixCLM H t‖^2

theorem covarianceMeanBound_le_norm_sq : S.covarianceMeanBound H e0 N ≤
    ‖e0‖^2 * S.quadraticMeanOperatorBound H N := by
  unfold covarianceMeanBound quadraticMeanOperatorBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [← S.quadraticPrefixCLM_apply]
  have h := (S.quadraticPrefixCLM H t).le_opNorm e0
  nlinarith [norm_nonneg e0, norm_nonneg (S.quadraticPrefixCLM H t e0),
    (S.quadraticPrefixCLM H t).opNorm_nonneg]

/-- A uniform remainder constant for initial errors of norm at most one. -/
def observationUnitRemainderBound : ℝ :=
  (S.observationOperatorBound H N Q)^2 * (N:ℝ)^2 * S.quadraticMeanOperatorBound H N *
    (1 + S.observationOperatorBound H N Q)^N

theorem observationRemainderBound_le_norm_sq : S.observationRemainderBound H e0 N Q ≤
    ‖e0‖^2 * S.observationUnitRemainderBound H N Q := by
  have hA : 0 ≤ S.observationOperatorBound H N Q := by
    apply Finset.sum_nonneg
    intro t _
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _)
      (Stochastic.quadraticBilin (Q s (S.forcingTailCLM H t s))).opNorm_nonneg)
  have h := mul_le_mul_of_nonneg_left (S.covarianceMeanBound_le_norm_sq H e0 N)
    (mul_nonneg (sq_nonneg (S.observationOperatorBound H N Q)) (sq_nonneg (N:ℝ)))
  have h' := mul_le_mul_of_nonneg_right h (pow_nonneg (by linarith :
    0 ≤ 1+S.observationOperatorBound H N Q) N)
  unfold observationRemainderBound observationUnitRemainderBound
  nlinarith

theorem observationOperatorBound_nonneg : 0 ≤ S.observationOperatorBound H N Q := by
  apply Finset.sum_nonneg
  intro t _
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _)
    (Stochastic.quadraticBilin (Q s (S.forcingTailCLM H t s))).opNorm_nonneg)

theorem observationRemainderBound_nonneg : 0 ≤ S.observationRemainderBound H e0 N Q := by
  have hM := S.covarianceMeanBound_nonneg H e0 N
  have hA := S.observationOperatorBound_nonneg H N Q
  unfold observationRemainderBound
  positivity

theorem le_observationOperatorBound {t s : ℕ} (ht : t ≤ N) (hs : s < t) :
    (S.gamma s)^2 * ‖Stochastic.quadraticBilin (Q s (S.forcingTailCLM H t s))‖ ≤
      S.observationOperatorBound H N Q := by
  have hnonneg : ∀ t s, 0 ≤ (S.gamma s)^2 *
      ‖Stochastic.quadraticBilin (Q s (S.forcingTailCLM H t s))‖ := by
    intro t s
    exact mul_nonneg (sq_nonneg _)
      (Stochastic.quadraticBilin (Q s (S.forcingTailCLM H t s))).opNorm_nonneg
  exact (Finset.single_le_sum (fun s _ => hnonneg t s) (Finset.mem_range.mpr hs)).trans
    (Finset.single_le_sum (fun t _ => Finset.sum_nonneg (fun s _ => hnonneg t s))
      (Finset.mem_range.mpr (by omega)))

namespace QuadraticObservationOracle
variable {S H e0 N Q} {eta : ℕ → Ω → EuclideanSpace ℝ d} {q : ℝ}
variable (R : QuadraticObservationOracle (μ := μ) S H e0 eta N Q q)

def secondMoment (_R : QuadraticObservationOracle (μ := μ) S H e0 eta N Q q)
    (t : ℕ) : ℝ := ∫ ω, ‖S.stochasticError H e0 eta (fun _ _ => 0) t ω‖^2 ∂μ

def variance (_R : QuadraticObservationOracle (μ := μ) S H e0 eta N Q q) (t : ℕ) : ℝ :=
  ∫ ω, ‖S.stochasticError H e0 eta (fun _ _ => 0) t ω -
    WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) t)‖^2 ∂μ

include R

theorem memLp {t : ℕ} (ht : t ≤ N) :
    MemLp (S.stochasticError H e0 eta (fun _ _ => 0) t) 2 μ := by
  exact S.stochasticError_memLp H e0 eta (fun _ _ => 0) t
    (fun s hs => R.squareIntegrable s (by omega)) (fun _ _ => by simp)

theorem mean {t : ℕ} (ht : t ≤ N) :
    (∫ ω, S.stochasticError H e0 eta (fun _ _ => 0) t ω ∂μ) =
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) t) := by
  exact (S.stochasticError_oracle_mean_variance H e0 eta t R.filtration R.le R.mono
    (fun s hs => R.adapted s (by omega)) (fun s hs => R.squareIntegrable s (by omega))
    (fun s hs => R.centered s (by omega))).1

theorem variance_eq {t : ℕ} (ht : t ≤ N) : R.variance t =
    ∑ s ∈ Finset.range t, (S.gamma s)^2 *
      (∫ ω, ‖S.forcingTailCLM H t s (eta s ω)‖^2 ∂μ) := by
  exact (S.stochasticError_oracle_mean_variance H e0 eta t R.filtration R.le R.mono
    (fun s hs => R.adapted s (by omega)) (fun s hs => R.squareIntegrable s (by omega))
    (fun s hs => R.centered s (by omega))).2

theorem secondMoment_decomposition {t : ℕ} (ht : t ≤ N) : R.secondMoment t =
    ‖WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) t)‖^2 + R.variance t := by
  exact Stochastic.quadratic_mean_decomposition (R.memLp ht) _ (R.mean ht)
    (ContinuousLinearMap.id ℝ _)

omit [DecidableEq d] in
theorem covariance_integral {s : ℕ} (hs : s < N)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    (∫ ω, ‖T (eta s ω)‖^2 ∂μ) =
      q * ∫ ω, Q s T (S.stochasticError H e0 eta (fun _ _ => 0) s ω) ∂μ := by
  rw [← integral_condExp (R.le s), integral_congr_ae (R.covariance s hs T),
    integral_const_mul]

theorem variance_expansion : R.variance N = q * S.observationNoiseGamma H e0 N Q +
    S.observationNoiseRemainder (μ := μ) H e0 N Q eta q := by
  rw [R.variance_eq le_rfl]
  unfold observationNoiseGamma observationNoiseRemainder
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hsN := Finset.mem_range.mp hs
  rw [R.covariance_integral hsN,
    Stochastic.quadraticForm_mean_decomposition _ (R.memLp (by omega)) _ (R.mean (by omega))]
  ring

omit [IsProbabilityMeasure μ] in
theorem remainder_nonneg (hq : 0 ≤ q) :
    0 ≤ S.observationNoiseRemainder (μ := μ) H e0 N Q eta q := by
  apply mul_nonneg hq
  apply Finset.sum_nonneg
  intro s hs
  apply mul_nonneg (sq_nonneg _)
  exact integral_nonneg (fun _ => R.nonnegative s (Finset.mem_range.mp hs) _ _)

theorem variance_le (hq : 0 ≤ q) {t : ℕ} (ht : t ≤ N) :
    R.variance t ≤ q * S.observationOperatorBound H N Q *
      ∑ s ∈ Finset.range t, R.secondMoment s := by
  rw [R.variance_eq ht, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hs' := Finset.mem_range.mp hs
  rw [R.covariance_integral (by omega)]
  have hob := Stochastic.quadraticForm_integral_le
    (Q s (S.forcingTailCLM H t s)) (R.memLp (t := s) (by omega))
  calc
    _ ≤ (S.gamma s)^2 * (q * (‖Stochastic.quadraticBilin (Q s (S.forcingTailCLM H t s))‖ *
        R.secondMoment s)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hob hq) (sq_nonneg _)
    _ = q * ((S.gamma s)^2 * ‖Stochastic.quadraticBilin (Q s (S.forcingTailCLM H t s))‖) *
        R.secondMoment s := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (S.le_observationOperatorBound H N Q ht hs') hq)
      (integral_nonneg (fun _ => sq_nonneg _))

theorem moment_recurrence (hq : 0 ≤ q) {t : ℕ} (ht : t ≤ N) :
    R.secondMoment t ≤ S.covarianceMeanBound H e0 N +
      q * S.observationOperatorBound H N Q * ∑ s ∈ Finset.range t, R.secondMoment s := by
  rw [R.secondMoment_decomposition ht]
  exact add_le_add (S.le_covarianceMeanBound H e0 N ht) (R.variance_le hq ht)

theorem secondMoment_bound (hq : 0 ≤ q) (hq1 : q ≤ 1) {t : ℕ} (ht : t ≤ N) :
    R.secondMoment t ≤ S.covarianceMeanBound H e0 N *
      (1 + S.observationOperatorBound H N Q)^t := by
  exact Stochastic.discrete_volterra_uniform (S.observationOperatorBound_nonneg H N Q)
    hq1 (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun _ ht => R.moment_recurrence hq ht) t ht

theorem variance_uniform_bound (hq : 0 ≤ q) (hq1 : q ≤ 1) {t : ℕ} (ht : t ≤ N) :
    R.variance t ≤ q * S.observationOperatorBound H N Q * (N:ℝ) *
      S.covarianceMeanBound H e0 N * (1 + S.observationOperatorBound H N Q)^N := by
  have hsum := Stochastic.discrete_volterra_sum_bound
    (S.covarianceMeanBound_nonneg H e0 N) (S.observationOperatorBound_nonneg H N Q)
    hq1 (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun _ ht => R.moment_recurrence hq ht)
  calc
    R.variance t ≤ q*S.observationOperatorBound H N Q * ∑ s ∈ Finset.range t,
        R.secondMoment s := R.variance_le hq ht
    _ ≤ q*S.observationOperatorBound H N Q * ∑ s ∈ Finset.range N,
        R.secondMoment s := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hq (S.observationOperatorBound_nonneg H N Q))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
        (fun _ _ _ => integral_nonneg (fun _ => sq_nonneg _))
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hq (S.observationOperatorBound_nonneg H N Q))
      simpa only [mul_assoc, secondMoment] using h

theorem remainder_bound (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    S.observationNoiseRemainder (μ := μ) H e0 N Q eta q ≤
      q^2 * S.observationRemainderBound H e0 N Q := by
  have hob : ∀ s < N, (S.gamma s)^2 * (∫ ω,
      Q s (S.forcingTailCLM H N s)
        (S.stochasticError H e0 eta (fun _ _ => 0) s ω -
          WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s)) ∂μ) ≤
      S.observationOperatorBound H N Q * R.variance s := by
    intro s hs
    have hdiff : MemLp (fun ω => S.stochasticError H e0 eta (fun _ _ => 0) s ω -
        WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s)) 2 μ :=
      (R.memLp (by omega)).sub (memLp_const _)
    have hi := Stochastic.quadraticForm_integral_le (Q s (S.forcingTailCLM H N s)) hdiff
    have hb := mul_le_mul_of_nonneg_left hi (sq_nonneg (S.gamma s))
    have hc := mul_le_mul_of_nonneg_right
      (S.le_observationOperatorBound H N Q le_rfl hs)
      (show 0 ≤ R.variance s from integral_nonneg (fun _ => sq_nonneg _))
    exact hb.trans (by simpa only [mul_assoc, variance] using hc)
  calc
    _ ≤ q * ∑ s ∈ Finset.range N, S.observationOperatorBound H N Q * R.variance s := by
      apply mul_le_mul_of_nonneg_left _ hq
      exact Finset.sum_le_sum (fun s hs => hob s (Finset.mem_range.mp hs))
    _ ≤ q * ∑ _s ∈ Finset.range N, S.observationOperatorBound H N Q *
        (q * S.observationOperatorBound H N Q * (N:ℝ) *
          S.covarianceMeanBound H e0 N * (1 + S.observationOperatorBound H N Q)^N) := by
      apply mul_le_mul_of_nonneg_left _ hq
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (R.variance_uniform_bound hq hq1 (Finset.mem_range.mp hs).le)
        (S.observationOperatorBound_nonneg H N Q)
    _ = _ := by simp [observationRemainderBound]; ring

end QuadraticObservationOracle

/-- The general quadratic conditional covariance model has an `O(σ⁴)` correction. -/
theorem observationNoiseRemainder_isBigO (eta : ℝ → ℕ → Ω → EuclideanSpace ℝ d)
    (models : ∀ σ, QuadraticObservationOracle (μ := μ) S H e0 (eta σ) N Q (σ^2)) :
    (fun σ => S.observationNoiseRemainder (μ := μ) H e0 N Q (eta σ) (σ^2)) =O[𝓝 0]
      (fun σ : ℝ => σ^4) := by
  apply IsBigO.of_bound (S.observationRemainderBound H e0 N Q)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with σ hσ
  have habs : |σ| < 1 := by simpa [Real.dist_eq] using hσ
  have hσ2 : σ^2 ≤ 1 := by nlinarith [sq_abs σ, abs_nonneg σ]
  have h := (models σ).remainder_bound (sq_nonneg σ) hσ2
  have hn := (models σ).remainder_nonneg (sq_nonneg σ)
  rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ σ^4 by positivity)]
  calc
    _ ≤ (σ^2)^2 * S.observationRemainderBound H e0 N Q := h
    _ = _ := by ring

/-- Only a neighborhood of zero needs to satisfy the covariance model. -/
theorem observationNoiseRemainder_isBigO_of_eventually
    (eta : ℝ → ℕ → Ω → EuclideanSpace ℝ d)
    (models : ∀ᶠ σ in 𝓝 (0 : ℝ),
      Nonempty (QuadraticObservationOracle (μ := μ) S H e0 (eta σ) N Q (σ^2))) :
    (fun σ => S.observationNoiseRemainder (μ := μ) H e0 N Q (eta σ) (σ^2)) =O[𝓝 0]
      (fun σ : ℝ => σ^4) := by
  apply IsBigO.of_bound (S.observationRemainderBound H e0 N Q)
  filter_upwards [models, Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)]
    with σ hmodel hσ
  obtain ⟨R⟩ := hmodel
  have habs : |σ| < 1 := by simpa [Real.dist_eq] using hσ
  have hσ2 : σ^2 ≤ 1 := by nlinarith [sq_abs σ, abs_nonneg σ]
  have h := R.remainder_bound (sq_nonneg σ) hσ2
  have hn := R.remainder_nonneg (sq_nonneg σ)
  rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ σ^4 by positivity)]
  calc
    _ ≤ (σ^2)^2 * S.observationRemainderBound H e0 N Q := h
    _ = _ := by ring

end
end chebyshev1.TwoTerm
