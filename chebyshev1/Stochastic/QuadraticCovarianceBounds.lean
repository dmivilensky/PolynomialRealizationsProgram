import chebyshev1.Stochastic.QuadraticCovariance
import chebyshev1.Stochastic.VolterraBound
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Uniform finite-horizon bounds for the nonnegative quadratic covariance remainder. -/
namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology

variable {d Ω k : Type*} [Fintype d] [DecidableEq d] [Fintype k]
variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Causal, square-integrable oracle noise with a quadratic conditional covariance. -/
structure QuadraticOracle (S : TwoTerm) (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d)
    (eta : ℕ → Ω → EuclideanSpace ℝ d) (N : ℕ)
    (C : ℕ → k → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) (q : ℝ) where
  filtration : ℕ → MeasurableSpace Ω
  le : ∀ s, filtration s ≤ mΩ
  mono : Monotone filtration
  adapted : ∀ s < N, StronglyMeasurable[filtration (s+1)] (eta s)
  squareIntegrable : ∀ s < N, MemLp (eta s) 2 μ
  centered : ∀ s < N, μ[eta s | filtration s] =ᵐ[μ] 0
  covariance : ∀ s < N, ∀ T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d,
    μ[fun ω => ‖T (eta s ω)‖^2 | filtration s] =ᵐ[μ]
      (fun ω => q * ∑ j, ‖T (C s j (S.stochasticError H e0 eta (fun _ _ => 0) s ω))‖^2)

variable (S : TwoTerm) (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
variable (C : ℕ → k → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)

/-- A deterministic bound on the squared means at every prefix of the fixed method. -/
def covarianceMeanBound : ℝ :=
  ∑ t ∈ Finset.range (N+1), ‖WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) t)‖^2

/-- A deterministic bound on all finite-horizon covariance observation coefficients. -/
def covarianceOperatorBound : ℝ :=
  ∑ t ∈ Finset.range (N+1), ∑ s ∈ Finset.range t, (S.gamma s)^2 *
    ∑ j, ‖(S.forcingTailCLM H t s).comp (C s j)‖^2

theorem covarianceMeanBound_nonneg : 0 ≤ S.covarianceMeanBound H e0 N :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem covarianceOperatorBound_nonneg : 0 ≤ S.covarianceOperatorBound H N C := by
  apply Finset.sum_nonneg
  intro t _
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- A finite deterministic constant for the fourth-order covariance remainder. -/
def covarianceRemainderBound : ℝ :=
  (S.covarianceOperatorBound H N C)^2 * (N:ℝ)^2 * S.covarianceMeanBound H e0 N *
    (1 + S.covarianceOperatorBound H N C)^N

theorem covarianceRemainderBound_nonneg : 0 ≤ S.covarianceRemainderBound H e0 N C := by
  have hM := S.covarianceMeanBound_nonneg H e0 N
  have hA := S.covarianceOperatorBound_nonneg H N C
  unfold covarianceRemainderBound
  positivity

theorem le_covarianceMeanBound {t : ℕ} (ht : t ≤ N) :
    ‖WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) t)‖^2 ≤
      S.covarianceMeanBound H e0 N := by
  unfold covarianceMeanBound
  exact Finset.single_le_sum (fun s _ =>
    sq_nonneg ‖WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s)‖)
    (show t ∈ Finset.range (N+1) from Finset.mem_range.mpr (by omega))

theorem le_covarianceOperatorBound {t s : ℕ} (ht : t ≤ N) (hs : s < t) :
    (S.gamma s)^2 * ∑ j, ‖(S.forcingTailCLM H t s).comp (C s j)‖^2 ≤
      S.covarianceOperatorBound H N C := by
  have hnonneg : ∀ t s, 0 ≤ (S.gamma s)^2 *
      ∑ j, ‖(S.forcingTailCLM H t s).comp (C s j)‖^2 := by
    intro t s
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact (Finset.single_le_sum (fun s _ => hnonneg t s) (Finset.mem_range.mpr hs)).trans
    (Finset.single_le_sum (fun t _ => Finset.sum_nonneg (fun s _ => hnonneg t s))
      (Finset.mem_range.mpr (by omega)))

namespace QuadraticOracle

variable {S H e0 N C} {eta : ℕ → Ω → EuclideanSpace ℝ d} {q : ℝ}
variable (R : QuadraticOracle (μ := μ) S H e0 eta N C q)

def restrictHorizon (t : ℕ) (ht : t ≤ N) : QuadraticOracle (μ := μ) S H e0 eta t C q where
  filtration := R.filtration
  le := R.le
  mono := R.mono
  adapted := fun s hs => R.adapted s (by omega)
  squareIntegrable := fun s hs => R.squareIntegrable s (by omega)
  centered := fun s hs => R.centered s (by omega)
  covariance := fun s hs => R.covariance s (by omega)

def secondMoment (_R : QuadraticOracle (μ := μ) S H e0 eta N C q) (t : ℕ) : ℝ :=
  ∫ ω, ‖S.stochasticError H e0 eta (fun _ _ => 0) t ω‖^2 ∂μ

def variance (_R : QuadraticOracle (μ := μ) S H e0 eta N C q) (t : ℕ) : ℝ :=
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

theorem covariance_integral {s : ℕ} (hs : s < N)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    (∫ ω, ‖T (eta s ω)‖^2 ∂μ) =
      q * ∑ j, ∫ ω,
        ‖T (C s j (S.stochasticError H e0 eta (fun _ _ => 0) s ω))‖^2 ∂μ := by
  have hintj : ∀ j, Integrable (fun ω =>
      ‖T (C s j (S.stochasticError H e0 eta (fun _ _ => 0) s ω))‖^2) μ := by
    intro j
    exact ((R.memLp (by omega)).continuousLinearMap_comp (T.comp (C s j))).integrable_norm_pow
      (by norm_num)
  rw [← integral_condExp (R.le s), integral_congr_ae (R.covariance s hs T),
    integral_const_mul, integral_finsetSum _ (fun j _ => hintj j)]

theorem variance_le (hq : 0 ≤ q) {t : ℕ} (ht : t ≤ N) :
    R.variance t ≤ q * S.covarianceOperatorBound H N C *
      ∑ s ∈ Finset.range t, R.secondMoment s := by
  rw [R.variance_eq ht, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hs' := Finset.mem_range.mp hs
  rw [R.covariance_integral (by omega)]
  have hob : ∀ j,
      (∫ ω, ‖S.forcingTailCLM H t s
        (C s j (S.stochasticError H e0 eta (fun _ _ => 0) s ω))‖^2 ∂μ) ≤
      ‖(S.forcingTailCLM H t s).comp (C s j)‖^2 * R.secondMoment s := by
    intro j
    exact Stochastic.quadratic_observation_bound (R.memLp (by omega))
      ((S.forcingTailCLM H t s).comp (C s j))
  calc
    _ ≤ (S.gamma s)^2 * (q * ∑ j,
        ‖(S.forcingTailCLM H t s).comp (C s j)‖^2 * R.secondMoment s) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hob j)) hq) (sq_nonneg _)
    _ = q * ((S.gamma s)^2 * ∑ j,
        ‖(S.forcingTailCLM H t s).comp (C s j)‖^2) * R.secondMoment s := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (S.le_covarianceOperatorBound H N C ht hs') hq)
      (integral_nonneg (fun _ => sq_nonneg _))

theorem moment_recurrence (hq : 0 ≤ q) {t : ℕ} (ht : t ≤ N) :
    R.secondMoment t ≤ S.covarianceMeanBound H e0 N +
      q * S.covarianceOperatorBound H N C * ∑ s ∈ Finset.range t, R.secondMoment s := by
  rw [R.secondMoment_decomposition ht]
  exact add_le_add (S.le_covarianceMeanBound H e0 N ht) (R.variance_le hq ht)

theorem secondMoment_bound (hq : 0 ≤ q) (hq1 : q ≤ 1) {t : ℕ} (ht : t ≤ N) :
    R.secondMoment t ≤ S.covarianceMeanBound H e0 N *
      (1 + S.covarianceOperatorBound H N C)^t := by
  exact Stochastic.discrete_volterra_uniform (S.covarianceOperatorBound_nonneg H N C)
    hq1 (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun _ ht => R.moment_recurrence hq ht) t ht

theorem variance_uniform_bound (hq : 0 ≤ q) (hq1 : q ≤ 1) {t : ℕ} (ht : t ≤ N) :
    R.variance t ≤ q * S.covarianceOperatorBound H N C * (N:ℝ) *
      S.covarianceMeanBound H e0 N * (1 + S.covarianceOperatorBound H N C)^N := by
  have hsum := Stochastic.discrete_volterra_sum_bound
    (S.covarianceMeanBound_nonneg H e0 N) (S.covarianceOperatorBound_nonneg H N C)
    hq1 (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun _ ht => R.moment_recurrence hq ht)
  calc
    R.variance t ≤ q*S.covarianceOperatorBound H N C * ∑ s ∈ Finset.range t,
        R.secondMoment s := R.variance_le hq ht
    _ ≤ q*S.covarianceOperatorBound H N C * ∑ s ∈ Finset.range N,
        R.secondMoment s := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hq (S.covarianceOperatorBound_nonneg H N C))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
        (fun _ _ _ => integral_nonneg (fun _ => sq_nonneg _))
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hq (S.covarianceOperatorBound_nonneg H N C))
      simpa only [mul_assoc, secondMoment] using h

/-- Uniform `q²` control of the nonnegative correction, with constants independent of the noise law. -/
theorem remainder_bound (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    S.quadraticNoiseRemainder (μ := μ) H e0 N eta C q ≤
      q^2 * S.covarianceRemainderBound H e0 N C := by
  have hob : ∀ s < N, (S.gamma s)^2 * ∑ j,
      (∫ ω, ‖S.forcingTailCLM H N s (C s j
        (S.stochasticError H e0 eta (fun _ _ => 0) s ω -
          WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s)))‖^2 ∂μ) ≤
      S.covarianceOperatorBound H N C * R.variance s := by
    intro s hs
    have hdiff : MemLp (fun ω => S.stochasticError H e0 eta (fun _ _ => 0) s ω -
        WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s)) 2 μ :=
      (R.memLp (by omega)).sub (memLp_const _)
    calc
      _ ≤ (S.gamma s)^2 * ∑ j,
          ‖(S.forcingTailCLM H N s).comp (C s j)‖^2 * R.variance s := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply Finset.sum_le_sum
        intro j _
        exact Stochastic.quadratic_observation_bound hdiff
          ((S.forcingTailCLM H N s).comp (C s j))
      _ = ((S.gamma s)^2 * ∑ j,
          ‖(S.forcingTailCLM H N s).comp (C s j)‖^2) * R.variance s := by
        rw [← Finset.sum_mul, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (S.le_covarianceOperatorBound H N C le_rfl hs)
        (integral_nonneg (fun _ => sq_nonneg _))
  calc
    _ ≤ q * ∑ s ∈ Finset.range N, S.covarianceOperatorBound H N C * R.variance s := by
      apply mul_le_mul_of_nonneg_left _ hq
      exact Finset.sum_le_sum (fun s hs => hob s (Finset.mem_range.mp hs))
    _ ≤ q * ∑ _s ∈ Finset.range N, S.covarianceOperatorBound H N C *
        (q * S.covarianceOperatorBound H N C * (N:ℝ) *
          S.covarianceMeanBound H e0 N * (1 + S.covarianceOperatorBound H N C)^N) := by
      apply mul_le_mul_of_nonneg_left _ hq
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (R.variance_uniform_bound hq hq1 (Finset.mem_range.mp hs).le)
        (S.covarianceOperatorBound_nonneg H N C)
    _ = _ := by simp [covarianceRemainderBound]; ring

end QuadraticOracle

/-- A family of quadratic noise models has a nonnegative fourth-order remainder. -/
theorem quadraticNoiseRemainder_isBigO (eta : ℝ → ℕ → Ω → EuclideanSpace ℝ d)
    (models : ∀ σ, QuadraticOracle (μ := μ) S H e0 (eta σ) N C (σ^2)) :
    (fun σ => S.quadraticNoiseRemainder (μ := μ) H e0 N (eta σ) C (σ^2)) =O[𝓝 0]
      (fun σ : ℝ => σ^4) := by
  apply IsBigO.of_bound (S.covarianceRemainderBound H e0 N C)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with σ hσ
  have habs : |σ| < 1 := by simpa [Real.dist_eq] using hσ
  have hσ2 : σ^2 ≤ 1 := by nlinarith [sq_abs σ, abs_nonneg σ]
  have h := (models σ).remainder_bound (sq_nonneg σ) hσ2
  have hn := S.quadraticNoiseRemainder_nonneg (μ := μ) H e0 N (eta σ) C (σ^2) (sq_nonneg σ)
  rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ σ^4 by positivity)]
  calc
    _ ≤ (σ^2)^2 * S.covarianceRemainderBound H e0 N C := h
    _ = _ := by ring

/-- Edge-dropout scaling `q=p/(1-p)` gives a nonnegative `O(p²)` correction from the right. -/
theorem quadraticNoiseRemainder_dropout_isBigO (eta : ℝ → ℕ → Ω → EuclideanSpace ℝ d)
    (models : ∀ p ∈ Set.Icc (0 : ℝ) (1/2),
      QuadraticOracle (μ := μ) S H e0 (eta p) N C (p/(1-p))) :
    (fun p => S.quadraticNoiseRemainder (μ := μ) H e0 N (eta p) C (p/(1-p)))
      =O[𝓝[Set.Ici 0] 0] (fun p : ℝ => p^2) := by
  apply IsBigO.of_bound (4*S.covarianceRemainderBound H e0 N C)
  have hsmall : ∀ᶠ p : ℝ in 𝓝[Set.Ici 0] 0, p ≤ 1/2 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with p hp hp1
  have hp0 : 0 ≤ p := hp
  have hden : 0 < 1-p := by linarith
  have hq : 0 ≤ p/(1-p) := div_nonneg hp0 hden.le
  have hq1 : p/(1-p) ≤ 1 := by rw [div_le_iff₀ hden]; linarith
  have hq2 : p/(1-p) ≤ 2*p := by rw [div_le_iff₀ hden]; nlinarith
  have hr := (models p ⟨hp0, hp1⟩).remainder_bound hq hq1
  have hn := S.quadraticNoiseRemainder_nonneg (μ := μ) H e0 N (eta p) C (p/(1-p)) hq
  have hsq : (p/(1-p))^2 ≤ 4*p^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hsq (S.covarianceRemainderBound_nonneg H e0 N C)
  rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg p)]
  exact hr.trans (by nlinarith)

end
end chebyshev1.TwoTerm
