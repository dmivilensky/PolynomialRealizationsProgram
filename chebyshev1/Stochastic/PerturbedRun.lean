import chebyshev1.Perturbations.Duhamel
import chebyshev1.Stochastic.PairedNoise
import chebyshev1.Spectral.OperatorNorm

/-! Exact mean and variance for the actual two-term run with oracle and update noise. -/
namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory Filter
open scoped BigOperators

variable (S : TwoTerm) {d Ω : Type*} [Fintype d] [DecidableEq d]
variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The deterministic tail as an operator on Euclidean error coordinates. -/
def forcingTailCLM (H : Matrix d d ℝ) (t s : ℕ) :
    EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (orderedProduct
    (fun i => S.memoryStep (s+1+i) H) (t-(s+1)) 0 0)

theorem forcingTailCLM_apply (H : Matrix d d ℝ) (t s : ℕ) (v : EuclideanSpace ℝ d) :
    S.forcingTailCLM H t s v = WithLp.toLp 2 (S.forcingTail H t s (WithLp.ofLp v)) := by
  rw [S.forcingTail_eq_memoryProduct]
  rfl

/-- A perturbed run in the same Euclidean coordinates as its probabilistic hypotheses. -/
def stochasticError (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d)
    (eta xi : ℕ → Ω → EuclideanSpace ℝ d) (t : ℕ) (ω : Ω) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 (S.perturbedError H (WithLp.ofLp e0)
    (fun s => WithLp.ofLp (eta s ω)) (fun s => WithLp.ofLp (xi s ω)) t)

omit [MeasurableSpace Ω] in
theorem stochasticError_expansion (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d)
    (eta xi : ℕ → Ω → EuclideanSpace ℝ d) (t : ℕ) (ω : Ω) :
    S.stochasticError H e0 eta xi t ω =
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) t) +
        ∑ s ∈ Finset.range t,
          ((-S.gamma s) • S.forcingTailCLM H t s (eta s ω) +
            S.forcingTailCLM H t s (xi s ω)) := by
  rw [stochasticError, S.perturbedError_eq_quadratic_add_forcing]
  simp only [WithLp.toLp_add, WithLp.toLp_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [map_sub, map_smul, WithLp.toLp_sub, WithLp.toLp_smul,
    ← S.forcingTailCLM_apply, ← S.forcingTailCLM_apply]
  module

/-- Conditional centering of both input noises gives exact residual mean and exact variance. -/
theorem stochasticError_mean_variance (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d)
    (eta xi : ℕ → Ω → EuclideanSpace ℝ d) (N : ℕ)
    (m q : ℕ → MeasurableSpace Ω)
    (hm : ∀ s, m s ≤ mΩ) (hq : ∀ s, q s ≤ mΩ) (hmono : Monotone m)
    (hpast : ∀ s, m s ≤ q s) (hfuture : ∀ s, q s ≤ m (s+1))
    (heta : ∀ s < N, StronglyMeasurable[q s] (eta s))
    (hxi : ∀ s < N, StronglyMeasurable[m (s+1)] (xi s))
    (heta2 : ∀ s < N, MemLp (eta s) 2 μ) (hxi2 : ∀ s < N, MemLp (xi s) 2 μ)
    (hceta : ∀ s < N, μ[eta s | m s] =ᵐ[μ] 0)
    (hcxi : ∀ s < N, μ[xi s | q s] =ᵐ[μ] 0) :
    (∫ ω, S.stochasticError H e0 eta xi N ω ∂μ) =
        WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) N) ∧
      (∫ ω, ‖S.stochasticError H e0 eta xi N ω -
        WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) N)‖ ^ 2 ∂μ) =
        ∑ s ∈ Finset.range N,
          ((S.gamma s)^2 * (∫ ω, ‖S.forcingTailCLM H N s (eta s ω)‖ ^ 2 ∂μ) +
            (∫ ω, ‖S.forcingTailCLM H N s (xi s ω)‖ ^ 2 ∂μ)) := by
  let A : ℕ → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d :=
    fun s => (-S.gamma s) • S.forcingTailCLM H N s
  let B : ℕ → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d :=
    fun s => S.forcingTailCLM H N s
  let U : ℕ → Ω → EuclideanSpace ℝ d := fun s ω => A s (eta s ω)
  let V : ℕ → Ω → EuclideanSpace ℝ d := fun s ω => B s (xi s ω)
  have h := Stochastic.pairedNoise_mean_variance m q hm hq hmono hpast hfuture U V N
    (fun s hs => (A s).continuous.comp_stronglyMeasurable (heta s hs))
    (fun s hs => (B s).continuous.comp_stronglyMeasurable (hxi s hs))
    (fun s hs => (heta2 s hs).continuousLinearMap_comp (A s))
    (fun s hs => (hxi2 s hs).continuousLinearMap_comp (B s))
    (fun s hs => Stochastic.conditionalCenter_linearMap
      ((heta2 s hs).integrable (by norm_num)) (hceta s hs) (A s))
    (fun s hs => Stochastic.conditionalCenter_linearMap
      ((hxi2 s hs).integrable (by norm_num)) (hcxi s hs) (B s))
  have hexp : ∀ ω, S.stochasticError H e0 eta xi N ω =
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) N) +
        ∑ s ∈ Finset.range N, (U s ω + V s ω) := by
    intro ω
    exact S.stochasticError_expansion H e0 eta xi N ω
  have hintSum : Integrable (fun ω => ∑ s ∈ Finset.range N, (U s ω + V s ω)) μ := by
    apply integrable_finsetSum
    intro s hs
    exact (((heta2 s (Finset.mem_range.mp hs)).continuousLinearMap_comp (A s)).integrable
      (by norm_num)).add
      (((hxi2 s (Finset.mem_range.mp hs)).continuousLinearMap_comp (B s)).integrable
        (by norm_num))
  constructor
  · simp_rw [hexp]
    rw [integral_add (integrable_const _) hintSum]
    simp only [integral_const, probReal_univ, one_smul, h.1, add_zero]
  · simp_rw [hexp, add_sub_cancel_left]
    rw [h.2]
    apply Finset.sum_congr rfl
    intro s _
    simp only [U, V, A, B, smul_apply, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
    rw [integral_const_mul]

/-- Oracle-only specialization, with no artificial independent-update assumption. -/
theorem stochasticError_oracle_mean_variance (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d)
    (eta : ℕ → Ω → EuclideanSpace ℝ d) (N : ℕ) (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (heta : ∀ s < N, StronglyMeasurable[m (s+1)] (eta s))
    (heta2 : ∀ s < N, MemLp (eta s) 2 μ)
    (hceta : ∀ s < N, μ[eta s | m s] =ᵐ[μ] 0) :
    (∫ ω, S.stochasticError H e0 eta (fun _ _ => 0) N ω ∂μ) =
        WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) N) ∧
      (∫ ω, ‖S.stochasticError H e0 eta (fun _ _ => 0) N ω -
        WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) N)‖^2 ∂μ) =
        ∑ s ∈ Finset.range N, (S.gamma s)^2 *
          (∫ ω, ‖S.forcingTailCLM H N s (eta s ω)‖^2 ∂μ) := by
  simpa only [map_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    integral_zero, add_zero] using
    S.stochasticError_mean_variance H e0 eta (fun _ _ => 0) N m (fun s => m (s+1))
      hm (fun s => hm (s+1)) hmono (fun s => hmono (by omega)) (fun _ => le_rfl)
      heta (fun _ _ => stronglyMeasurable_const) heta2 (fun _ _ => by simp)
      hceta (fun _ _ => condExp_zero.eventuallyEq)

end
end chebyshev1.TwoTerm
