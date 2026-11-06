import chebyshev1.Stochastic.PerturbedRun

/-!
Quadratic conditional covariance: the leading variance evaluates covariance on
the deterministic run; the remaining term is an explicit sum of squares.
-/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace

variable {Ω E F : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The exact second moment decomposition, after any fixed linear observation. -/
theorem quadratic_mean_decomposition {X : Ω → E} (hX : MemLp X 2 μ)
    (a : E) (hmean : (∫ ω, X ω ∂μ) = a) (T : E →L[ℝ] F) :
    (∫ ω, ‖T (X ω)‖ ^ 2 ∂μ) = ‖T a‖^2 +
      (∫ ω, ‖T (X ω - a)‖ ^ 2 ∂μ) := by
  have hTX := hX.continuousLinearMap_comp T
  have hiX : Integrable X μ := hX.integrable (by norm_num)
  have hiTX : Integrable (fun ω => T (X ω)) μ := hTX.integrable (by norm_num)
  have hi2 : Integrable (fun ω => ‖T (X ω)‖^2) μ := hTX.integrable_norm_pow (by norm_num)
  have hiinner : Integrable (fun ω => ⟪T (X ω), T a⟫) μ := hiTX.inner_const _
  have hcross : (∫ ω, ⟪T (X ω), T a⟫ ∂μ) = ‖T a‖^2 := by
    have h := integral_inner (𝕜 := ℝ) hiTX (T a)
    rw [T.integral_comp_comm hiX, hmean] at h
    simpa only [real_inner_comm, real_inner_self_eq_norm_sq] using h
  simp_rw [map_sub, norm_sub_sq_real]
  have hfirst : Integrable (fun ω => ‖T (X ω)‖^2 - 2*⟪T (X ω), T a⟫) μ :=
    hi2.sub (hiinner.const_mul 2)
  rw [integral_add hfirst (integrable_const _),
    integral_sub hi2 (hiinner.const_mul 2), integral_const_mul, hcross]
  simp only [integral_const, probReal_univ, one_smul]
  ring

omit [CompleteSpace E] [CompleteSpace F] [IsProbabilityMeasure μ] in
/-- A coarse bound used in finite-horizon covariance control. -/
theorem quadratic_observation_bound {X : Ω → E} (hX : MemLp X 2 μ)
    (T : E →L[ℝ] F) :
    (∫ ω, ‖T (X ω)‖ ^ 2 ∂μ) ≤ ‖T‖^2 * (∫ ω, ‖X ω‖^2 ∂μ) := by
  rw [← integral_const_mul]
  apply integral_mono
  · exact (hX.continuousLinearMap_comp T).integrable_norm_pow (by norm_num)
  · exact (hX.integrable_norm_pow (by norm_num)).const_mul _
  · intro ω
    calc
      ‖T (X ω)‖^2 ≤ (‖T‖*‖X ω‖)^2 := by gcongr; exact T.le_opNorm _
      _ = ‖T‖^2 * ‖X ω‖^2 := mul_pow _ _ _

end
end chebyshev1.Stochastic

namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
variable (S : TwoTerm) {d Ω k : Type*} [Fintype d] [DecidableEq d] [Fintype k]
variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem stochasticError_memLp (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d)
    (eta xi : ℕ → Ω → EuclideanSpace ℝ d) (t : ℕ)
    (heta2 : ∀ s < t, MemLp (eta s) 2 μ) (hxi2 : ∀ s < t, MemLp (xi s) 2 μ) :
    MemLp (S.stochasticError H e0 eta xi t) 2 μ := by
  classical
  change MemLp (fun ω => S.stochasticError H e0 eta xi t ω) 2 μ
  simp_rw [S.stochasticError_expansion]
  have hconst : MemLp (fun _ : Ω =>
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) t)) 2 μ := memLp_const _
  apply MemLp.add hconst
  apply memLp_finsetSum
  intro s hs
  have hs' := Finset.mem_range.mp hs
  exact ((heta2 s hs').continuousLinearMap_comp
    ((-S.gamma s) • S.forcingTailCLM H t s)).add
    ((hxi2 s hs').continuousLinearMap_comp (S.forcingTailCLM H t s))

/-- Leading covariance evaluated along the deterministic quadratic trajectory. -/
def quadraticNoiseGamma (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
    (C : ℕ → k → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) : ℝ :=
  ∑ s ∈ Finset.range N, (S.gamma s)^2 * ∑ j,
    ‖S.forcingTailCLM H N s
      (C s j (WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s)))‖^2

/-- The exact covariance correction is a nonnegative quadratic form of the centered iterates. -/
def quadraticNoiseRemainder (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
    (eta : ℕ → Ω → EuclideanSpace ℝ d)
    (C : ℕ → k → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) (q : ℝ) : ℝ :=
  q * ∑ s ∈ Finset.range N, (S.gamma s)^2 * ∑ j,
    ∫ ω, ‖S.forcingTailCLM H N s (C s j
      (S.stochasticError H e0 eta (fun _ _ => 0) s ω -
        WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s)))‖^2 ∂μ

omit [IsProbabilityMeasure μ] in
theorem quadraticNoiseRemainder_nonneg (H : Matrix d d ℝ) (e0 : EuclideanSpace ℝ d)
    (N : ℕ) (eta : ℕ → Ω → EuclideanSpace ℝ d)
    (C : ℕ → k → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ S.quadraticNoiseRemainder (μ := μ) H e0 N eta C q := by
  apply mul_nonneg hq
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg (sq_nonneg _)
  apply Finset.sum_nonneg
  intro j _
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Exact leading-plus-remainder formula under a quadratic conditional covariance model. -/
theorem stochasticError_quadratic_covariance (H : Matrix d d ℝ)
    (e0 : EuclideanSpace ℝ d) (eta : ℕ → Ω → EuclideanSpace ℝ d) (N : ℕ)
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (heta : ∀ s < N, StronglyMeasurable[m (s+1)] (eta s))
    (heta2 : ∀ s < N, MemLp (eta s) 2 μ)
    (hceta : ∀ s < N, μ[eta s | m s] =ᵐ[μ] 0)
    (C : ℕ → k → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) (q : ℝ)
    (hcov : ∀ s < N, ∀ T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d,
      μ[fun ω => ‖T (eta s ω)‖^2 | m s] =ᵐ[μ]
        (fun ω => q * ∑ j, ‖T (C s j (S.stochasticError H e0 eta (fun _ _ => 0) s ω))‖^2)) :
    (∫ ω, ‖S.stochasticError H e0 eta (fun _ _ => 0) N ω -
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) N)‖^2 ∂μ) =
      q * S.quadraticNoiseGamma H e0 N C +
        S.quadraticNoiseRemainder (μ := μ) H e0 N eta C q := by
  have hX2 : ∀ t ≤ N,
      MemLp (S.stochasticError H e0 eta (fun _ _ => 0) t) 2 μ := by
    intro t ht
    exact S.stochasticError_memLp H e0 eta (fun _ _ => 0) t
      (fun s hs => heta2 s (by omega)) (fun _ _ => by simp)
  have hmean : ∀ t ≤ N,
      (∫ ω, S.stochasticError H e0 eta (fun _ _ => 0) t ω ∂μ) =
        WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) t) := by
    intro t ht
    exact (S.stochasticError_oracle_mean_variance H e0 eta t m hm hmono
      (fun s hs => heta s (by omega)) (fun s hs => heta2 s (by omega))
      (fun s hs => hceta s (by omega))).1
  have hcovInt : ∀ s < N, ∀ T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d,
      (∫ ω, ‖T (eta s ω)‖^2 ∂μ) =
        q * ∑ j, ∫ ω,
          ‖T (C s j (S.stochasticError H e0 eta (fun _ _ => 0) s ω))‖^2 ∂μ := by
    intro s hs T
    have hintj : ∀ j, Integrable (fun ω =>
        ‖T (C s j (S.stochasticError H e0 eta (fun _ _ => 0) s ω))‖^2) μ := by
      intro j
      exact ((hX2 s (by omega)).continuousLinearMap_comp (T.comp (C s j))).integrable_norm_pow
        (by norm_num)
    rw [← integral_condExp (hm s), integral_congr_ae (hcov s hs T), integral_const_mul,
      integral_finsetSum _ (fun j _ => hintj j)]
  have hsplit : ∀ s < N, ∀ j,
      (∫ ω, ‖S.forcingTailCLM H N s
        (C s j (S.stochasticError H e0 eta (fun _ _ => 0) s ω))‖^2 ∂μ) =
      ‖S.forcingTailCLM H N s
        (C s j (WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s)))‖^2 +
      (∫ ω, ‖S.forcingTailCLM H N s (C s j
        (S.stochasticError H e0 eta (fun _ _ => 0) s ω -
          WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) s)))‖^2 ∂μ) := by
    intro s hs j
    exact Stochastic.quadratic_mean_decomposition (hX2 s (by omega)) _
      (hmean s (by omega)) ((S.forcingTailCLM H N s).comp (C s j))
  rw [(S.stochasticError_oracle_mean_variance H e0 eta N m hm hmono heta heta2 hceta).2]
  unfold quadraticNoiseGamma quadraticNoiseRemainder
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hcovInt s (Finset.mem_range.mp hs)]
  simp_rw [hsplit s (Finset.mem_range.mp hs), Finset.sum_add_distrib]
  ring

end
end chebyshev1.TwoTerm
