import chebyshev1.Stochastic.IndependentMatrixNoise
import chebyshev1.Stochastic.ImpulseMatrix
import chebyshev1.Stochastic.SphereAveraging

/-! The actual finite two-term run driven by fresh centered L² random matrices. -/
set_option backward.isDefEq.respectTransparency false
namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped BigOperators Topology
variable {Ω d : Type*} [mΩ : MeasurableSpace Ω] [Fintype d] [DecidableEq d]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual recurrence with independently sampled Hessians `H + σ Z_s`. -/
def matrixCurvatureError (S : TwoTerm) (H : Matrix d d ℝ) (Z : ℕ → Ω → Matrix d d ℝ)
    (σ : ℝ) (e0 : EuclideanSpace ℝ d) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 (S.variableError (fun s => H + σ • Z s ω) (WithLp.ofLp e0) n)

def matrixCurvatureNoise (S : TwoTerm) (H : Matrix d d ℝ) (Z : ℕ → Ω → Matrix d d ℝ)
    (σ : ℝ) (e0 : EuclideanSpace ℝ d) (s : ℕ) (ω : Ω) : EuclideanSpace ℝ d :=
  σ • Stochastic.randomMatrixApply (Z s) (S.matrixCurvatureError H Z σ e0 s ω) ω

/-- The random terminal transfer matrix of the actual sampled-Hessian recurrence. -/
def matrixCurvatureTransfer (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (σ : ℝ) (n : ℕ) (ω : Ω) : Matrix d d ℝ :=
  S.realization.operatorTransfer n (fun s => H+σ • Z s ω)

omit mΩ in
theorem matrixCurvatureTransfer_apply (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (σ : ℝ) (n : ℕ) (ω : Ω) (x : EuclideanSpace ℝ d) :
    WithLp.toLp 2 ((S.matrixCurvatureTransfer H Z σ n ω).mulVec (WithLp.ofLp x)) =
      S.matrixCurvatureError H Z σ x n ω := by
  rw [matrixCurvatureError, S.variableError_eq_transfer]
  rfl

omit mΩ in
theorem matrixCurvatureTransfer_entry (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (σ : ℝ) (n : ℕ) (ω : Ω) (i j : d) :
    S.matrixCurvatureTransfer H Z σ n ω i j = WithLp.ofLp
      (S.matrixCurvatureError H Z σ (WithLp.toLp 2 (Pi.single j 1)) n ω) i := by
  rw [← S.matrixCurvatureTransfer_apply H Z σ n ω]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

omit mΩ [DecidableEq d] in
theorem matrixCurvatureError_eq_stochasticError (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (σ : ℝ) (e0 : EuclideanSpace ℝ d) (n : ℕ) (ω : Ω) :
    S.matrixCurvatureError H Z σ e0 n ω =
      S.stochasticError H e0 (S.matrixCurvatureNoise H Z σ e0) (fun _ _ => 0) n ω := by
  have he : ∀ n, S.perturbedError H (WithLp.ofLp e0)
      (fun s => WithLp.ofLp (S.matrixCurvatureNoise H Z σ e0 s ω)) (fun _ => 0) n =
      S.variableError (fun s => H+σ • Z s ω) (WithLp.ofLp e0) n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one =>
      simp [perturbedError, variableError, matrixCurvatureNoise, Stochastic.randomMatrixApply,
        matrixCurvatureError, Matrix.add_mulVec, Matrix.smul_mulVec]
    | more n ih0 ih1 =>
      rw [perturbedError, ih0, ih1]
      simp [variableError, matrixCurvatureNoise, Stochastic.randomMatrixApply,
        matrixCurvatureError, Matrix.add_mulVec, Matrix.smul_mulVec]
  exact congrArg (WithLp.toLp 2) (he n).symm

/-- Adaptedness and L² regularity follow from freshness and entrywise second moments. -/
theorem matrixCurvatureError_regular (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (σ : ℝ) (e0 : EuclideanSpace ℝ d)
    (m q : ℕ → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (hfuture : ∀ s, q s ≤ m (s+1)) (hfresh : ∀ s, Indep (q s) (m s) μ)
    (hZ : ∀ s i j, StronglyMeasurable[q s] (fun ω => Z s ω i j))
    (hZ2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ) (n : ℕ) :
    StronglyMeasurable[m n] (S.matrixCurvatureError H Z σ e0 n) ∧
      MemLp (S.matrixCurvatureError H Z σ e0 n) 2 μ := by
  let : MeasurableSpace Ω := mΩ
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hnoise (s : ℕ) (hs : s < n) :
        StronglyMeasurable[m (s+1)] (S.matrixCurvatureNoise H Z σ e0 s) ∧
          MemLp (S.matrixCurvatureNoise H Z σ e0 s) 2 μ := by
      constructor
      · let : MeasurableSpace Ω := m (s+1)
        exact (Stochastic.randomMatrixApply_stronglyMeasurable (Z s)
          (fun i j => (hZ s i j).mono (hfuture s)) _
          ((ih s hs).1.mono (hmono (Nat.le_succ s)))).const_smul σ
      · exact (Stochastic.randomMatrixApply_memLp (Z s) (m s) (q s) (hm s)
          ((hfuture s).trans (hm (s+1))) (hfresh s) (hZ s) (hZ2 s)
          _ (ih s hs).1 (ih s hs).2).const_smul σ
    have hexp : S.matrixCurvatureError H Z σ e0 n = fun ω =>
        WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) n) +
          ∑ s ∈ Finset.range n, (-S.gamma s) • S.forcingTailCLM H n s
            (S.matrixCurvatureNoise H Z σ e0 s ω) := by
      funext ω
      rw [S.matrixCurvatureError_eq_stochasticError, S.stochasticError_expansion]
      simp only [map_zero, add_zero]
    rw [hexp]
    constructor
    · apply stronglyMeasurable_const.add
      apply Finset.stronglyMeasurable_fun_sum
      intro s hs
      have hs' : s+1 ≤ n := by have := Finset.mem_range.mp hs; omega
      exact ((S.forcingTailCLM H n s).continuous.comp_stronglyMeasurable
        ((hnoise s (Finset.mem_range.mp hs)).1.mono (hmono hs'))).const_smul (-S.gamma s)
    · have hc : MemLp (fun _ : Ω =>
          WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) n)) 2 μ := memLp_const _
      have ht (s : ℕ) (hs : s ∈ Finset.range n) : MemLp
          (fun ω => (-S.gamma s) • S.forcingTailCLM H n s
            (S.matrixCurvatureNoise H Z σ e0 s ω)) 2 μ :=
        (((hnoise s (Finset.mem_range.mp hs)).2).continuousLinearMap_comp
          (S.forcingTailCLM H n s)).const_smul (-S.gamma s)
      exact hc.add (memLp_finsetSum _ ht)

/-- Canonical scalar observations of the random-matrix covariance, independent of `σ`. -/
def independentMatrixObservations (Z : ℕ → Ω → Matrix d d ℝ) :
    ℕ → (EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) →
      QuadraticForm ℝ (EuclideanSpace ℝ d) :=
  fun s T => Stochastic.independentMatrixObservation (μ := μ) (Z s) T

/-- The actual fresh-matrix recurrence satisfies the general quadratic covariance model. -/
def independentMatrixOracle (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (σ : ℝ) (e0 : EuclideanSpace ℝ d)
    (m q : ℕ → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (hfuture : ∀ s, q s ≤ m (s+1)) (hfresh : ∀ s, Indep (q s) (m s) μ)
    (hZ : ∀ s i j, StronglyMeasurable[q s] (fun ω => Z s ω i j))
    (hZ2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ)
    (hmean : ∀ s i j, (∫ ω, Z s ω i j ∂μ) = 0) (N : ℕ) :
    QuadraticObservationOracle (μ := μ) S H e0 (S.matrixCurvatureNoise H Z σ e0) N
      (independentMatrixObservations (μ := μ) Z) (σ^2) := by
  let : MeasurableSpace Ω := mΩ
  have hstate (s : ℕ) := S.matrixCurvatureError_regular H Z σ e0 m q hm hmono hfuture
    hfresh hZ hZ2 s
  refine {
    filtration := m
    le := hm
    mono := hmono
    adapted := ?_
    squareIntegrable := ?_
    centered := ?_
    nonnegative := ?_
    covariance := ?_ }
  · intro s _
    let : MeasurableSpace Ω := m (s+1)
    exact (Stochastic.randomMatrixApply_stronglyMeasurable (Z s)
      (fun i j => (hZ s i j).mono (hfuture s)) _
      ((hstate s).1.mono (hmono (Nat.le_succ s)))).const_smul σ
  · intro s _
    exact (Stochastic.randomMatrixApply_memLp (Z s) (m s) (q s) (hm s)
      ((hfuture s).trans (hm (s+1))) (hfresh s) (hZ s) (hZ2 s)
      _ (hstate s).1 (hstate s).2).const_smul σ
  · intro s _
    let X := fun ω => Stochastic.randomMatrixApply (Z s) (S.matrixCurvatureError H Z σ e0 s ω) ω
    have hc := (Stochastic.randomMatrixApply_conditional_moments (Z s) (m s) (q s)
      (hm s) ((hfuture s).trans (hm (s+1))) (hfresh s) (hZ s) (hZ2 s) (hmean s)
      _ (hstate s).1 (hstate s).2 (ContinuousLinearMap.id ℝ _)).1
    simp only [ContinuousLinearMap.id_apply] at hc
    have hs := condExp_smul (μ := μ) σ X (m s)
    change μ[fun ω => σ • X ω | m s] =ᵐ[μ] (fun ω => σ • μ[X | m s] ω) at hs
    change μ[fun ω => σ • X ω | m s] =ᵐ[μ] 0
    filter_upwards [hs, hc] with ω hs hc
    change μ[X | m s] ω = 0 at hc
    simpa only [hc, Pi.zero_apply, smul_zero] using hs
  · intro s _ T x
    exact Stochastic.independentMatrixObservation_nonneg (Z s) (hZ2 s) T x
  · intro s _ T
    let X := fun ω => Stochastic.randomMatrixApply (Z s) (S.matrixCurvatureError H Z σ e0 s ω) ω
    have hc := (Stochastic.randomMatrixApply_conditional_moments (Z s) (m s) (q s)
      (hm s) ((hfuture s).trans (hm (s+1))) (hfresh s) (hZ s) (hZ2 s) (hmean s)
      _ (hstate s).1 (hstate s).2 T).2
    have heq : (fun ω => ‖T (S.matrixCurvatureNoise H Z σ e0 s ω)‖^2) =
        (fun ω => σ^2 * ‖T (X ω)‖^2) := by
      funext ω
      simp only [matrixCurvatureNoise, X, map_smul, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs]
    rw [heq]
    have hs := condExp_smul (μ := μ) (σ^2) (fun ω => ‖T (X ω)‖^2) (m s)
    change μ[fun ω => σ^2 * ‖T (X ω)‖^2 | m s] =ᵐ[μ]
      (fun ω => σ^2 * μ[fun ω => ‖T (X ω)‖^2 | m s] ω) at hs
    filter_upwards [hs, hc] with ω hs hc
    rw [hs, hc]
    rw [S.matrixCurvatureError_eq_stochasticError]
    rfl

/-- Fixed-data leading curvature coefficient for the actual random-matrix run. -/
def matrixCurvatureGamma (S : TwoTerm) (H : Matrix d d ℝ) (Z : ℕ → Ω → Matrix d d ℝ)
    (e0 : EuclideanSpace ℝ d) (N : ℕ) : ℝ :=
  S.observationNoiseGamma H e0 N (independentMatrixObservations (μ := μ) Z)

def matrixCurvatureRemainder (S : TwoTerm) (H : Matrix d d ℝ) (Z : ℕ → Ω → Matrix d d ℝ)
    (σ : ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ) : ℝ :=
  S.observationNoiseRemainder (μ := μ) H e0 N (independentMatrixObservations (μ := μ) Z)
    (S.matrixCurvatureNoise H Z σ e0) (σ^2)

omit [IsProbabilityMeasure μ] in
/-- The leading coefficient is precisely the sum of expected squared first-variation impulses. -/
theorem matrixCurvatureGamma_eq_impulses (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
    (hZ2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ) :
    S.matrixCurvatureGamma (μ := μ) H Z e0 N = ∑ s ∈ Finset.range N,
      ∫ ω, ‖WithLp.toLp 2 ((S.curvatureImpulse H N s (Z s ω)).mulVec (WithLp.ofLp e0))‖^2 ∂μ := by
  unfold matrixCurvatureGamma observationNoiseGamma independentMatrixObservations
  apply Finset.sum_congr rfl
  intro s _
  rw [Stochastic.independentMatrixObservation_eq_integral (Z s) (hZ2 s), ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  dsimp only
  rw [S.curvatureImpulse_mulVec, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, neg_sq]
  rw [S.forcingTailCLM_apply]
  rfl

/-- Averaging the actual leading coefficient over independent uniform initial directions. -/
theorem matrixCurvatureGamma_sphere_spectral [Nonempty d] (S : TwoTerm)
    {H : Matrix d d ℝ} (B : SpectralBasis H) (Z : ℕ → Ω → Matrix d d ℝ) (N : ℕ)
    (hmZ : ∀ s, Measurable (Z s)) (hZ2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ) :
    (∫ x : Metric.sphere (0 : EuclideanSpace ℝ d) 1,
      S.matrixCurvatureGamma (μ := μ) H Z x.val N
        ∂Stochastic.uniformSphere (EuclideanSpace ℝ d)) =
      S.realization.isotropicSpectralEnergy N B.eigenvalues
        (fun s i j => ∫ ω, (B.coordinates (Z s ω) i j)^2 ∂μ) := by
  simp_rw [S.matrixCurvatureGamma_eq_impulses H Z _ N hZ2]
  exact Stochastic.sphere_curvature_impulse_energy_spectral S N B Z hmZ hZ2

omit [IsProbabilityMeasure μ] in
theorem matrixCurvatureRemainder_nonneg (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (σ : ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
    (hZ2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ) :
    0 ≤ S.matrixCurvatureRemainder (μ := μ) H Z σ e0 N := by
  apply mul_nonneg (sq_nonneg σ)
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg (sq_nonneg _)
  exact integral_nonneg (fun _ => Stochastic.independentMatrixObservation_nonneg
    (Z s) (hZ2 s) _ _)

section FixedMatrixModel
variable (S : TwoTerm) (H : Matrix d d ℝ) (Z : ℕ → Ω → Matrix d d ℝ)
variable (m q : ℕ → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
variable (hfuture : ∀ s, q s ≤ m (s+1)) (hfresh : ∀ s, Indep (q s) (m s) μ)
variable (hZ : ∀ s i j, StronglyMeasurable[q s] (fun ω => Z s ω i j))
variable (hZ2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ)
variable (hmean : ∀ s i j, (∫ ω, Z s ω i j ∂μ) = 0)
include hm hmono hfuture hfresh hZ hZ2 hmean

omit hmean in
/-- Entrywise second moments of the actual terminal transfer, derived from basis runs. -/
theorem matrixCurvatureTransfer_memLp (σ : ℝ) (N : ℕ) (i j : d) :
    MemLp (fun ω => S.matrixCurvatureTransfer H Z σ N ω i j) 2 μ := by
  have hh := (S.matrixCurvatureError_regular H Z σ (WithLp.toLp 2 (Pi.single j 1))
    m q hm hmono hfuture hfresh hZ hZ2 N).2
  have hc := hh.continuousLinearMap_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) i)
  change MemLp (fun ω => WithLp.ofLp
    (S.matrixCurvatureError H Z σ (WithLp.toLp 2 (Pi.single j 1)) N ω) i) 2 μ at hc
  simpa only [← S.matrixCurvatureTransfer_entry] using hc

omit hmean in
/-- Measurability of the complete transfer matrix, derived from adapted basis runs. -/
theorem matrixCurvatureTransfer_measurable (σ : ℝ) (N : ℕ) :
    Measurable (S.matrixCurvatureTransfer H Z σ N) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  have hh := (S.matrixCurvatureError_regular H Z σ (WithLp.toLp 2 (Pi.single j 1))
    m q hm hmono hfuture hfresh hZ hZ2 N).1
  have hc := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) i).continuous.comp_stronglyMeasurable
    (hh.mono (hm N))
  have hp := hc.measurable
  change Measurable (fun ω => WithLp.ofLp
    (S.matrixCurvatureError H Z σ (WithLp.toLp 2 (Pi.single j 1)) N ω) i) at hp
  simpa only [← S.matrixCurvatureTransfer_entry] using hp

/-- The actual independently sampled run has precisely its first-variation variance plus a nonnegative correction. -/
theorem matrixCurvature_variance_expansion (σ : ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ) :
    (∫ ω, ‖S.matrixCurvatureError H Z σ e0 N ω -
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) N)‖^2 ∂μ) =
      σ^2 * S.matrixCurvatureGamma (μ := μ) H Z e0 N +
        S.matrixCurvatureRemainder (μ := μ) H Z σ e0 N := by
  have h := (S.independentMatrixOracle H Z σ e0 m q hm hmono hfuture hfresh hZ hZ2 hmean N).variance_expansion
  simpa only [QuadraticObservationOracle.variance, ← matrixCurvatureError_eq_stochasticError,
    matrixCurvatureGamma, matrixCurvatureRemainder] using h

/-- A remainder bound uniform over the unit sphere of initial errors. -/
theorem matrixCurvatureRemainder_bound (σ : ℝ) (hσ : σ^2 ≤ 1)
    (e0 : EuclideanSpace ℝ d) (N : ℕ) :
    S.matrixCurvatureRemainder (μ := μ) H Z σ e0 N ≤ σ^4 * ‖e0‖^2 *
      S.observationUnitRemainderBound H N (independentMatrixObservations (μ := μ) Z) := by
  have R := S.independentMatrixOracle H Z σ e0 m q hm hmono hfuture hfresh hZ hZ2 hmean N
  have h := R.remainder_bound (sq_nonneg σ) hσ
  have hk := S.observationRemainderBound_le_norm_sq H e0 N (independentMatrixObservations (μ := μ) Z)
  calc
    _ ≤ (σ^2)^2 * S.observationRemainderBound H e0 N
        (independentMatrixObservations (μ := μ) Z) := h
    _ ≤ (σ^2)^2 * (‖e0‖^2 * S.observationUnitRemainderBound H N
        (independentMatrixObservations (μ := μ) Z)) := mul_le_mul_of_nonneg_left hk (sq_nonneg _)
    _ = _ := by ring

theorem matrixCurvatureRemainder_isBigO (e0 : EuclideanSpace ℝ d) (N : ℕ) :
    (fun σ => S.matrixCurvatureRemainder (μ := μ) H Z σ e0 N) =O[𝓝 0]
      (fun σ : ℝ => σ^4) := by
  exact S.observationNoiseRemainder_isBigO H e0 N (independentMatrixObservations (μ := μ) Z)
    (fun σ => S.matrixCurvatureNoise H Z σ e0)
    (fun σ => S.independentMatrixOracle H Z σ e0 m q hm hmono hfuture hfresh hZ hZ2 hmean N)

end FixedMatrixModel

end
end chebyshev1.TwoTerm
