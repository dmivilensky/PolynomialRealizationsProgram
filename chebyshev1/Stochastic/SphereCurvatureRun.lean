import chebyshev1.Stochastic.IndependentMatrixRun
import chebyshev1.Stochastic.MatrixNoiseFiltration

/-! Actual random-matrix runs averaged over an independent uniform initial direction. -/
namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
variable {Ω d : Type*} [mΩ : MeasurableSpace Ω] [Fintype d] [DecidableEq d] [Nonempty d]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
local notation "V" => EuclideanSpace ℝ d
local notation "Sph" => Metric.sphere (0 : V) 1
variable (S : TwoTerm) (H : Matrix d d ℝ) (Z : ℕ → Ω → Matrix d d ℝ)
variable (m q : ℕ → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
variable (hfuture : ∀ s, q s ≤ m (s+1)) (hfresh : ∀ s, Indep (q s) (m s) μ)
variable (hZ : ∀ s i j, StronglyMeasurable[q s] (fun ω => Z s ω i j))
variable (hZ2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ)
variable (hmean : ∀ s i j, (∫ ω, Z s ω i j ∂μ) = 0)

def sphereCurvatureRemainder (σ : ℝ) (N : ℕ) : ℝ :=
  ∫ x : Sph, S.matrixCurvatureRemainder (μ := μ) H Z σ x.val N
    ∂Stochastic.uniformSphere V

include hm hmono hfuture hfresh hZ hZ2 hmean

omit hmean in
private theorem sphere_variance_integrable (σ : ℝ) (N : ℕ) :
    Integrable (fun x : Sph => ∫ ω, ‖S.matrixCurvatureError H Z σ x.val N ω -
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp x.val) N)‖^2 ∂μ)
      (Stochastic.uniformSphere V) := by
  let M := fun ω => S.matrixCurvatureTransfer H Z σ N ω -
    S.realization.operatorTransfer N (fun _ => H)
  have hmM : Measurable M := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (S.matrixCurvatureTransfer_measurable H Z m q hm hmono hfuture hfresh hZ hZ2 σ N).eval_matrix.sub
      measurable_const
  have hL2 (i j : d) : MemLp (fun ω => M ω i j) 2 μ :=
    (S.matrixCurvatureTransfer_memLp H Z m q hm hmono hfuture hfresh hZ hZ2 σ N i j).sub
      (memLp_const _)
  have hi := (Stochastic.sphere_random_matrix_integrable M hmM hL2).integral_prod_right
  convert hi using 1
  funext x
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  simp only [M, Matrix.sub_mulVec, WithLp.toLp_sub,
    S.matrixCurvatureTransfer_apply, ← S.quadraticError_eq_transfer]

omit hm hmono hfuture hfresh hZ hmean in
private theorem sphere_gamma_integrable (N : ℕ) (hmZ : ∀ s, Measurable (Z s)) :
    Integrable (fun x : Sph => S.matrixCurvatureGamma (μ := μ) H Z x.val N)
      (Stochastic.uniformSphere V) := by
  simp_rw [S.matrixCurvatureGamma_eq_impulses H Z _ N hZ2]
  apply integrable_finsetSum
  intro s _
  exact (Stochastic.sphere_random_matrix_integrable
    (fun ω => S.curvatureImpulse H N s (Z s ω))
    (Stochastic.curvatureImpulse_measurable S H N s (Z s) (hmZ s))
    (Stochastic.curvatureImpulse_memLp S H N s (Z s) (hZ2 s))).integral_prod_right

omit [Fintype d] [DecidableEq d] [Nonempty d] [IsProbabilityMeasure μ] hmono hfresh hZ2 hmean in
private theorem sphere_matrix_measurable (s : ℕ) : Measurable (Z s) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact ((hZ s i j).mono ((hfuture s).trans (hm (s+1)))).measurable

theorem sphereCurvatureRemainder_integrable (σ : ℝ) (N : ℕ) :
    Integrable (fun x : Sph => S.matrixCurvatureRemainder (μ := μ) H Z σ x.val N)
      (Stochastic.uniformSphere V) := by
  have hv := S.sphere_variance_integrable H Z m q hm hmono hfuture hfresh hZ hZ2 σ N
  have hg := S.sphere_gamma_integrable H Z hZ2 N
    (fun s => sphere_matrix_measurable Z m q hm hfuture hZ s)
  convert hv.sub (hg.const_mul (σ^2)) using 1
  funext x
  have h := S.matrixCurvature_variance_expansion H Z m q hm hmono hfuture hfresh hZ hZ2 hmean σ x.val N
  change S.matrixCurvatureRemainder (μ := μ) H Z σ x.val N =
    (∫ ω, ‖S.matrixCurvatureError H Z σ x.val N ω -
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp x.val) N)‖^2 ∂μ) -
      σ^2 * S.matrixCurvatureGamma (μ := μ) H Z x.val N
  linarith

/-- Uniform initial directions give the displayed spectral leading term for the
actual recurrence, with its actual averaged nonnegative correction. -/
theorem sphereCurvature_variance_expansion {H : Matrix d d ℝ} (B : SpectralBasis H)
    (σ : ℝ) (N : ℕ) :
    (∫ x : Sph, ∫ ω, ‖S.matrixCurvatureError H Z σ x.val N ω -
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp x.val) N)‖^2 ∂μ
      ∂Stochastic.uniformSphere V) =
    σ^2 * S.realization.isotropicSpectralEnergy N B.eigenvalues
      (fun s i j => ∫ ω, (B.coordinates (Z s ω) i j)^2 ∂μ) +
      S.sphereCurvatureRemainder (μ := μ) H Z σ N := by
  simp_rw [S.matrixCurvature_variance_expansion H Z m q hm hmono hfuture hfresh hZ hZ2 hmean]
  rw [integral_add
    ((S.sphere_gamma_integrable H Z hZ2 N
      (fun s => sphere_matrix_measurable Z m q hm hfuture hZ s)).const_mul _)
    (S.sphereCurvatureRemainder_integrable H Z m q hm hmono hfuture hfresh hZ hZ2 hmean σ N),
    integral_const_mul, S.matrixCurvatureGamma_sphere_spectral B Z N
      (fun s => sphere_matrix_measurable Z m q hm hfuture hZ s) hZ2]
  rfl

omit [Nonempty d] [IsProbabilityMeasure μ] hm hmono hfuture hfresh hZ hmean in
theorem sphereCurvatureRemainder_nonneg (σ : ℝ) (N : ℕ) :
    0 ≤ S.sphereCurvatureRemainder (μ := μ) H Z σ N :=
  integral_nonneg (fun _ => S.matrixCurvatureRemainder_nonneg H Z σ _ N hZ2)

theorem sphereCurvatureRemainder_bound (σ : ℝ) (hσ : σ^2 ≤ 1) (N : ℕ) :
    S.sphereCurvatureRemainder (μ := μ) H Z σ N ≤ σ^4 *
      S.observationUnitRemainderBound H N (independentMatrixObservations (μ := μ) Z) := by
  have hb (x : Sph) : S.matrixCurvatureRemainder (μ := μ) H Z σ x.val N ≤ σ^4 *
      S.observationUnitRemainderBound H N (independentMatrixObservations (μ := μ) Z) := by
    have h := S.matrixCurvatureRemainder_bound H Z m q hm hmono hfuture hfresh hZ hZ2 hmean σ hσ x.val N
    have hx : ‖x.val‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using x.property
    simpa only [hx, one_pow, mul_one] using h
  have hi := integral_mono
    (S.sphereCurvatureRemainder_integrable H Z m q hm hmono hfuture hfresh hZ hZ2 hmean σ N)
    (integrable_const (σ^4*S.observationUnitRemainderBound H N
      (independentMatrixObservations (μ := μ) Z))) hb
  simpa [sphereCurvatureRemainder] using hi

theorem sphereCurvatureRemainder_isBigO (N : ℕ) :
    (fun σ => S.sphereCurvatureRemainder (μ := μ) H Z σ N) =O[𝓝 0]
      (fun σ : ℝ => σ^4) := by
  apply IsBigO.of_bound (S.observationUnitRemainderBound H N (independentMatrixObservations (μ := μ) Z))
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with σ hσ
  have habs : |σ| < 1 := by simpa [Real.dist_eq] using hσ
  have hσ2 : σ^2 ≤ 1 := by nlinarith [sq_abs σ, abs_nonneg σ]
  have h := S.sphereCurvatureRemainder_bound H Z m q hm hmono hfuture hfresh hZ hZ2 hmean σ hσ2 N
  have hn := S.sphereCurvatureRemainder_nonneg H Z hZ2 σ N
  rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ σ^4 by positivity)]
  simpa only [mul_comm] using h

end
end chebyshev1.TwoTerm

namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology
variable {Ω d : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d] [Nonempty d]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The complete isotropic curvature expansion, stated directly from independent
matrix samples. The past filtration is constructed, rather than supplied. -/
theorem sphereCurvature_of_iIndepFun (S : TwoTerm) {H : Matrix d d ℝ}
    (B : SpectralBasis H) (Z : ℕ → Ω → Matrix d d ℝ) (N : ℕ)
    (hZ : ∀ s, Measurable (Z s)) (hind : iIndepFun Z μ)
    (hL2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ)
    (hmean : ∀ s i j, (∫ ω, Z s ω i j ∂μ) = 0) :
    (∀ σ : ℝ,
      (∫ x : Metric.sphere (0 : EuclideanSpace ℝ d) 1, ∫ ω,
        ‖S.matrixCurvatureError H Z σ x.val N ω -
          WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp x.val) N)‖^2 ∂μ
          ∂Stochastic.uniformSphere (EuclideanSpace ℝ d)) =
        σ^2 * S.realization.isotropicSpectralEnergy N B.eigenvalues
          (fun s i j => ∫ ω, (B.coordinates (Z s ω) i j)^2 ∂μ) +
          S.sphereCurvatureRemainder (μ := μ) H Z σ N) ∧
      (∀ σ, 0 ≤ S.sphereCurvatureRemainder (μ := μ) H Z σ N) ∧
      ((fun σ => S.sphereCurvatureRemainder (μ := μ) H Z σ N) =O[𝓝 0]
        (fun σ : ℝ => σ^4)) := by
  refine ⟨?_, fun σ => S.sphereCurvatureRemainder_nonneg H Z hL2 σ N, ?_⟩
  · intro σ
    exact S.sphereCurvature_variance_expansion Z
      (Stochastic.matrixPastSigma Z) (Stochastic.matrixSampleSigma Z)
      (Stochastic.matrixPastSigma_le Z hZ) (Stochastic.matrixPastSigma_mono Z)
      (Stochastic.matrixSampleSigma_le_future Z) (Stochastic.matrixSampleSigma_indep_past Z hZ hind)
      (Stochastic.matrixSampleSigma_entries Z) hL2 hmean B σ N
  · exact S.sphereCurvatureRemainder_isBigO H Z
      (Stochastic.matrixPastSigma Z) (Stochastic.matrixSampleSigma Z)
      (Stochastic.matrixPastSigma_le Z hZ) (Stochastic.matrixPastSigma_mono Z)
      (Stochastic.matrixSampleSigma_le_future Z) (Stochastic.matrixSampleSigma_indep_past Z hZ hind)
      (Stochastic.matrixSampleSigma_entries Z) hL2 hmean N

end
end chebyshev1.TwoTerm
