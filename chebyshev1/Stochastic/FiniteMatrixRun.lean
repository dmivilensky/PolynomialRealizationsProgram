import chebyshev1.Stochastic.FiniteNoiseExtension
import chebyshev1.Stochastic.FiniteIndependentSpectral
import chebyshev1.Stochastic.SphereCurvatureRun

/-! The actual curvature-noise recurrence on its original probability space,
using only finite-horizon independence and moment hypotheses. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory
variable {Ω d : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d]
  {μ : Measure Ω}

omit [Fintype d] [DecidableEq d] in
theorem zeroAfter_matrix_memLp (N : ℕ) (Z : ℕ → Ω → Matrix d d ℝ)
    (hL2 : ∀ s<N, ∀ i j, MemLp (fun ω => Z s ω i j) 2 μ) (s : ℕ) (i j : d) :
    MemLp (fun ω => zeroAfter N Z s ω i j) 2 μ := by
  by_cases hs : s<N
  · simpa only [zeroAfter_eq N Z hs] using hL2 s hs i j
  · simp only [zeroAfter,hs,ite_false,Matrix.zero_apply]
    exact MemLp.zero

omit [Fintype d] [DecidableEq d] in
theorem zeroAfter_matrix_mean (N : ℕ) (Z : ℕ → Ω → Matrix d d ℝ)
    (hmean : ∀ s<N, ∀ i j, (∫ ω, Z s ω i j ∂μ)=0) (s : ℕ) (i j : d) :
    (∫ ω, zeroAfter N Z s ω i j ∂μ)=0 := by
  by_cases hs : s<N
  · simpa only [zeroAfter_eq N Z hs] using hmean s hs i j
  · simp only [zeroAfter,hs,ite_false,Matrix.zero_apply,integral_zero]

theorem spectralEnergy_zeroAfter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Realization ι) (N : ℕ) {H : Matrix d d ℝ} (B : SpectralBasis H)
    (Z : ℕ → Ω → Matrix d d ℝ) :
    R.isotropicSpectralEnergy N B.eigenvalues
      (fun s i j => ∫ ω, (B.coordinates (zeroAfter N Z s ω) i j)^2 ∂μ) =
        R.isotropicSpectralEnergy N B.eigenvalues
          (fun s i j => ∫ ω, (B.coordinates (Z s ω) i j)^2 ∂μ) := by
  unfold Realization.isotropicSpectralEnergy
  apply congrArg (fun x : ℝ => x/(Fintype.card d:ℝ))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s hs
  dsimp only
  rw [zeroAfter_eq N Z (Finset.mem_range.mp hs)]

end
end chebyshev1.Stochastic

namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics Stochastic
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {Ω d : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
theorem matrixCurvatureError_zeroAfter (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (N : ℕ) (σ : ℝ) (e0 : EuclideanSpace ℝ d) (ω : Ω) :
    S.matrixCurvatureError H (zeroAfter N Z) σ e0 N ω =
      S.matrixCurvatureError H Z σ e0 N ω := by
  have ht : S.realization.operatorTransfer N (fun s => H+σ • zeroAfter N Z s ω) =
      S.realization.operatorTransfer N (fun s => H+σ • Z s ω) := by
    unfold Realization.operatorTransfer
    apply congrArg S.realization.contract
    apply orderedProduct_congr
    intro s hs
    dsimp only
    rw [zeroAfter_eq N Z hs]
  unfold matrixCurvatureError
  rw [S.variableError_eq_transfer,S.variableError_eq_transfer,ht]

/-- The finite-data remainder is computed after deterministic zero continuation.
Its definition introduces no additional random variables. -/
def finiteSphereCurvatureRemainder (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (σ : ℝ) (N : ℕ) : ℝ :=
  S.sphereCurvatureRemainder (μ := μ) H (zeroAfter N Z) σ N

/-- Complete actual-run expansion from finite independent samples. In particular,
none of the sample, mean or moment hypotheses constrain times `s >= N`. -/
theorem finiteSphereCurvature_of_iIndepFun (S : TwoTerm) {H : Matrix d d ℝ}
    (B : SpectralBasis H) (Z : ℕ → Ω → Matrix d d ℝ) (N : ℕ) [Nonempty d]
    (hZ : ∀ s<N, Measurable (Z s)) (hind : iIndepFun (fun s : Fin N => Z s.val) μ)
    (hL2 : ∀ s<N, ∀ i j, MemLp (fun ω => Z s ω i j) 2 μ)
    (hmean : ∀ s<N, ∀ i j, (∫ ω, Z s ω i j ∂μ)=0) :
    (∀ σ : ℝ,
      (∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1, ∫ ω,
        ‖S.matrixCurvatureError H Z σ x.val N ω-
          WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp x.val) N)‖^2 ∂μ
          ∂uniformSphere (EuclideanSpace ℝ d)) =
        σ^2*S.realization.isotropicSpectralEnergy N B.eigenvalues
          (fun s i j => ∫ ω, (B.coordinates (Z s ω) i j)^2 ∂μ)+
          S.finiteSphereCurvatureRemainder (μ := μ) H Z σ N) ∧
      (∀ σ, 0≤S.finiteSphereCurvatureRemainder (μ := μ) H Z σ N) ∧
      ((fun σ => S.finiteSphereCurvatureRemainder (μ := μ) H Z σ N)
        =O[𝓝 0] (fun σ : ℝ => σ^4)) := by
  have hh := S.sphereCurvature_of_iIndepFun B (zeroAfter N Z) N
    (zeroAfter_measurable N Z hZ) (zeroAfter_iIndepFun N Z hind)
    (zeroAfter_matrix_memLp N Z hL2) (zeroAfter_matrix_mean N Z hmean)
  refine ⟨?_,hh.2.1,hh.2.2⟩
  intro σ
  have hv := hh.1 σ
  simp_rw [S.matrixCurvatureError_zeroAfter H Z N σ,
    spectralEnergy_zeroAfter S.realization N B Z] at hv
  exact hv

end
end chebyshev1.TwoTerm
