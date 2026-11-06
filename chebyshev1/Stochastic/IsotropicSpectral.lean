import chebyshev1.Stochastic.UniformSphere
import chebyshev1.Stochastic.IndependentCovariance
import chebyshev1.Spectral.DiagonalResponse
import chebyshev1.Realization.Coordinates
import chebyshev1.Spectral.Basis
import chebyshev1.Jacobi.Reversal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Matrix.MeasurableSpace

/-! Isotropic first-order curvature variance and symmetric spectral coupling. -/
namespace chebyshev1
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

namespace Realization

/-- The spectral energy with an explicitly specified covariance coupling. -/
def isotropicSpectralEnergy (R : Realization ι) (N : ℕ) (eig : d → ℝ)
    (C : ℕ → d → d → ℝ) : ℝ :=
  (∑ i, ∑ j, ∑ s ∈ Finset.range N, (R.kernel N s (eig i) (eig j))^2 * C s i j) /
    (Fintype.card d:ℝ)

omit [DecidableEq d] in
theorem isotropicSpectralEnergy_iid_bound (R : Realization ι) (I : SpectralInterval)
    (N : ℕ) (eig : d → ℝ) (heig : ∀ i, eig i ∈ Set.Icc I.mu I.L)
    (C : d → d → ℝ) (hC : ∀ i j, 0 ≤ C i j) :
    R.isotropicSpectralEnergy N eig (fun _ => C) ≤
      R.gain I N ^ 2 * (∑ i, ∑ j, C i j) / (Fintype.card d:ℝ) := by
  unfold isotropicSpectralEnergy
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (hC i j)
  have h := R.kernelNorm_le_gain I N (heig i) (heig j)
  have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) (R.gain_nonneg I N)).mpr h
  simpa only [kernelNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] using hh

omit [DecidableEq d] in
theorem isotropicSpectralEnergy_iid_eq (R : Realization ι) (I : SpectralInterval)
    (N : ℕ) (eig : d → ℝ) (C : d → d → ℝ)
    (hC : ∀ i j, C i j ≠ 0 → R.kernelNorm N (eig i) (eig j) = R.gain I N) :
    R.isotropicSpectralEnergy N eig (fun _ => C) =
      R.gain I N ^ 2 * (∑ i, ∑ j, C i j) / (Fintype.card d:ℝ) := by
  unfold isotropicSpectralEnergy
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]
  by_cases hz : C i j=0
  · simp [hz]
  · have hh := congrArg (fun x : ℝ => x^2) (hC i j hz)
    rw [kernelNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hh
    rw [hh]

end Realization

namespace JacobiData

omit [DecidableEq d] in
/-- Symmetric, time-independent covariance couplings are invariant under Jacobi reversal. -/
theorem isotropicSpectralEnergy_reversed (J : JacobiData) (I : SpectralInterval)
    {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t) (h : J.Admissible I N)
    (hrev : (J.reversed N).Admissible I N) (eig : d → ℝ)
    (C : d → d → ℝ) (hC : ∀ i j, C i j=C j i) :
    ((J.reversed N).realization I).isotropicSpectralEnergy N eig (fun _ => C) =
      (J.realization I).isotropicSpectralEnergy N eig (fun _ => C) := by
  unfold Realization.isotropicSpectralEnergy
  apply congrArg (fun x : ℝ => x/(Fintype.card d:ℝ))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ s ∈ Finset.range N,
        ((J.realization I).kernel N (N-1-s) (eig i) (eig j))^2*C i j := by
      apply Finset.sum_congr rfl
      intro s hs
      dsimp only
      rw [J.kernel_reversed I hsq h hrev s (Finset.mem_range.mp hs), hC j i]
    _ = _ := Finset.sum_range_reflect
      (fun s => ((J.realization I).kernel N s (eig i) (eig j))^2*C i j) N

end JacobiData

namespace Stochastic
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem independent_weighted_square (z : ℕ → Ω → ℝ)
    (hz : iIndepFun z μ) (hm : ∀ s, Measurable (z s))
    (hL2 : ∀ s, MemLp (z s) 2 μ) (hmean : ∀ s, ∫ ω, z s ω ∂μ = 0)
    (a : ℕ → ℝ) (N : ℕ) :
    (∫ ω, (∑ s ∈ Finset.range N, a s * z s ω)^2 ∂μ) =
      ∑ s ∈ Finset.range N, (a s)^2 * ∫ ω, (z s ω)^2 ∂μ := by
  have h := integral_independent_centered_sum_norm_sq
    (hz.precomp Fin.val_injective) (fun s : Fin N => hm s)
    (fun s : Fin N => (hL2 s).integrable (by norm_num))
    (fun s : Fin N => (hL2 s).integrable_sq) (fun s : Fin N => hmean s)
    (fun s : Fin N => a s)
  simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs] at h
  simpa only [← Fin.sum_univ_eq_sum_range, mul_comm] using h

/-- Exact isotropic leading variance for independent matrix-valued perturbations
in an orthonormal eigenbasis. Within-step entries may be arbitrarily correlated. -/
theorem independent_matrix_isotropic_leading (R : Realization ι) (N : ℕ) (eig : d → ℝ)
    (E : ℕ → Ω → Matrix d d ℝ) [Nonempty d]
    (hE : iIndepFun E μ) (hm : ∀ s, Measurable (E s))
    (hL2 : ∀ s i j, MemLp (fun ω => E s ω i j) 2 μ)
    (hmean : ∀ s i j, ∫ ω, E s ω i j ∂μ = 0) :
    (∫ ω, ∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
      ‖WithLp.toLp 2 ((R.linearResponse N (Matrix.diagonal eig) (fun s => E s ω)).mulVec
        (WithLp.ofLp x.val))‖^2 ∂uniformSphere (EuclideanSpace ℝ d) ∂μ) =
      R.isotropicSpectralEnergy N eig (fun s i j => ∫ ω, (E s ω i j)^2 ∂μ) := by
  simp_rw [uniformSphere_matrix_norm_sq]
  rw [integral_div]
  unfold Realization.isotropicSpectralEnergy hsSq
  congr 1
  have hint (i j : d) : Integrable (fun ω =>
      (R.linearResponse N (Matrix.diagonal eig) (fun s => E s ω) i j)^2) μ := by
    have hh : MemLp (fun ω => ∑ s ∈ Finset.range N,
        R.kernel N s (eig i) (eig j) * E s ω i j) 2 μ := by
      exact memLp_finsetSum _ (fun s _ => (hL2 s i j).const_mul _)
    simpa only [R.diagonal_linearResponse_entry] using hh.integrable_sq
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j _
  have hind := hE.comp (fun _ M => M i j) (fun _ => Matrix.measurable_apply)
  simp_rw [R.diagonal_linearResponse_entry]
  exact independent_weighted_square (fun s ω => E s ω i j) hind
    (fun s => (hm s).eval_matrix)
    (fun s => hL2 s i j) (fun s => hmean s i j) (fun s => R.kernel N s (eig i) (eig j)) N

end Stochastic
end
end chebyshev1
