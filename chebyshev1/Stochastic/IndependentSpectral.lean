import chebyshev1.Stochastic.IsotropicSpectral
import Mathlib.Probability.IdentDistrib

/-! Spectral curvature variance in an arbitrary orthonormal eigenbasis. -/
namespace chebyshev1
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {d Ω ι : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]

namespace SpectralBasis
variable {H : Matrix d d ℝ} (B : SpectralBasis H)

theorem coordinates_continuous : Continuous B.coordinates := by
  unfold coordinates
  fun_prop

theorem coordinates_hsSq (M : Matrix d d ℝ) : hsSq (B.coordinates M) = hsSq M := by
  rw [← hsNorm_sq, ← hsNorm_sq]
  exact congrArg (fun x : ℝ => x^2)
    (hsNorm_orthogonal_conjugation B.Q M B.transpose_mul B.mul_transpose)

omit [IsProbabilityMeasure μ] in
theorem coordinates_memLp {E : Ω → Matrix d d ℝ}
    (hE : ∀ i j, MemLp (fun ω => E ω i j) 2 μ) (i j : d) :
    MemLp (fun ω => B.coordinates (E ω) i j) 2 μ := by
  simp only [coordinates, Matrix.mul_apply, Matrix.transpose_apply]
  apply memLp_finsetSum
  intro k _
  have hh : MemLp (fun ω => ∑ l, B.Q l i * E ω l k) 2 μ :=
    memLp_finsetSum _ (fun l _ => (hE l k).const_mul _)
  exact hh.mul_const _

theorem coordinates_mean_zero {E : Ω → Matrix d d ℝ}
    (hE : ∀ i j, MemLp (fun ω => E ω i j) 2 μ)
    (hmean : ∀ i j, ∫ ω, E ω i j ∂μ = 0) (i j : d) :
    (∫ ω, B.coordinates (E ω) i j ∂μ) = 0 := by
  have hi (k : d) : Integrable (fun ω => (∑ l, B.Q l i * E ω l k)*B.Q k j) μ := by
    apply Integrable.mul_const
    exact integrable_finsetSum _ (fun l _ => ((hE l k).integrable (by norm_num)).const_mul _)
  simp only [coordinates, Matrix.mul_apply, Matrix.transpose_apply]
  rw [integral_finsetSum _ (fun k _ => hi k)]
  simp_rw [integral_mul_const, integral_finsetSum _ (fun l _ =>
    ((hE l _).integrable (by norm_num)).const_mul _), integral_const_mul, hmean,
    mul_zero, Finset.sum_const_zero, zero_mul]
  simp only [Finset.sum_const_zero]

end SpectralBasis

namespace Stochastic

theorem independent_matrix_isotropic_spectral (R : Realization ι) (N : ℕ)
    {H : Matrix d d ℝ} (B : SpectralBasis H) (E : ℕ → Ω → Matrix d d ℝ) [Nonempty d]
    (hE : iIndepFun E μ) (hm : ∀ s, Measurable (E s))
    (hL2 : ∀ s i j, MemLp (fun ω => E s ω i j) 2 μ)
    (hmean : ∀ s i j, ∫ ω, E s ω i j ∂μ = 0) :
    (∫ ω, ∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
      ‖WithLp.toLp 2 ((R.linearResponse N H (fun s => E s ω)).mulVec
        (WithLp.ofLp x.val))‖^2 ∂uniformSphere (EuclideanSpace ℝ d) ∂μ) =
      R.isotropicSpectralEnergy N B.eigenvalues
        (fun s i j => ∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ) := by
  have hc := independent_matrix_isotropic_leading R N B.eigenvalues
    (fun s ω => B.coordinates (E s ω)) (hE.comp (fun _ => B.coordinates)
      (fun _ => B.coordinates_continuous.measurable))
    (fun s => B.coordinates_continuous.measurable.comp (hm s))
    (fun s => B.coordinates_memLp (hL2 s)) (fun s => B.coordinates_mean_zero (hL2 s) (hmean s))
  have hhs (ω : Ω) : hsSq (R.linearResponse N (Matrix.diagonal B.eigenvalues)
      (fun s => B.coordinates (E s ω))) = hsSq (R.linearResponse N H (fun s => E s ω)) := by
    have hh := R.linearResponse_coordinates B.Q H B.transpose_mul B.mul_transpose N
      (fun s => E s ω)
    rw [B.diagonalize] at hh
    change R.linearResponse N (Matrix.diagonal B.eigenvalues)
      (fun s => B.coordinates (E s ω)) = B.coordinates (R.linearResponse N H (fun s => E s ω)) at hh
    rw [hh]
    exact B.coordinates_hsSq _
  simp_rw [uniformSphere_matrix_norm_sq, hhs] at hc
  simpa only [uniformSphere_matrix_norm_sq] using hc

omit [IsProbabilityMeasure μ] in
theorem independent_matrix_iid_coupling {H : Matrix d d ℝ} (B : SpectralBasis H)
    (E : ℕ → Ω → Matrix d d ℝ)
    (hiid : ∀ s, IdentDistrib (E s) (E 0) μ μ) (s : ℕ) (i j : d) :
    (∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ) =
      ∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ := by
  exact ((hiid s).comp (B.coordinates_continuous.measurable.eval_matrix.pow_const 2)).integral_eq

omit [IsProbabilityMeasure μ] in
theorem independent_matrix_coupling_mass {H : Matrix d d ℝ} (B : SpectralBasis H)
    (E : Ω → Matrix d d ℝ) (hL2 : ∀ i j, MemLp (fun ω => E ω i j) 2 μ) :
    (∑ i, ∑ j, ∫ ω, (B.coordinates (E ω) i j)^2 ∂μ) = ∫ ω, hsSq (E ω) ∂μ := by
  have hi (i j : d) := (B.coordinates_memLp hL2 i j).integrable_sq
  calc
    _ = ∫ ω, hsSq (B.coordinates (E ω)) ∂μ := by
      unfold hsSq
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
    _ = _ := by simp_rw [B.coordinates_hsSq]

/-- The iid curvature-noise coefficient has the gain-squared bound, with the actual
Hilbert--Schmidt second moment of a single noise matrix. -/
theorem independent_matrix_isotropic_iid_bound (R : Realization ι) (I : SpectralInterval)
    (N : ℕ) {H : Matrix d d ℝ} (B : SpectralBasis H)
    (heig : ∀ i, B.eigenvalues i ∈ Set.Icc I.mu I.L)
    (E : ℕ → Ω → Matrix d d ℝ) [Nonempty d]
    (hE : iIndepFun E μ) (hm : ∀ s, Measurable (E s))
    (hL2 : ∀ s i j, MemLp (fun ω => E s ω i j) 2 μ)
    (hmean : ∀ s i j, ∫ ω, E s ω i j ∂μ = 0)
    (hiid : ∀ s, IdentDistrib (E s) (E 0) μ μ) :
    (∫ ω, ∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
      ‖WithLp.toLp 2 ((R.linearResponse N H (fun s => E s ω)).mulVec
        (WithLp.ofLp x.val))‖^2 ∂uniformSphere (EuclideanSpace ℝ d) ∂μ) ≤
      R.gain I N ^ 2 / (Fintype.card d:ℝ) * (∫ ω, hsSq (E 0 ω) ∂μ) := by
  rw [independent_matrix_isotropic_spectral R N B E hE hm hL2 hmean]
  simp_rw [independent_matrix_iid_coupling B E hiid]
  have hb := R.isotropicSpectralEnergy_iid_bound I N B.eigenvalues heig
    (fun i j => ∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ)
    (fun i j => integral_nonneg (fun _ => sq_nonneg _))
  rw [independent_matrix_coupling_mass B (E 0) (hL2 0)] at hb
  exact hb.trans_eq (by ring)

theorem independent_matrix_isotropic_iid_attained (R : Realization ι) (I : SpectralInterval)
    (N : ℕ) {H : Matrix d d ℝ} (B : SpectralBasis H)
    (E : ℕ → Ω → Matrix d d ℝ) [Nonempty d]
    (hE : iIndepFun E μ) (hm : ∀ s, Measurable (E s))
    (hL2 : ∀ s i j, MemLp (fun ω => E s ω i j) 2 μ)
    (hmean : ∀ s i j, ∫ ω, E s ω i j ∂μ = 0)
    (hiid : ∀ s, IdentDistrib (E s) (E 0) μ μ)
    (p q : d) (hmax : R.kernelNorm N (B.eigenvalues p) (B.eigenvalues q)=R.gain I N)
    (hsupport : ∀ i j, (i≠p ∨ j≠q) → ∀ᵐ ω ∂μ, B.coordinates (E 0 ω) i j=0) :
    (∫ ω, ∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
      ‖WithLp.toLp 2 ((R.linearResponse N H (fun s => E s ω)).mulVec
        (WithLp.ofLp x.val))‖^2 ∂uniformSphere (EuclideanSpace ℝ d) ∂μ) =
      R.gain I N ^ 2 / (Fintype.card d:ℝ) * (∫ ω, hsSq (E 0 ω) ∂μ) := by
  rw [independent_matrix_isotropic_spectral R N B E hE hm hL2 hmean]
  simp_rw [independent_matrix_iid_coupling B E hiid]
  have hc (i j : d) (hh : (∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ) ≠ 0) :
      R.kernelNorm N (B.eigenvalues i) (B.eigenvalues j)=R.gain I N := by
    by_cases hip : i=p
    · by_cases hjq : j=q
      · simpa only [hip,hjq] using hmax
      · exfalso
        apply hh
        calc
          _ = ∫ _ : Ω, (0:ℝ) ∂μ := integral_congr_ae ((hsupport i j (Or.inr hjq)).mono
            (fun _ h => by rw [h]; norm_num))
          _ = 0 := integral_zero _ _
    · exfalso
      apply hh
      calc
        _ = ∫ _ : Ω, (0:ℝ) ∂μ := integral_congr_ae ((hsupport i j (Or.inl hip)).mono
          (fun _ h => by rw [h]; norm_num))
        _ = 0 := integral_zero _ _
  rw [R.isotropicSpectralEnergy_iid_eq I N B.eigenvalues _ hc,
    independent_matrix_coupling_mass B (E 0) (hL2 0)]
  ring

end Stochastic
end
end chebyshev1
