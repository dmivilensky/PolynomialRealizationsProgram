import chebyshev1.Stochastic.IndependentSpectral
import chebyshev1.Stochastic.ImpulseMatrix

/-! The actual gossip coefficient averaged over a uniform initial direction. -/
namespace chebyshev1
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

namespace Stochastic

def edgeMatrix (w : e → ℝ) (b : e → d → ℝ) (i : e) : Matrix d d ℝ :=
  w i • Matrix.vecMulVec (b i) (b i)

omit [DecidableEq d] [Fintype e] [DecidableEq e] in
theorem edgeMatrix_mulVec (w : e → ℝ) (b : e → d → ℝ) (i : e) (v : d → ℝ) :
    (edgeMatrix w b i).mulVec v = (w i * dotProduct (b i) v) • b i := by
  rw [edgeMatrix, Matrix.smul_mulVec]
  ext k
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, smul_eq_mul, Pi.smul_apply, dotProduct]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

omit [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e] in
theorem edgeMatrix_transpose (w : e → ℝ) (b : e → d → ℝ) (i : e) :
    (edgeMatrix w b i)ᵀ = edgeMatrix w b i := by
  ext k l
  simp only [edgeMatrix, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  ring

def edgeSpectralCoupling {H : Matrix d d ℝ} (B : SpectralBasis H)
    (w : e → ℝ) (b : e → d → ℝ) (i j : d) : ℝ :=
  ∑ k, (B.coordinates (edgeMatrix w b k) i j)^2

omit [DecidableEq e] in
theorem edgeSpectralCoupling_symmetric {H : Matrix d d ℝ} (B : SpectralBasis H)
    (w : e → ℝ) (b : e → d → ℝ) (i j : d) :
    edgeSpectralCoupling B w b i j = edgeSpectralCoupling B w b j i := by
  apply Finset.sum_congr rfl
  intro k _
  have ht : (B.coordinates (edgeMatrix w b k))ᵀ = B.coordinates (edgeMatrix w b k) := by
    simp only [SpectralBasis.coordinates, Matrix.transpose_mul, Matrix.transpose_transpose,
      edgeMatrix_transpose]
    exact (Matrix.mul_assoc B.Qᵀ (edgeMatrix w b k) B.Q).symm
  exact congrArg (fun x : ℝ => x^2) (congrArg (fun M : Matrix d d ℝ => M j i) ht)

end Stochastic

namespace TwoTerm
open MeasureTheory Stochastic
open scoped BigOperators Matrix
variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

omit [DecidableEq e] in
theorem gossipGamma_eq_impulse_energy (S : TwoTerm) (w : e → ℝ) (b : e → d → ℝ)
    (v : EuclideanSpace ℝ d) (N : ℕ) :
    S.gossipGamma w b v N = ∑ s ∈ Finset.range N, ∑ k,
      ‖WithLp.toLp 2 ((S.curvatureImpulse (edgeLaplacian w b) N s (edgeMatrix w b k)).mulVec
        (WithLp.ofLp v))‖^2 := by
  unfold gossipGamma
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [S.curvatureImpulse_mulVec, edgeMatrix_mulVec, map_smul,
    WithLp.toLp_smul, WithLp.toLp_smul, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  rw [S.forcingTailCLM_apply]
  ring

/-- The actual fixed-state gossip coefficient, averaged over spherical Haar probability. -/
def isotropicGossipGamma (S : TwoTerm) (w : e → ℝ) (b : e → d → ℝ) (N : ℕ) : ℝ :=
  ∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
    S.gossipGamma w b x.val N ∂uniformSphere (EuclideanSpace ℝ d)

omit [DecidableEq e] in
theorem isotropicGossipGamma_eq_impulse_hsSq (S : TwoTerm) (w : e → ℝ)
    (b : e → d → ℝ) (N : ℕ) [Nonempty d] :
    S.isotropicGossipGamma w b N = (∑ s ∈ Finset.range N, ∑ k,
      hsSq (S.curvatureImpulse (edgeLaplacian w b) N s (edgeMatrix w b k))) /
        (Fintype.card d:ℝ) := by
  unfold isotropicGossipGamma
  simp_rw [S.gossipGamma_eq_impulse_energy]
  have hi (s : ℕ) (k : e) : Integrable
      (fun x : Metric.sphere (0:EuclideanSpace ℝ d) 1 =>
        ‖WithLp.toLp 2 ((S.curvatureImpulse (edgeLaplacian w b) N s
          (edgeMatrix w b k)).mulVec (WithLp.ofLp x.val))‖^2)
      (uniformSphere (EuclideanSpace ℝ d)) := by
    have hc : Continuous (fun x : Metric.sphere (0:EuclideanSpace ℝ d) 1 =>
        ‖WithLp.toLp 2 ((S.curvatureImpulse (edgeLaplacian w b) N s
          (edgeMatrix w b k)).mulVec (WithLp.ofLp x.val))‖^2) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun k _ => hi s k))]
  simp_rw [integral_finsetSum _ (fun k _ => hi _ k), uniformSphere_matrix_norm_sq,
    Finset.sum_div]

omit [DecidableEq e] in
/-- The symmetric edge coupling is precisely the coefficient in the averaged
fixed-state graph formula. Repeated eigenvalues need no special convention. -/
theorem isotropicGossipGamma_spectral (S : TwoTerm) (w : e → ℝ) (b : e → d → ℝ)
    (N : ℕ) [Nonempty d] (B : SpectralBasis (edgeLaplacian w b)) :
    S.isotropicGossipGamma w b N = S.realization.isotropicSpectralEnergy N B.eigenvalues
      (fun _ => edgeSpectralCoupling B w b) := by
  rw [S.isotropicGossipGamma_eq_impulse_hsSq]
  unfold Realization.isotropicSpectralEnergy
  apply congrArg (fun x : ℝ => x/(Fintype.card d:ℝ))
  have he (s : ℕ) (hs : s<N) (k : e) :
      hsSq (S.curvatureImpulse (edgeLaplacian w b) N s (edgeMatrix w b k)) =
        ∑ i, ∑ j, (S.realization.kernel N s (B.eigenvalues i) (B.eigenvalues j))^2 *
          (B.coordinates (edgeMatrix w b k) i j)^2 := by
    rw [← B.coordinates_hsSq, S.curvatureImpulse_coordinates hs]
    unfold hsSq
    simp_rw [S.curvatureImpulse_diagonal_entry hs, mul_pow]
  calc
    _ = ∑ s ∈ Finset.range N, ∑ k, ∑ i, ∑ j,
        (S.realization.kernel N s (B.eigenvalues i) (B.eigenvalues j))^2 *
          (B.coordinates (edgeMatrix w b k) i j)^2 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_congr rfl (fun k _ => he s (Finset.mem_range.mp hs) k)
    _ = ∑ s ∈ Finset.range N, ∑ i, ∑ j, ∑ k,
        (S.realization.kernel N s (B.eigenvalues i) (B.eigenvalues j))^2 *
          (B.coordinates (edgeMatrix w b k) i j)^2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ s ∈ Finset.range N, ∑ j, ∑ k,
        (S.realization.kernel N s (B.eigenvalues i) (B.eigenvalues j))^2 *
          (B.coordinates (edgeMatrix w b k) i j)^2 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [edgeSpectralCoupling, Finset.mul_sum]

end TwoTerm

namespace JacobiData
open Stochastic
variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

omit [DecidableEq e] in
/-- Reversal invariance of the actual graph coefficient averaged over an isotropic initial error. -/
theorem isotropicGossipGamma_reversed (J : JacobiData) (I : SpectralInterval) {N : ℕ}
    (hsq : ∀ t, 0 ≤ J.aSq t) (h : J.Admissible I N)
    (hrev : (J.reversed N).Admissible I N)
    (w : e → ℝ) (b : e → d → ℝ) [Nonempty d]
    (B : SpectralBasis (edgeLaplacian w b)) :
    ((J.reversed N).method I).isotropicGossipGamma w b N =
      (J.method I).isotropicGossipGamma w b N := by
  rw [TwoTerm.isotropicGossipGamma_spectral _ _ _ _ B,
    TwoTerm.isotropicGossipGamma_spectral _ _ _ _ B]
  exact J.isotropicSpectralEnergy_reversed I hsq h hrev B.eigenvalues _
    (edgeSpectralCoupling_symmetric B w b)

end JacobiData
end
end chebyshev1
