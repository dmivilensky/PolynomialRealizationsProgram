import chebyshev1.Stochastic.UniformFrames
import chebyshev1.Stochastic.GossipIsotropic

/-! Isotropic gossip on the orthogonal complement of an omitted spectral mode. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e]

theorem edgeCoordinates_omitted_mode_zero (w : e → ℝ) (b : e → d → ℝ)
    (B : SpectralBasis (edgeLaplacian w b)) (c : d)
    (hb : ∀ k, dotProduct (b k) (fun i => B.Q i c)=0) (k : e) (i : d) :
    B.coordinates (edgeMatrix w b k) i c=0 := by
  have hz : (edgeMatrix w b k).mulVec (fun i => B.Q i c)=0 := by
    rw [edgeMatrix_mulVec, hb, mul_zero, zero_smul]
  have hcol (j : d) : (edgeMatrix w b k*B.Q) j c=0 := congrFun hz j
  rw [SpectralBasis.coordinates, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, hcol, mul_zero, Finset.sum_const_zero]

theorem curvatureImpulse_omitted_mode_zero (S : TwoTerm) {N s : ℕ} (hs : s<N)
    (w : e → ℝ) (b : e → d → ℝ) (B : SpectralBasis (edgeLaplacian w b)) (c : d)
    (hb : ∀ k, dotProduct (b k) (fun i => B.Q i c)=0) (k : e) (i : d) :
    (S.curvatureImpulse (edgeLaplacian w b) N s (edgeMatrix w b k)*B.Q) i c=0 := by
  let M := S.curvatureImpulse (edgeLaplacian w b) N s (edgeMatrix w b k)
  have hz (j : d) : B.coordinates M j c=0 := by
    rw [show M=S.curvatureImpulse (edgeLaplacian w b) N s (edgeMatrix w b k) from rfl,
      S.curvatureImpulse_coordinates hs, S.curvatureImpulse_diagonal_entry hs,
      edgeCoordinates_omitted_mode_zero w b B c hb k j, mul_zero]
  have hr : M*B.Q=B.Q*B.coordinates M := by
    simp only [SpectralBasis.coordinates, ← Matrix.mul_assoc, B.mul_transpose, Matrix.one_mul]
  change (M*B.Q) i c=0
  rw [hr]
  simp only [Matrix.mul_apply, hz, mul_zero, Finset.sum_const_zero]

end
end chebyshev1.Stochastic

namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory Stochastic
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e]

/-- A uniform initial direction in the orthonormal frame omitting mode `c`. -/
def frameGossipGamma (S : TwoTerm) (w : e → ℝ) (b : e → d → ℝ) (N : ℕ)
    (B : SpectralBasis (edgeLaplacian w b)) (c : d) : ℝ :=
  ∫ x : Metric.sphere (0:EuclideanSpace ℝ {j : d // j≠c}) 1,
    S.gossipGamma w b (B.frameError c x.val) N
      ∂uniformSphere (EuclideanSpace ℝ {j : d // j≠c})

theorem frameGossipGamma_eq_impulse_hsSq (S : TwoTerm) (w : e → ℝ) (b : e → d → ℝ)
    (N : ℕ) (B : SpectralBasis (edgeLaplacian w b)) (c : d)
    [Nonempty {j : d // j≠c}] (hb : ∀ k, dotProduct (b k) (fun i => B.Q i c)=0) :
    S.frameGossipGamma w b N B c = (∑ s ∈ Finset.range N, ∑ k,
      hsSq (S.curvatureImpulse (edgeLaplacian w b) N s (edgeMatrix w b k))) /
        (Fintype.card {j : d // j≠c}:ℝ) := by
  unfold frameGossipGamma
  simp_rw [S.gossipGamma_eq_impulse_energy]
  have hi (s : ℕ) (k : e) : Integrable
      (fun x : Metric.sphere (0:EuclideanSpace ℝ {j : d // j≠c}) 1 =>
        ‖WithLp.toLp 2 ((S.curvatureImpulse (edgeLaplacian w b) N s
          (edgeMatrix w b k)).mulVec (WithLp.ofLp (B.frameError c x.val)))‖^2)
      (uniformSphere (EuclideanSpace ℝ {j : d // j≠c})) := by
    have hc : Continuous (fun x : Metric.sphere (0:EuclideanSpace ℝ {j : d // j≠c}) 1 =>
        ‖WithLp.toLp 2 ((S.curvatureImpulse (edgeLaplacian w b) N s
          (edgeMatrix w b k)).mulVec (WithLp.ofLp (B.frameError c x.val)))‖^2) := by
      unfold SpectralBasis.frameError
      fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun k _ => hi s k))]
  calc
    _ = ∑ s ∈ Finset.range N, ∑ k,
        hsSq (S.curvatureImpulse (edgeLaplacian w b) N s (edgeMatrix w b k)) /
          (Fintype.card {j : d // j≠c}:ℝ) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [integral_finsetSum _ (fun k _ => hi s k)]
      exact Finset.sum_congr rfl (fun k _ => B.uniformSphere_frame_matrix_norm_sq c _
        (curvatureImpulse_omitted_mode_zero S (Finset.mem_range.mp hs) w b B c hb k))
    _ = _ := by simp only [Finset.sum_div]

theorem frameGossipGamma_eq_rescaled_isotropic (S : TwoTerm) (w : e → ℝ) (b : e → d → ℝ)
    (N : ℕ) (B : SpectralBasis (edgeLaplacian w b)) (c : d)
    [Nonempty {j : d // j≠c}] (hb : ∀ k, dotProduct (b k) (fun i => B.Q i c)=0) :
    S.frameGossipGamma w b N B c =
      (Fintype.card d:ℝ)/(Fintype.card {j : d // j≠c}:ℝ) * S.isotropicGossipGamma w b N := by
  have : Nonempty d := ⟨c⟩
  rw [S.frameGossipGamma_eq_impulse_hsSq w b N B c hb,
    S.isotropicGossipGamma_eq_impulse_hsSq]
  have hd : (Fintype.card d:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end
end chebyshev1.TwoTerm

namespace chebyshev1.SpectralBasis
noncomputable section
open scoped BigOperators Matrix
variable {d : Type*} [Fintype d] [DecidableEq d] {H : Matrix d d ℝ} (B : SpectralBasis H)

theorem frame_dimension (c : d) : Fintype.card {j : d // j≠c}=Fintype.card d-1 := by
  simpa only [Fintype.card_subtype_eq] using Fintype.card_subtype_compl (fun j : d => j=c)

theorem frameError_mean_zero (c : d) {k : ℝ} (hk : k≠0) (hcol : ∀ i, B.Q i c=k)
    (x : EuclideanSpace ℝ {j : d // j≠c}) :
    (∑ i, B.frameError c x i)=0 := by
  have hh := B.frameError_orthogonal c x
  simp only [dotProduct, hcol, ← Finset.mul_sum] at hh
  exact (mul_eq_zero.mp hh).resolve_left hk

end
end chebyshev1.SpectralBasis

namespace chebyshev1.JacobiData
noncomputable section
open Stochastic
open scoped BigOperators
variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e]

/-- Reversal for a genuinely uniform direction in the complement of an omitted
mode; the sampling space has dimension `card d - 1`. -/
theorem frameGossipGamma_reversed (J : JacobiData) (I : SpectralInterval) {N : ℕ}
    (hsq : ∀ t, 0 ≤ J.aSq t) (h : J.Admissible I N)
    (hrev : (J.reversed N).Admissible I N)
    (w : e → ℝ) (b : e → d → ℝ) (B : SpectralBasis (edgeLaplacian w b)) (c : d)
    [Nonempty {j : d // j≠c}] (hb : ∀ k, dotProduct (b k) (fun i => B.Q i c)=0) :
    ((J.reversed N).method I).frameGossipGamma w b N B c =
      (J.method I).frameGossipGamma w b N B c := by
  have : Nonempty d := ⟨c⟩
  rw [TwoTerm.frameGossipGamma_eq_rescaled_isotropic _ w b N B c hb,
    TwoTerm.frameGossipGamma_eq_rescaled_isotropic _ w b N B c hb,
    J.isotropicGossipGamma_reversed I hsq h hrev w b B]

/-- The graph specialization: every edge has zero coordinate sum, and the
omitted eigenvector is the nonzero normalized constant vector. -/
theorem meanZeroGossipGamma_reversed (J : JacobiData) (I : SpectralInterval) {N : ℕ}
    (hsq : ∀ t, 0 ≤ J.aSq t) (h : J.Admissible I N)
    (hrev : (J.reversed N).Admissible I N)
    (w : e → ℝ) (b : e → d → ℝ) (hb : ∀ k, ∑ i, b k i=0)
    (B : SpectralBasis (edgeLaplacian w b)) (c : d) [Nonempty {j : d // j≠c}]
    {k : ℝ} (hcol : ∀ i, B.Q i c=k) :
    ((J.reversed N).method I).frameGossipGamma w b N B c =
      (J.method I).frameGossipGamma w b N B c := by
  apply J.frameGossipGamma_reversed I hsq h hrev w b B c
  intro r
  simp only [dotProduct, hcol, ← Finset.sum_mul, hb, zero_mul]

end
end chebyshev1.JacobiData
