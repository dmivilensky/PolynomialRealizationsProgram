import chebyshev1.Stochastic.GossipFrame
import chebyshev1.Background.GraphSpectrum

/-! Connected graph data construct the constant mode and the complete mean-zero sampling frame. -/
namespace chebyshev1.SpectralBasis
noncomputable section
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d] [DecidableEq d] {H : Matrix d d ℝ} (B : SpectralBasis H)

theorem column_eigenvector (c : d) : H.mulVec (fun i => B.Q i c) =
    B.eigenvalues c • (fun i => B.Q i c) := by
  have hh := congrArg (fun M : Matrix d d ℝ => B.Q*M) B.diagonalize
  have he : H*B.Q=B.Q*Matrix.diagonal B.eigenvalues := by
    simpa only [← Matrix.mul_assoc, B.mul_transpose, Matrix.one_mul] using hh
  funext i
  have hi := congrArg (fun M : Matrix d d ℝ => M i c) he
  rw [Matrix.mul_diagonal] at hi
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm]
    using hi

theorem column_ne_zero (c : d) : (fun i => B.Q i c) ≠ 0 := by
  intro hz
  have hh := congrArg (fun M : Matrix d d ℝ => M c c) B.transpose_mul
  have hq (i : d) : B.Q i c=0 := congrFun hz i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hq, mul_zero,
    Finset.sum_const_zero, Matrix.one_apply, ite_true] at hh
  exact zero_ne_one hh

theorem frameError_range_meanZero (c : d) {k : ℝ} (hk : k≠0) (hcol : ∀ i, B.Q i c=k) :
    Set.range (B.frameError c) = {y : EuclideanSpace ℝ d | (∑ i, y i)=0} := by
  rw [B.frameError_range c]
  ext y
  simp only [Set.mem_ofPred_eq, dotProduct, hcol, ← Finset.mul_sum, mul_eq_zero, hk, false_or]

/-- The sampled directions cover exactly the unit sphere of the mean-zero space. -/
theorem frameSphere_range_meanZero (c : d) {k : ℝ} (hk : k≠0) (hcol : ∀ i, B.Q i c=k) :
    Set.range (fun x : Metric.sphere (0:EuclideanSpace ℝ {j : d // j≠c}) 1 =>
      B.frameError c x.val) = {y : EuclideanSpace ℝ d | ‖y‖=1 ∧ (∑ i, y i)=0} := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨?_,B.frameError_mean_zero c hk hcol x.val⟩
    rw [B.frameError_norm]
    exact mem_sphere_zero_iff_norm.mp x.property
  · rintro ⟨hnorm,hmean⟩
    have hy : y ∈ Set.range (B.frameError c) := (B.frameError_range_meanZero c hk hcol).symm ▸ hmean
    obtain ⟨x,hx⟩ := hy
    refine ⟨⟨x,?_⟩,hx⟩
    apply mem_sphere_zero_iff_norm.mpr
    rw [← B.frameError_norm c x,hx]
    exact hnorm

theorem exists_zero_eigenvalue [Nonempty d] (hH : H.mulVec (fun _ => (1:ℝ))=0) :
    ∃ c, B.eigenvalues c=0 := by
  let a := B.Qᵀ.mulVec (fun _ => (1:ℝ))
  have hQa : B.Q.mulVec a=(fun _ => (1:ℝ)) := by
    dsimp only [a]
    rw [Matrix.mulVec_mulVec,B.mul_transpose,Matrix.one_mulVec]
  have ha : a≠0 := by
    intro hz
    have hh := congrFun hQa (Classical.choice (inferInstance : Nonempty d))
    rw [hz,Matrix.mulVec_zero] at hh
    exact zero_ne_one hh
  obtain ⟨c,hc⟩ : ∃ c, a c≠0 := by
    by_contra hh
    push Not at hh
    apply ha
    funext c
    exact hh c
  have hd : (Matrix.diagonal B.eigenvalues).mulVec a=0 := by
    rw [← B.diagonalize, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hQa,hH,Matrix.mulVec_zero]
  have hh := congrFun hd c
  rw [Matrix.mulVec_diagonal] at hh
  exact ⟨c,(mul_eq_zero.mp hh).resolve_right hc⟩

end
end chebyshev1.SpectralBasis

namespace chebyshev1.Background
noncomputable section
open Stochastic
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {d e : Type*} [Fintype d] [DecidableEq d] [Nonempty d] [Fintype e]

/-- Every orthonormal spectral basis of a positive connected graph has one
constant column and positive eigenvalues on the other columns. -/
theorem weightedGraph_spectral_frame (w : e → ℝ) (hw : ∀ k, 0<w k)
    (a b : e → d) (hconn : EdgesConnected a b)
    (B : SpectralBasis (weightedLaplacian w a b)) :
    ∃ c : d, ∃ k : ℝ, k≠0 ∧ (∀ i, B.Q i c=k) ∧ B.eigenvalues c=0 ∧
      (∀ j, j≠c → 0<B.eigenvalues j) := by
  obtain ⟨c,hc⟩ := B.exists_zero_eigenvalue (weightedLaplacian_mulVec_const w a b 1)
  have hzero := B.column_eigenvector c
  rw [hc,zero_smul] at hzero
  obtain ⟨k,hkcol⟩ := (weightedLaplacian_kernel_iff w hw a b hconn _).mp hzero
  have hk : k≠0 := by
    intro hk0
    apply B.column_ne_zero c
    rw [hkcol,hk0]
    rfl
  have hcol (i : d) : B.Q i c=k := congrFun hkcol i
  refine ⟨c,k,hk,hcol,hc,?_⟩
  intro j hj
  apply weightedLaplacian_nonzero_eigenvalue_pos w hw a b hconn _ _ _
    (B.column_ne_zero j) (B.column_eigenvector j)
  intro hj0
  have hzeroj := B.column_eigenvector j
  rw [hj0,zero_smul] at hzeroj
  obtain ⟨l,hlcol⟩ := (weightedLaplacian_kernel_iff w hw a b hconn _).mp hzeroj
  have hl (i : d) : B.Q i j=l := congrFun hlcol i
  have hh := congrArg (fun M : Matrix d d ℝ => M c j) B.transpose_mul
  simp only [Matrix.mul_apply,Matrix.transpose_apply,hcol,hl,Matrix.one_apply,
    Ne.symm hj,ite_false,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have hd : (Fintype.card d:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hl0 : l=0 := (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hd)).resolve_left hk
  apply B.column_ne_zero j
  rw [hlcol,hl0]
  rfl

/-- The constant mode and the sampling frame are constructed from graph data. -/
theorem exists_weightedGraph_spectral_frame (w : e → ℝ) (hw : ∀ k, 0<w k)
    (a b : e → d) (hconn : EdgesConnected a b) :
    ∃ B : SpectralBasis (weightedLaplacian w a b), ∃ c : d, ∃ k : ℝ,
      k≠0 ∧ (∀ i, B.Q i c=k) ∧ B.eigenvalues c=0 ∧
        (∀ j, j≠c → 0<B.eigenvalues j) := by
  let B := SpectralBasis.ofHermitian _ (weightedLaplacian_isHermitian w a b)
  exact ⟨B,weightedGraph_spectral_frame w hw a b hconn B⟩

end
end chebyshev1.Background

namespace chebyshev1.JacobiData
noncomputable section
open Stochastic Background
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {d e : Type*} [Fintype d] [DecidableEq d] [Nontrivial d] [Fintype e]

/-- The complete connected-graph specialization: graph data supply a constant
mode, the frame samples the entire mean-zero unit sphere, and reversal preserves
the averaged coefficient of the actual dropout model. -/
theorem connectedGraph_meanZero_reversal (J : JacobiData) (I : SpectralInterval) {N : ℕ}
    (hsq : ∀ t, 0 ≤ J.aSq t) {v : ℝ} (hv : v≠0)
    (ht : J.leading N=Polynomial.C v*Polynomial.Chebyshev.T ℝ N)
    (w : e → ℝ) (hw : ∀ k, 0<w k) (a b : e → d) (hconn : EdgesConnected a b) :
    ∃ B : SpectralBasis (weightedLaplacian w a b), ∃ c : d,
      Set.range (fun x : Metric.sphere (0:EuclideanSpace ℝ {j : d // j≠c}) 1 =>
        B.frameError c x.val) = {y : EuclideanSpace ℝ d | ‖y‖=1 ∧ (∑ i, y i)=0} ∧
      ((J.reversed N).method I).frameGossipGamma w (fun k => incidence (a k) (b k)) N B c =
        (J.method I).frameGossipGamma w (fun k => incidence (a k) (b k)) N B c := by
  obtain ⟨B,c,k,hk,hcol,_hc,_hpos⟩ := exists_weightedGraph_spectral_frame w hw a b hconn
  obtain ⟨j,hj⟩ := exists_ne c
  have : Nonempty {j : d // j≠c} := ⟨⟨j,hj⟩⟩
  refine ⟨B,c,B.frameSphere_range_meanZero c hk hcol,?_⟩
  exact J.meanZeroGossipGamma_reversed I hsq (J.admissible_of_terminal I hsq hv ht)
    (J.reversed_admissible_of_terminal I hsq hv ht) w (fun k => incidence (a k) (b k))
    (fun k => incidence_sum (a k) (b k)) B c hcol

end
end chebyshev1.JacobiData
