import jacobi.Comparison.EmbeddedEigenvectors

/-!
Article: jacobi, Theorem 2.1.
The genuine finite target eigenvectors retain unit Euclidean norm;
their actual step embeddings retain unit L2 norm. Zero spectral padding
is the only case with norm zero. No uniform normalization premise is added.
Use: finiteTargetEigenvector_norm_le_one bounds every original padded spectral projector in the nuclear-norm convergence argument for Theorem 2.1.
-/
namespace jacobi.Comparison
noncomputable section
open Real Filter Matrix jacobi.Reference jacobi.Analysis
open scoped Topology

/-- Every actual finite target eigenvector has its original unit norm
whenever its scalar spectral index belongs to the true dimension.
Use: finiteTargetEigenvector_norm_le_one bounds every original padded
spectral projector in the nuclear-norm convergence argument for Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: the original target eigenvector matrix is orthogonal. Its actual
column-square sum is one, exactly the finite Euclidean norm squared. -/
theorem finiteTargetEigenvector_norm (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) (hk:k<n+1) :
    ‖finiteTargetEigenvector a b ha hb n k‖=1 := by
  have hq := congrArg (fun M:Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M ⟨k,hk⟩ ⟨k,hk⟩)
    (targetMeasure a b ha hb n).reconstructedBasis.transpose_mul
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq] at hq
  have hs : ‖finiteTargetEigenvector a b ha hb n k‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [finiteTargetEigenvector,targetEigenvectorEntry,dite_eq_left hk,pow_two] using hq
  nlinarith [norm_nonneg (finiteTargetEigenvector a b ha hb n k)]

/-- Every padded actual finite target vector has norm at most one.
Use: the actual embedded eigenprojectors have a common nuclear-norm
bound across their entire growing original spectral range.
Article: jacobi, Theorem 2.1.
Proof: genuine finite indices use the proved unit norm; all other
original padded vectors are exactly zero. -/
theorem finiteTargetEigenvector_norm_le_one (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) :
    ‖finiteTargetEigenvector a b ha hb n k‖≤1 := by
  by_cases hk:k<n+1
  · exact (finiteTargetEigenvector_norm a b ha hb n k hk).le
  · have hz : finiteTargetEigenvector a b ha hb n k=0 := by
      ext i
      simp only [finiteTargetEigenvector,targetEigenvectorEntry,dite_eq_right hk,PiLp.zero_apply]
    rw [hz,norm_zero]
    norm_num

/-- Every genuine original step-embedded target eigenvector has norm
at most one in the actual full physical Hilbert space.
Use: its original rank-one projector has nuclear norm at most one,
so the genuine L1 spectrum controls the full operator-series tail.
Article: jacobi, Theorem 2.1.
Proof: the actual original step map is an exact linear isometry. -/
theorem embeddedTargetEigenvector_norm_le_one (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) :
    ‖embeddedTargetEigenvector a b ha hb n k‖≤1 := by
  rw [embeddedTargetEigenvector,(fullStepIsometry n).norm_map]
  exact finiteTargetEigenvector_norm_le_one a b ha hb n k

end
end jacobi.Comparison
