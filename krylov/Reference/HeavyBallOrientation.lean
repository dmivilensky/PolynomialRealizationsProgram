import krylov.Reference.AlternatingSigns
import krylov.Reference.CGCovariance
import krylov.Reference.HeavyBallWindow
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), genuine printed heavy-ball Jacobi orientation.
Use: transfer actual measured CG parameters and strict spectral support between the original positive-edge matrix and the true normalized residual orientation.
Source: actual first-site-preserving alternating orthogonal conjugacy, genuine CG covariance and the finite Hermitian characteristic polynomial theorem.
-/

namespace krylov.Reference
noncomputable section
open Matrix
variable {N : ℕ}

/-- Two actual adjacent chronological signs have genuine product minus one.
Use: Two actual adjacent chronological signs have genuine product minus one.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball Jacobi orientation.
Proof: Use the true successor power and the actual sign square. -/
theorem alternating_adjacent (i : ℕ) : (-1:ℝ)^i*(-1:ℝ)^(i+1)= -1 := by
  rw [pow_succ,← mul_assoc,alternating_square,one_mul]

/-- The original positive-edge heavy-ball matrix is the actual alternating conjugate of the genuine negative-residual matrix.
Use: The original positive-edge heavy-ball matrix is the actual alternating conjugate of the genuine negative-residual matrix.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball Jacobi orientation.
Proof: The true diagonal signs cancel on the diagonal and reverse every actual adjacent physical edge. -/
theorem heavyBallMatrix_alternating (d q : ℝ) (N : ℕ) :
    alternatingMatrix N*heavyBallMatrix d q N*alternatingMatrix N=heavyBallMatrix d (-q) N := by
  -- Preserve the actual first diagonal and reverse only the genuine adjacent physical edges.
  ext i j
  simp only [alternatingMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal]
  have hr : (-1:ℝ)^i.val*heavyBallMatrix d q N i j*(-1:ℝ)^j.val=
      heavyBallMatrix d q N i j*((-1:ℝ)^i.val*(-1:ℝ)^j.val) := by ring
  rw [hr]
  by_cases hij : i=j
  · subst j
    simp [heavyBallMatrix,alternating_square]
  · by_cases h1 : i.val+1=j.val
    · simp only [heavyBallMatrix,ite_eq_right hij,ite_eq_left (Or.inl h1)]
      rw [← h1,alternating_adjacent]
      ring
    · by_cases h2 : j.val+1=i.val
      · simp only [heavyBallMatrix,ite_eq_right hij,ite_eq_left (Or.inr h2)]
        have hs : (-1:ℝ)^i.val*(-1:ℝ)^j.val= -1 := by
          rw [mul_comm,← h2,alternating_adjacent]
        rw [hs]
        ring
      · simp [heavyBallMatrix,hij,h1,h2]

/-- The genuine positive-edge and negative-residual heavy-ball operators intertwine under the actual physical alternating isometry.
Use: The genuine positive-edge and negative-residual heavy-ball operators intertwine under the actual physical alternating isometry.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball Jacobi orientation.
Proof: Use the true matrix conjugacy and its actual sign inverse. -/
theorem heavyBall_operator_intertwine (d q : ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    cgOperator (heavyBallMatrix d (-q) N) (alternatingMap N v)=
      alternatingMap N (cgOperator (heavyBallMatrix d q N) v) := by
  have hm : heavyBallMatrix d (-q) N*alternatingMatrix N=alternatingMatrix N*heavyBallMatrix d q N := by
    rw [← heavyBallMatrix_alternating d q N,Matrix.mul_assoc,alternatingMatrix_mul_self,Matrix.mul_one]
  have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ =>
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) M v) hm
  simpa only [map_mul,mul_apply_eq_comp,cgOperator,alternatingMap] using h

/-- Both genuine heavy-ball orientations have identical actual measured first-site CG line lengths and recurrence ratios.
Use: Both genuine heavy-ball orientations have identical actual measured first-site CG line lengths and recurrence ratios.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball Jacobi orientation.
Proof: Apply actual CG isometric covariance through the genuine first-site-preserving operator intertwiner. -/
theorem heavyBall_orientation_coefficients (d q : ℝ) (N k : ℕ) :
    let g : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (chebyshev1.JacobiData.site N 0)
    CG.length (cgOperator (heavyBallMatrix d (-q) N)) g k=
      CG.length (cgOperator (heavyBallMatrix d q N)) g k ∧
    CG.beta (cgOperator (heavyBallMatrix d (-q) N)) g k=
      CG.beta (cgOperator (heavyBallMatrix d q N)) g k := by
  -- The actual alternating isometry fixes the true initial first-site gradient before either measured coefficient is transferred.
  dsimp only
  have hα := cg_length_isometric (alternatingMap N) alternatingMap_inner
    (cgOperator (heavyBallMatrix d q N)) (cgOperator (heavyBallMatrix d (-q) N))
    (heavyBall_operator_intertwine d q) (WithLp.toLp 2 (chebyshev1.JacobiData.site N 0)) k
  have hβ := cg_beta_isometric (alternatingMap N) alternatingMap_inner
    (cgOperator (heavyBallMatrix d q N)) (cgOperator (heavyBallMatrix d (-q) N))
    (heavyBall_operator_intertwine d q) (WithLp.toLp 2 (chebyshev1.JacobiData.site N 0)) k
  rw [alternatingMap_firstSite] at hα hβ
  exact ⟨hα,hβ⟩
/-- The actual positive-edge and normalized-residual heavy-ball matrices have the same genuine characteristic polynomial.
Use: The actual positive-edge and normalized-residual heavy-ball matrices have the same genuine characteristic polynomial.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball Jacobi orientation.
Proof: The actual alternating conjugation cancels through the true cyclic determinant identity. -/
theorem heavyBall_orientation_charpoly (d q : ℝ) (N : ℕ) :
    (heavyBallMatrix d (-q) N).charpoly=(heavyBallMatrix d q N).charpoly := by
  rw [← heavyBallMatrix_alternating d q N,Matrix.charpoly_mul_comm,← Matrix.mul_assoc,
    alternatingMatrix_mul_self,Matrix.one_mul]

/-- The actual positive-edge and normalized-residual heavy-ball matrices have the same genuine ordered eigenvalues.
Use: The actual positive-edge and normalized-residual heavy-ball matrices have the same genuine ordered eigenvalues.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball Jacobi orientation.
Proof: Use their true common characteristic polynomial in the actual Hermitian spectral theorem. -/
theorem heavyBall_orientation_eigenvalues (d q : ℝ) (hd : 0 < d) (N : ℕ) :
    (heavyBallMatrix_posDef d (-q) hd N).1.eigenvalues=(heavyBallMatrix_posDef d q hd N).1.eigenvalues := by
  exact ((heavyBallMatrix_posDef d (-q) hd N).1.eigenvalues_eq_eigenvalues_iff
    (heavyBallMatrix_posDef d q hd N).1).mpr (heavyBall_orientation_charpoly d q N)

/-- The original positive-edge heavy-ball matrix has genuine strict finite spectral support inside its printed squared-parameter interval.
Use: The original positive-edge heavy-ball matrix has genuine strict finite spectral support inside its printed squared-parameter interval.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball Jacobi orientation.
Proof: Transfer the actual strict negative-residual spectrum through its genuine orthogonal conjugacy. -/
theorem heavyBall_positive_spectral_window (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (hq1 : q≤1) (N : ℕ) :
    ∀ i,d*(1-q)^2<(heavyBallMatrix_posDef d (-q) hd N).1.eigenvalues i ∧
      (heavyBallMatrix_posDef d (-q) hd N).1.eigenvalues i<d*(1+q)^2 := by
  rw [heavyBall_orientation_eigenvalues d q hd N]
  exact heavyBall_strict_spectral_window d q hd hq hq1 N

end
end krylov.Reference
