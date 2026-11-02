import krylov.Reference.JacobiSequence
import krylov.Reference.HeavyBallOrientation
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), original Gaussian Jacobi orientation.
Use: transfer true physical windows and actual measured CG coefficients between the original positive-edge Gauss block and its genuine negative-residual orientation.
Source: actual first-site-preserving alternating isometry, original Jacobi entries and proved CG covariance.
-/

namespace krylov.Reference
noncomputable section
open Matrix chebyshev1

/-- The original positive-edge Gaussian Jacobi block is exactly the alternating conjugate of its actual negative-residual prefix.
Use: The original positive-edge Gaussian Jacobi block is exactly the alternating conjugate of its actual negative-residual prefix.
Article: main_krylov, prop:phi(c), original Gaussian Jacobi orientation.
Proof: The genuine diagonal signs cancel and every chronological adjacent sign product equals minus one. -/
theorem jacobiData_matrix_orientation (J : JacobiData) (N : ℕ) :
    alternatingMatrix N*jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N*alternatingMatrix N=
      J.matrix 0 N := by
  -- Reverse only genuine chronological edges while preserving the actual original physical diagonal.
  ext i j
  simp only [alternatingMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal,JacobiData.matrix_apply,Nat.zero_add]
  have hr : (-1:ℝ)^i.val*jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N i j*(-1:ℝ)^j.val=
      jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N i j*((-1:ℝ)^i.val*(-1:ℝ)^j.val) := by ring
  rw [hr]
  by_cases hij : i=j
  · subst j
    simp [jacobiPrefix,alternating_square]
  · by_cases h1 : i.val+1=j.val
    · simp only [jacobiPrefix,ite_eq_right hij,ite_eq_left h1]
      rw [← h1,alternating_adjacent]
      ring
    · by_cases h2 : j.val+1=i.val
      · simp only [jacobiPrefix,ite_eq_right hij,ite_eq_right h1,ite_eq_left h2]
        have hs : (-1:ℝ)^i.val*(-1:ℝ)^j.val= -1 := by rw [mul_comm,← h2,alternating_adjacent]
        rw [hs,← h2]
        ring
      · simp [jacobiPrefix,hij,h1,h2]

/-- Actual alternating conjugation transfers the genuine lower shifted physical positivity form.
Use: Actual alternating conjugation transfers the genuine lower shifted physical positivity form.
Article: main_krylov, prop:phi(c), original Gaussian Jacobi orientation.
Proof: Conjugate the original shifted form by its actual self-inverse orthogonal sign matrix. -/
theorem alternating_conjugate_lower {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (mu : ℝ)
    (h : (alternatingMatrix N*T*alternatingMatrix N-mu • 1).PosSemidef) :
    (T-mu • 1).PosSemidef := by
  -- Conjugate the actual shifted form by its genuine orthogonal inverse before simplifying the true matrix domain.
  have hh := h.mul_mul_conjTranspose_same (alternatingMatrix N)
  have he : alternatingMatrix N*(alternatingMatrix N*T*alternatingMatrix N-mu • 1)*alternatingMatrix N=T-mu • 1 := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
    have hp : alternatingMatrix N*(alternatingMatrix N*T*alternatingMatrix N)*alternatingMatrix N=T := by
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,alternatingMatrix_mul_self,Matrix.one_mul,
        Matrix.mul_assoc,alternatingMatrix_mul_self,Matrix.mul_one]
    rw [hp,alternatingMatrix_mul_self]
  have hc : (alternatingMatrix N)ᴴ=alternatingMatrix N := by simp [alternatingMatrix]
  rwa [hc,he] at hh

/-- Actual alternating conjugation transfers the genuine upper shifted physical positivity form.
Use: Actual alternating conjugation transfers the genuine upper shifted physical positivity form.
Article: main_krylov, prop:phi(c), original Gaussian Jacobi orientation.
Proof: Conjugate the original shifted form by its actual self-inverse orthogonal sign matrix. -/
theorem alternating_conjugate_upper {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (L : ℝ)
    (h : (L • (1 : Matrix (Fin N) (Fin N) ℝ)-alternatingMatrix N*T*alternatingMatrix N).PosSemidef) :
    (L • 1-T).PosSemidef := by
  -- Conjugate the true upper shifted form with the actual orthogonal inverse sign matrix.
  have hh := h.mul_mul_conjTranspose_same (alternatingMatrix N)
  have he : alternatingMatrix N*(L • (1 : Matrix (Fin N) (Fin N) ℝ)-alternatingMatrix N*T*alternatingMatrix N)*alternatingMatrix N=L • 1-T := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
    have hp : alternatingMatrix N*(alternatingMatrix N*T*alternatingMatrix N)*alternatingMatrix N=T := by
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,alternatingMatrix_mul_self,Matrix.one_mul,
        Matrix.mul_assoc,alternatingMatrix_mul_self,Matrix.mul_one]
    rw [hp,alternatingMatrix_mul_self]
  have hc : (alternatingMatrix N)ᴴ=alternatingMatrix N := by simp [alternatingMatrix]
  rwa [hc,he] at hh

/-- The original positive-edge Gaussian operator intertwines with its genuine residual orientation under the actual alternating physical isometry.
Use: The original positive-edge Gaussian operator intertwines with its genuine residual orientation under the actual alternating physical isometry.
Article: main_krylov, prop:phi(c), original Gaussian Jacobi orientation.
Proof: Use the true matrix conjugacy and its genuine inverse sign identity. -/
theorem jacobiData_operator_intertwine (J : JacobiData) {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) :
    cgOperator (J.matrix 0 N) (alternatingMap N v)=
      alternatingMap N (cgOperator (jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N) v) := by
  have hm : J.matrix 0 N*alternatingMatrix N=
      alternatingMatrix N*jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N := by
    rw [← jacobiData_matrix_orientation J N,Matrix.mul_assoc,alternatingMatrix_mul_self,Matrix.mul_one]
  have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ =>
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) M v) hm
  simpa only [map_mul,mul_apply_eq_comp,cgOperator,alternatingMap] using h

/-- The original positive-edge Gauss block and its actual negative-residual prefix have identical genuinely measured CG coefficients.
Use: The original positive-edge Gauss block and its actual negative-residual prefix have identical genuinely measured CG coefficients.
Article: main_krylov, prop:phi(c), original Gaussian Jacobi orientation.
Proof: Apply actual isometric CG covariance and the genuine first-site initial-vector identity. -/
theorem jacobiData_orientation_coefficients (J : JacobiData) (N k : ℕ) :
    let g : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (JacobiData.site N 0)
    CG.length (cgOperator (J.matrix 0 N)) g k=
      CG.length (cgOperator (jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N)) g k ∧
    CG.beta (cgOperator (J.matrix 0 N)) g k=
      CG.beta (cgOperator (jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N)) g k := by
  -- The actual first-site initial gradient is fixed before transferring either genuinely measured coefficient.
  dsimp only
  have ha := cg_length_isometric (alternatingMap N) alternatingMap_inner
    (cgOperator (jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N)) (cgOperator (J.matrix 0 N))
    (jacobiData_operator_intertwine J) (WithLp.toLp 2 (JacobiData.site N 0)) k
  have hb := cg_beta_isometric (alternatingMap N) alternatingMap_inner
    (cgOperator (jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N)) (cgOperator (J.matrix 0 N))
    (jacobiData_operator_intertwine J) (WithLp.toLp 2 (JacobiData.site N 0)) k
  rw [alternatingMap_firstSite] at ha hb
  exact ⟨ha,hb⟩

end
end krylov.Reference
