import krylov.Reference.HeavyBallMatrix
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), actual Jacobi orientation isometry.
Use: identify the original positive-edge heavy-ball spectral measure and its true negative-residual CG orientation through a genuine first-site-preserving isometry.
Source: the standard alternating diagonal sign change, with actual orthogonality and real first-site preservation proved from its entries.
-/

namespace krylov.Reference
noncomputable section
open Matrix
variable {N : ℕ}

/-- The actual diagonal alternating sign matrix on the genuine finite physical sites.
Use: The actual diagonal alternating sign matrix on the genuine finite physical sites.
Article: main_krylov, prop:phi(b), actual Jacobi orientation isometry.
Proof: Use the real integer powers at the original chronological site indices. -/
def alternatingMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => (-1:ℝ)^i.val)

/-- The actual physical continuous linear alternating sign map.
Use: The actual physical continuous linear alternating sign map.
Article: main_krylov, prop:phi(b), actual Jacobi orientation isometry.
Proof: Apply the genuine finite diagonal sign matrix in Euclidean space. -/
def alternatingMap (N : ℕ) : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (alternatingMatrix N)

/-- Every actual alternating scalar sign has square one.
Use: Every actual alternating scalar sign has square one.
Article: main_krylov, prop:phi(b), actual Jacobi orientation isometry.
Proof: Multiply the genuine equal integer powers. -/
theorem alternating_square (i : ℕ) : (-1:ℝ)^i*(-1:ℝ)^i=1 := by
  rw [← mul_pow]
  norm_num

/-- The actual alternating matrix is its genuine two-sided inverse.
Use: The actual alternating matrix is its genuine two-sided inverse.
Article: main_krylov, prop:phi(b), actual Jacobi orientation isometry.
Proof: Its true diagonal squares are all one. -/
theorem alternatingMatrix_mul_self (N : ℕ) : alternatingMatrix N*alternatingMatrix N=1 := by
  rw [alternatingMatrix,Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j <;> simp [hij,alternating_square,Matrix.one_apply]

/-- The actual alternating physical map multiplies each genuine coordinate by its true sign.
Use: The actual alternating physical map multiplies each genuine coordinate by its true sign.
Article: main_krylov, prop:phi(b), actual Jacobi orientation isometry.
Proof: Evaluate the real diagonal matrix action. -/
theorem alternatingMap_apply (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    alternatingMap N v i=(-1:ℝ)^i.val*v i := by
  change (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (alternatingMatrix N) v) i=_
  conv_lhs => rw [← WithLp.toLp_ofLp 2 v]
  rw [Matrix.toEuclideanCLM_toLp]
  simp [alternatingMatrix,Matrix.mulVec_diagonal]

/-- The actual alternating physical map preserves the genuine real inner product.
Use: The actual alternating physical map preserves the genuine real inner product.
Article: main_krylov, prop:phi(b), actual Jacobi orientation isometry.
Proof: The two true coordinate signs square to one in every actual inner-product summand. -/
theorem alternatingMap_inner (v w : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (alternatingMap N v) (alternatingMap N w)=inner ℝ v w := by
  -- Both actual coordinate signs appear before cancellation in each genuine real inner-product summand.
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [alternatingMap_apply,alternatingMap_apply]
  simp only [RCLike.inner_apply]
  change ((-1:ℝ)^i.val*w i)*((-1:ℝ)^i.val*v i)=w i*v i
  linear_combination (v i*w i)*alternating_square i.val

/-- The actual alternating physical map fixes the genuine first-site initial gradient, including empty dimensions.
Use: The actual alternating physical map fixes the genuine first-site initial gradient, including empty dimensions.
Article: main_krylov, prop:phi(b), actual Jacobi orientation isometry.
Proof: The only actual present first-site coordinate has true sign one. -/
theorem alternatingMap_firstSite (N : ℕ) :
    alternatingMap N (WithLp.toLp 2 (chebyshev1.JacobiData.site N 0))=
      WithLp.toLp 2 (chebyshev1.JacobiData.site N 0) := by
  ext i
  rw [alternatingMap_apply]
  change (-1:ℝ)^i.val*(if i.val=0 then 1 else 0)=if i.val=0 then 1 else 0
  by_cases hi : i.val=0 <;> simp [hi]
end
end krylov.Reference
