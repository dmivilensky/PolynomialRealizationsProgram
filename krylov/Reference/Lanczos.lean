import krylov.Reference.PolynomialAction
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Order.Star.Real

/-!
Article: main_krylov, prop:dict(i) and s5:fibre, measured Lanczos/LDL data.
Use: construct the residual basis and its Jacobi compression directly from
the executed CG recurrence and identify the actual positive LDL pivots.
Source: the classical CG--Lanczos equivalence (Meurant06, GolubMeurant10).
-/

namespace krylov.Reference.CG
noncomputable section
open Matrix
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The computed residual divided by its actual norm.
Use: fixes the negative-off-diagonal orientation of the measured Jacobi matrix.
Article: main_krylov, prop:dict(i), normalized residual basis. -/
def residualUnit (Q : E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  ‖gradient Q g k‖⁻¹ • gradient Q g k

/-- The computed direction divided by the actual residual norm.
Use: conjugacy diagonalizes its positive operator Gram matrix.
Article: main_krylov, prop:dict(i), CG factorization coordinates. -/
def scaledDirection (Q : E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  ‖gradient Q g k‖⁻¹ • direction Q g k

/-- The positive square-root residual norm ratio computed by CG.
Use: the adjacent entry of the actual unit lower bidiagonal factor.
Article: main_krylov, prop:dict(i), sqrt(β_k). -/
def residualRatio (Q : E →L[ℝ] E) (g : E) (k : ℕ) : ℝ :=
  ‖gradient Q g (k+1)‖/‖gradient Q g k‖

/-- The actual residual norm ratio is the positive square root of the actual Fletcher--Reeves coefficient.
Use: matches the source's square-root coefficient without a sign assumption.
Article: main_krylov, prop:dict(i), L_(k+1,k)=−sqrt(β_k).
Proof: square roots commute with nonnegative division and recover the nonnegative residual norms. -/
theorem residualRatio_eq_sqrt (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    residualRatio Q g k=Real.sqrt (beta Q g k) := by
  unfold residualRatio beta
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- All computed residual units in a nondegenerate prefix form an orthonormal family.
Use: the measured compression really is a Lanczos compression in an orthonormal basis.
Article: main_krylov, prop:dict(i), CG--Lanczos basis.
Proof: normalize the already proved orthogonal actual residuals by their genuine nonzero norms. -/
theorem residualUnit_orthonormal (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hg : ∀ i<m, gradient Q g i≠0) : Orthonormal ℝ (fun i : Fin m => residualUnit Q g i.val) := by
  -- Each off-diagonal entry vanishes by the actual finite-prefix residual invariant.
  rw [orthonormal_iff_ite]
  intro i j
  simp only [residualUnit, real_inner_smul_left, real_inner_smul_right]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl, real_inner_self_eq_norm_sq]
    have hn := norm_ne_zero_iff.mpr (hg i.val i.isLt)
    field_simp
  · rw [ite_eq_right hij]
    have ho (a b : Fin m) (hab : a.val<b.val) : inner ℝ (gradient Q g a.val) (gradient Q g b.val)=0 :=
      (invariant Q hQ hpos g b.val (fun k hk => hg k (hk.trans b.isLt))).old_gradient a.val hab
    rcases lt_or_gt_of_ne (show i.val≠j.val from fun h => hij (Fin.ext h)) with h | h
    · rw [ho i j h, mul_zero, mul_zero]
    · rw [real_inner_comm (gradient Q g j.val) (gradient Q g i.val), ho j i h, mul_zero, mul_zero]

/-- Normalized actual residuals and scaled actual directions obey the bidiagonal CG relation.
Use: constructs the true LDL factor rather than postulating a tridiagonal matrix with chosen pivots.
Article: main_krylov, prop:dict(i), the CG--LDL dictionary.
Proof: divide the executed Fletcher--Reeves direction update by the actual new residual norm. -/
theorem residualUnit_succ (Q : E →L[ℝ] E) (g : E) (k : ℕ)
    (hk : gradient Q g k≠0) (hn : gradient Q g (k+1)≠0) :
    residualUnit Q g (k+1)= -scaledDirection Q g (k+1)+
      residualRatio Q g k • scaledDirection Q g k := by
  -- Only the two proved nonzero residual norms are canceled in this normalization.
  have hkn := norm_ne_zero_iff.mpr hk
  have hnn := norm_ne_zero_iff.mpr hn
  unfold residualUnit scaledDirection residualRatio
  rw [direction_succ, smul_add, smul_neg, smul_smul, neg_add_rev, neg_neg, smul_smul]
  have he : ‖gradient Q g (k+1)‖⁻¹*beta Q g k=
      (‖gradient Q g (k+1)‖/‖gradient Q g k‖)*‖gradient Q g k‖⁻¹ := by
    dsimp only [beta]
    field_simp
  rw [he]
  module

/-- Conjugacy makes the actual scaled-direction operator Gram matrix diagonal with inverse line pivots.
Use: identifies the diagonal D in the measured LDL factorization.
Article: main_krylov, prop:dict(i), D_kk=1/α_k.
Proof: distinct directions are actually conjugate; on the diagonal the actual
line formula divides the true positive curvature by the true residual energy. -/
theorem scaledDirection_gram (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hg : ∀ i<m, gradient Q g i≠0) (i j : Fin m) :
    inner ℝ (scaledDirection Q g i.val) (Q (scaledDirection Q g j.val))=
      if i=j then (length Q g i.val)⁻¹ else 0 := by
  -- Every line pivot is computed from the same run whose conjugacy is being used.
  simp only [scaledDirection, map_smul, real_inner_smul_left, real_inner_smul_right]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    have hi := invariant Q hQ hpos g i.val (fun k hk => hg k (hk.trans i.isLt))
    obtain ⟨hd, _, hl⟩ := invariant_line_pos Q hpos g i.val hi (hg i.val i.isLt)
    have hc := (hpos _ hd).ne'
    have hn := norm_ne_zero_iff.mpr (hg i.val i.isLt)
    rw [hl]
    field_simp
  · rw [ite_eq_right hij]
    have ho (a b : Fin m) (hab : a.val<b.val) : inner ℝ (direction Q g a.val) (Q (direction Q g b.val))=0 :=
      (invariant Q hQ hpos g b.val (fun k hk => hg k (hk.trans b.isLt))).conjugate a.val b.val hab le_rfl
    rcases lt_or_gt_of_ne (show i.val≠j.val from fun h => hij (Fin.ext h)) with h | h
    · rw [ho i j h, mul_zero, mul_zero]
    · have he := hQ (direction Q g j.val) (direction Q g i.val)
      change inner ℝ (Q (direction Q g j.val)) (direction Q g i.val)=
        inner ℝ (direction Q g j.val) (Q (direction Q g i.val)) at he
      rw [real_inner_comm (Q (direction Q g j.val)) (direction Q g i.val), he,
        ho j i h, mul_zero, mul_zero]

/-- The measured unit lower bidiagonal CG factor.
Use: its entries use actual residual norms and therefore actual measured CG coefficients.
Article: main_krylov, prop:dict(i), L with subdiagonal −sqrt(β). -/
def lowerFactor (Q : E →L[ℝ] E) (g : E) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (if i=j then 1 else 0) - (if i.val=j.val+1 then residualRatio Q g j.val else 0)

/-- The actual Lanczos compression in the normalized residual orientation.
Use: a matrix computed from the actual reference, with no independently supplied Jacobi data.
Article: main_krylov, prop:dict(i), T. -/
def lanczosMatrix (Q : E →L[ℝ] E) (g : E) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => inner ℝ (residualUnit Q g i.val) (Q (residualUnit Q g j.val))

/-- The lower bidiagonal factor transforms scaled directions into actual normalized residuals.
Use: the measured LDL factorization follows from a proved vector identity.
Article: main_krylov, prop:dict(i).
Proof: each row contains the current direction and, when present, its one predecessor;
the executed normalized direction recurrence gives the claimed residual. -/
theorem lowerFactor_action (Q : E →L[ℝ] E) (g : E) (m : ℕ)
    (hg : ∀ i<m, gradient Q g i≠0) (i : Fin m) :
    (∑ j : Fin m, lowerFactor Q g m i j • scaledDirection Q g j.val)= -residualUnit Q g i.val := by
  -- Split the identity diagonal from the single strictly lower predecessor entry.
  simp only [lowerFactor, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  by_cases hi : i.val=0
  · have hz : (∑ j : Fin m, if i.val=j.val+1 then residualRatio Q g j.val • scaledDirection Q g j.val else 0)=0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [ite_eq_right (by omega)]
    rw [hz, sub_zero]
    change ‖gradient Q g i.val‖⁻¹ • direction Q g i.val= -(‖gradient Q g i.val‖⁻¹ • gradient Q g i.val)
    rw [hi]
    change ‖g‖⁻¹ • (-g)= -(‖g‖⁻¹ • g)
    exact smul_neg _ _
  · let j : Fin m := ⟨i.val-1, by omega⟩
    have hj : j.val+1=i.val := by dsimp only [j]; omega
    have hs : (∑ a : Fin m, if i.val=a.val+1 then residualRatio Q g a.val • scaledDirection Q g a.val else 0)=
        residualRatio Q g j.val • scaledDirection Q g j.val := by
      rw [Finset.sum_eq_single j]
      · rw [ite_eq_left hj.symm]
      · intro a _ ha
        exact ite_eq_right (by intro h; apply ha; apply Fin.ext; omega)
      · simp
    rw [hs]
    have he := residualUnit_succ Q g j.val (hg j.val j.isLt) (hg (j.val+1) (by omega))
    rw [hj] at he
    rw [he]
    module

/-- The measured Lanczos matrix has the genuine LDL factorization with the actual inverse CG line lengths.
Use: the only free last Jacobi pivot in later information fibres is the actual last CG pivot.
Article: main_krylov, prop:dict(i), T=L diag(1/α)Lᵀ.
Proof: expand the established bidiagonal residual representation in both slots;
the proved actual scaled-direction Gram matrix kills every off-diagonal term. -/
theorem lanczosMatrix_ldl (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hg : ∀ i<m, gradient Q g i≠0) :
    lanczosMatrix Q g m=lowerFactor Q g m*
      Matrix.diagonal (fun i : Fin m => (length Q g i.val)⁻¹)*(lowerFactor Q g m)ᵀ := by
  -- The factorization is derived from actual vector actions and conjugacy, not entrywise coefficient guesses.
  ext i j
  have hi : residualUnit Q g i.val= -(∑ a : Fin m, lowerFactor Q g m i a • scaledDirection Q g a.val) := by
    rw [lowerFactor_action Q g m hg i, neg_neg]
  have hj : residualUnit Q g j.val= -(∑ b : Fin m, lowerFactor Q g m j b • scaledDirection Q g b.val) := by
    rw [lowerFactor_action Q g m hg j, neg_neg]
  rw [lanczosMatrix, hi, hj, map_neg, inner_neg_neg, map_sum, sum_inner]
  rw [Matrix.mul_apply]
  simp only [map_smul, inner_sum, real_inner_smul_left, real_inner_smul_right,
    scaledDirection_gram Q hQ hpos g m hg, Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp only [ite_true]
    ring
  · intro b _ hb
    rw [ite_eq_right (Ne.symm hb), mul_zero, mul_zero]
  · simp

/-- The measured lower factor has unit diagonal and no entries above it.
Use: its determinant is one, so every actual LDL pivot is visible independently.
Article: main_krylov, prop:dict(i), unit lower bidiagonal factor.
Proof: the only nonidentity entries are exactly one row below the diagonal. -/
theorem lowerFactor_triangular (Q : E →L[ℝ] E) (g : E) (m : ℕ) :
    (lowerFactor Q g m).IsLowerTriangular ∧ ∀ i, lowerFactor Q g m i i=1 := by
  constructor
  · intro i j hij
    change i<j at hij
    have hv : i.val<j.val := hij
    simp only [lowerFactor, ite_eq_right (ne_of_lt hij), ite_eq_right (by omega : i.val≠j.val+1), sub_self]
  · intro i
    simp only [lowerFactor, ite_true, ite_eq_right (by omega : i.val≠i.val+1), sub_zero]

/-- The measured Lanczos matrix has no entries beyond the adjacent diagonals.
Use: the actual CG compression is tridiagonal, rather than merely declared Jacobi data.
Article: main_krylov, prop:dict(i), measured tridiagonal matrix.
Proof: two lower-bidiagonal rows have disjoint supports when their indices are separated by more than one. -/
theorem lanczosMatrix_tridiagonal (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hg : ∀ i<m, gradient Q g i≠0) (i j : Fin m)
    (hij : i.val+1 < j.val ∨ j.val+1 < i.val) : lanczosMatrix Q g m i j=0 := by
  -- The two row supports cannot overlap at a summation index outside the adjacent diagonals.
  rw [lanczosMatrix_ldl Q hQ hpos g m hg, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases hi : i=a ∨ i.val=a.val+1
  · have hj : j≠a ∧ j.val≠a.val+1 := by
      rcases hi with rfl | hi
      · constructor <;> omega
      · constructor
        · intro h; subst j; omega
        · omega
    simp only [lowerFactor, ite_eq_right hj.1, ite_eq_right hj.2, sub_self, mul_zero]
  · push Not at hi
    simp only [lowerFactor, ite_eq_right hi.1, ite_eq_right hi.2, sub_self, zero_mul]

/-- The actual adjacent Lanczos coupling is the negative square-root CG coefficient divided by the actual line length.
Use: matches the source's negative-off-diagonal convention and proves irreducibility before exhaustion.
Article: main_krylov, prop:dict(i), T_(k,k+1)=−sqrt(β_k)/α_k.
Proof: in the LDL product the two adjacent bidiagonal rows overlap only at the preceding diagonal site. -/
theorem lanczosMatrix_adjacent (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hg : ∀ i<m, gradient Q g i≠0) (i j : Fin m) (hij : i.val+1=j.val) :
    lanczosMatrix Q g m i j= -Real.sqrt (beta Q g i.val)/length Q g i.val := by
  -- Only the actual predecessor index survives in the factor product.
  rw [lanczosMatrix_ldl Q hQ hpos g m hg, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  rw [Finset.sum_eq_single i]
  · have hji : j≠i := by intro h; subst j; omega
    simp only [lowerFactor, ite_true, ite_eq_right (by omega : i.val≠i.val+1),
      sub_zero, ite_eq_right hji, ite_eq_left hij.symm, zero_sub, residualRatio_eq_sqrt]
    ring
  · intro a _ hai
    by_cases hia : i.val=a.val+1
    · have hja : j≠a ∧ j.val≠a.val+1 := by
        constructor
        · intro h; subst j; omega
        · omega
      simp only [lowerFactor, ite_eq_right hja.1, ite_eq_right hja.2, sub_self, mul_zero]
    · simp only [lowerFactor, ite_eq_right (Ne.symm hai), ite_eq_right hia, sub_self, zero_mul]
  · simp

/-- Every internal measured Lanczos off-diagonal is strictly negative before active-spectrum exhaustion.
Use: later fibre and spectral arguments use proved irreducibility of the actual measured matrix.
Article: main_krylov, prop:dict(i), negative off-diagonal orientation.
Proof: actual residual norms and actual line lengths are strictly positive throughout the finite prefix. -/
theorem lanczosMatrix_adjacent_neg (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hg : ∀ i<m, gradient Q g i≠0) (i j : Fin m) (hij : i.val+1=j.val) :
    lanczosMatrix Q g m i j<0 := by
  -- Both actual residual norms and the actual line pivot are positive at this internal index.
  rw [lanczosMatrix_adjacent Q hQ hpos g m hg i j hij, ← residualRatio_eq_sqrt]
  have hr : 0<residualRatio Q g i.val := div_pos
    (norm_pos_iff.mpr (hg (i.val+1) (by omega))) (norm_pos_iff.mpr (hg i.val i.isLt))
  have hl := (invariant_line_pos Q hpos g i.val
    (invariant Q hQ hpos g i.val (fun k hk => hg k (hk.trans i.isLt))) (hg i.val i.isLt)).2.1
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hr) hl

/-- The measured Lanczos determinant is the product of the actual inverse CG line lengths.
Use: identifies every leading-block determinant with the actual CG pivots.
Article: main_krylov, prop:dict(i), the Lanczos--LDL determinant dictionary.
Proof: both unit triangular factors have determinant one; take determinants of the proved actual LDL identity. -/
theorem lanczosMatrix_det (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hg : ∀ i<m, gradient Q g i≠0) :
    (lanczosMatrix Q g m).det=∏ i : Fin m, (length Q g i.val)⁻¹ := by
  have hL : (lowerFactor Q g m).det=1 := by
    rw [Matrix.det_of_isLowerTriangular _ (lowerFactor_triangular Q g m).1]
    simp only [(lowerFactor_triangular Q g m).2, Finset.prod_const_one]
  rw [lanczosMatrix_ldl Q hQ hpos g m hg, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal, hL, one_mul, mul_one]

/-- The measured Lanczos compression is genuinely positive definite throughout every nondegenerate prefix.
Use: all its inverse moments and LDL pivots come from an actual positive Jacobi matrix.
Article: main_krylov, prop:dict(i), T positive definite.
Proof: the diagonal factor has the proved positive actual inverse lines and
the actual unit lower factor has determinant one, so positive congruence applies. -/
theorem lanczosMatrix_posDef (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hg : ∀ i<m, gradient Q g i≠0) : (lanczosMatrix Q g m).PosDef := by
  -- The positive congruence uses the actual triangular factor, whose invertibility is proved by its determinant.
  have hD : (Matrix.diagonal (fun i : Fin m => (length Q g i.val)⁻¹)).PosDef :=
    Matrix.PosDef.diagonal (fun i => inv_pos.mpr ((invariant_line_pos Q hpos g i.val
      (invariant Q hQ hpos g i.val (fun k hk => hg k (hk.trans i.isLt))) (hg i.val i.isLt)).2.1))
  have hdet : (lowerFactor Q g m).det=1 := by
    rw [Matrix.det_of_isLowerTriangular _ (lowerFactor_triangular Q g m).1]
    simp only [(lowerFactor_triangular Q g m).2, Finset.prod_const_one]
  have hB : Function.Injective ((lowerFactor Q g m)ᵀ).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (by rw [Matrix.det_transpose, hdet]; exact isUnit_one))
  have hp := hD.conjTranspose_mul_mul_same (B := (lowerFactor Q g m)ᵀ) hB
  rw [lanczosMatrix_ldl Q hQ hpos g m hg]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hp

end
end krylov.Reference.CG
