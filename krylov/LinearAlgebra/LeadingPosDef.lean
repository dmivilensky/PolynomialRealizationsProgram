import krylov.LinearAlgebra.SchurDeterminant
import Mathlib.Analysis.Matrix.Order

/-!
Article: main_krylov, prop:deep, genuine positive correction models.
Use: Deduce actual positive definiteness from the original certified leading
principal determinants, including the positive side of the final singularity.
Source: Sylvester's criterion; standard Schur-complement determinant and
positivity identities, mathlib Matrix.PosDef.fromBlocks₁₁ and
Matrix.PosSemidef.posDef_iff_det_ne_zero. The source proof derives the criterion.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix

/-- A positive leading block and strictly positive whole determinant give a genuinely positive real symmetric scalar-bordered matrix.
Use: Convert exact original correction-model determinant certificates into genuine matrix positivity.
Article: main_krylov, prop:deep, source correction-model positivity.
Proof: Use the standard genuine Schur determinant factorization and positive scalar Schur complement; iterate over the exact leading blocks.
-/
theorem scalar_border_posDef {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (B : Matrix n (Fin 1) ℝ) (D : Matrix (Fin 1) (Fin 1) ℝ)
    (hA : A.PosDef) (hd : 0<(Matrix.fromBlocks A B Bᴴ D).det) :
    (Matrix.fromBlocks A B Bᴴ D).PosDef := by
  -- The original determinant factorization makes the one-dimensional Schur complement positive; its true block criterion gives positive semidefiniteness and nonsingularity upgrades it.
  let : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have he := block_schur_det A B Bᴴ D (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hs : 0<(D-Bᴴ*A⁻¹*B).det := by rw [he] at hd; exact pos_of_mul_pos_right hd hA.det_pos.le
  have hp : (D-Bᴴ*A⁻¹*B).PosSemidef := by
    have hdiag : D-Bᴴ*A⁻¹*B=diagonal (fun _ : Fin 1 => (D-Bᴴ*A⁻¹*B) 0 0) := by
      ext i j
      fin_cases i; fin_cases j
      simp
    rw [Matrix.det_fin_one] at hs
    rw [hdiag]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun _ => hs.le)
  have hw := (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr hp
  exact hw.posDef_iff_det_ne_zero.mpr hd.ne'


/-- An actual real Hermitian matrix with positive leading predecessor block and positive determinant is positive definite.
Use: Convert exact original correction-model determinant certificates into genuine matrix positivity.
Article: main_krylov, prop:deep, source correction-model positivity.
Proof: Use the standard genuine Schur determinant factorization and positive scalar Schur complement; iterate over the exact leading blocks.
-/
theorem leading_border_posDef {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hM : M.IsHermitian) (hA : (M.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hd : 0<M.det) : M.PosDef := by
  -- Reindex the genuine final coordinate as a scalar border, preserving the original leading block and whole determinant.
  let e : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
  let N := M.submatrix e e
  let A := N.submatrix Sum.inl Sum.inl
  let B := N.submatrix Sum.inl Sum.inr
  let D := N.submatrix Sum.inr Sum.inr
  have hN : N.IsHermitian := hM.submatrix e
  have he : N=Matrix.fromBlocks A B Bᴴ D := by
    ext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => exact (hN.apply (Sum.inr i) (Sum.inl j)).symm
      | inr j => rfl
  have hAp : A.PosDef := by
    change (M.submatrix (fun i => finSumFinEquiv (Sum.inl i)) (fun i => finSumFinEquiv (Sum.inl i))).PosDef
    have he : (fun i : Fin n => (finSumFinEquiv (Sum.inl i) : Fin (n+1)))=Fin.castSucc := by
      funext i
      apply Fin.ext
      rfl
    rw [he]
    exact hA
  have hNd : 0<N.det := by simpa only [N,Matrix.det_submatrix_equiv_self] using hd
  rw [he] at hNd
  have hp := scalar_border_posDef A B D hAp hNd
  rw [← he] at hp
  have hback := hp.submatrix e.symm.injective
  simpa [N] using hback


/-- The genuine leading principal block of its original finite real matrix.
Use: Convert exact original correction-model determinant certificates into genuine matrix positivity.
Article: main_krylov, prop:deep, source correction-model positivity.
-/
def leadingBlock {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (hk : k≤n) :
    Matrix (Fin k) (Fin k) ℝ := M.submatrix (Fin.castLE hk) (Fin.castLE hk)

/-- The genuine leading block at the complete original dimension is the original matrix itself.
Use: Recover the true whole determinant as the last leading principal determinant.
Article: main_krylov, prop:deep, source correction-model positivity.
Proof: Both actual finite coordinate inclusions preserve every original index. -/
theorem leadingBlock_full {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hn : n≤n) :
    leadingBlock M n hn=M := by ext i j; rfl

/-- Sylvester's criterion: a real Hermitian matrix with all strictly positive genuine leading principal determinants is positive definite, including the empty case.
Use: Convert exact original correction-model determinant certificates into genuine matrix positivity.
Article: main_krylov, prop:deep, source correction-model positivity.
Proof: Use the standard genuine Schur determinant factorization and positive scalar Schur complement; iterate over the exact leading blocks.
-/
theorem posDef_of_leading_determinants {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian)
    (hpos : ∀ k, 0<k → ∀ hk : k≤n, 0<(leadingBlock M k hk).det) : M.PosDef := by
  -- Remove the actual last coordinate and inherit every shorter leading determinant before restoring the positive scalar border.
  induction n with
  | zero =>
    have he : M=1 := Subsingleton.elim _ _
    rw [he]
    exact Matrix.PosDef.one
  | succ n ih =>
    apply leading_border_posDef M hM
    · apply ih (M.submatrix Fin.castSucc Fin.castSucc) (hM.submatrix _)
      intro k hk hkn
      have he : leadingBlock (M.submatrix Fin.castSucc Fin.castSucc) k hkn=
          leadingBlock M k (hkn.trans (Nat.le_succ n)) := by ext i j; rfl
      rw [he]
      exact hpos k hk _
    · have he : leadingBlock M (n+1) le_rfl=M := by ext i j; rfl
      rw [← he]
      exact hpos (n+1) (by omega) _

end
end krylov.LinearAlgebra
