import «2610.05164v2».Green.LiftIdentities
import «2610.05164v2».Green.Contractivity

/-!
Article: 2610.05164v2, Theorem A.1.
Lift Contractivity.
Result: `«2610.05164v2».Jacobi.lift_contractive` supplies the stated article conclusion.
-/
namespace «2610.05164v2».Centering
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

/--
The precise assertion is `(1-blockLift B).PosDef`.

Use: `«2610.05164v2».Centering.blockLift_pencils` uses this assertion to establish the precise
assertion is `(1-blockLift B).PosDef ∧ (1+blockLift B).PosDef`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.lift_contractive`.

Proof: Use the identities/estimates `«2610.05164v2».Centering.blockLift_pencil` with the
arguments shown in the proof.
-/
theorem blockLift_posDef (B : Matrix (Fin N) (Fin N) ℝ) (h : (1-B*Bᵀ).PosDef) :
    (1-blockLift B).PosDef := by
  -- Use the identities/estimates `«2610.05164v2».Centering.blockLift_pencil` with the
  -- arguments shown in the proof.
  let : Invertible (1 : Matrix (Fin N) (Fin N) ℝ) := invertibleOne
  have hp : (fromBlocks 1 (-B) (-Bᵀ) 1).PosSemidef := by
    have hh := Matrix.PosDef.fromBlocks₂₂ (1 : Matrix (Fin N) (Fin N) ℝ)
      (-B) (Matrix.PosDef.one : (1 : Matrix (Fin N) (Fin N) ℝ).PosDef)
    simpa using hh.mpr (by simpa using h.posSemidef)
  have hd : (fromBlocks 1 (-B) (-Bᵀ) 1).det ≠ 0 := by
    simpa using h.det_pos.ne'
  have hh := hp.posDef_iff_det_ne_zero.mpr hd
  have he := blockLift_pencil B 1
  simp only [one_smul] at he
  rw [he]; exact hh

/--
The precise assertion is `(1-blockLift B).PosDef ∧ (1+blockLift B).PosDef`.

Use: `«2610.05164v2».Jacobi.lift_pencils` uses this assertion to establish the precise
assertion is `(1-J.lift.matrix).PosDef ∧ (1+J.lift.matrix).PosDef`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.lift_contractive`.

Proof: Use the identities/estimates `«2610.05164v2».Centering.blockLift_posDef` with the
arguments shown in the proof.
-/
theorem blockLift_pencils (B : Matrix (Fin N) (Fin N) ℝ) (h : (1-B*Bᵀ).PosDef) :
    (1-blockLift B).PosDef ∧ (1+blockLift B).PosDef := by
  refine ⟨blockLift_posDef B h, ?_⟩
  have hn : blockLift (-B) = -blockLift B := by
    ext i j; cases i <;> cases j <;> simp [blockLift, Matrix.fromBlocks]
  have hh := blockLift_posDef (-B) (by simpa using h)
  simpa [hn] using hh

end
end «2610.05164v2».Centering

namespace «2610.05164v2».Jacobi
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
The precise assertion is `(1-J.lift.matrix).PosDef ∧ (1+J.lift.matrix).PosDef`.

Use: `«2610.05164v2».Jacobi.lift_contractive` uses this assertion to establish the stated
quantitative bound `«2606.16671v2».opNorm J.lift.matrix < 1`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.lift_contractive`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.cholesky_factor`,
`«2610.05164v2».Centering.blockLift_pencils`, `«2610.05164v2».Jacobi.lift_grouped_matrix` with
the arguments shown in the proof.
-/
theorem lift_pencils (h : (1+J.matrix).PosDef) (hm : (1-J.matrix).PosDef) :
    (1-J.lift.matrix).PosDef ∧ (1+J.lift.matrix).PosDef := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.cholesky_factor`,
  -- `«2610.05164v2».Centering.blockLift_pencils`, `«2610.05164v2».Jacobi.lift_grouped_matrix`
  -- with the arguments shown in the proof.
  have hs : 1-J.cholesky*J.choleskyᵀ = (1/2:ℝ) • (1-J.matrix) := by
    rw [J.cholesky_factor h]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hp : (1-J.cholesky*J.choleskyᵀ).PosDef := by rw [hs]; exact hm.smul (by norm_num)
  obtain ⟨hn, hp⟩ := Centering.blockLift_pencils J.cholesky hp
  have he : (1-J.lift.matrix).submatrix (Centering.interleave N) (Centering.interleave N) =
      1-Centering.blockLift J.cholesky := by
    simp only [Matrix.submatrix_sub, Pi.sub_apply]
    rw [Matrix.submatrix_one _ (Centering.interleave N).injective, J.lift_grouped_matrix]
  have he' : (1+J.lift.matrix).submatrix (Centering.interleave N) (Centering.interleave N) =
      1+Centering.blockLift J.cholesky := by
    simp only [Matrix.submatrix_add, Pi.add_apply]
    rw [Matrix.submatrix_one _ (Centering.interleave N).injective, J.lift_grouped_matrix]
  rw [← he] at hn
  rw [← he'] at hp
  have hr (A : Matrix (Fin (2*N)) (Fin (2*N)) ℝ) :
      (A.submatrix (Centering.interleave N) (Centering.interleave N)).submatrix
        (Centering.interleave N).symm (Centering.interleave N).symm = A := by
    ext i j
    change A ((Centering.interleave N) ((Centering.interleave N).symm i))
      ((Centering.interleave N) ((Centering.interleave N).symm j)) = A i j
    simp
  constructor
  · have hh := hn.submatrix (Centering.interleave N).symm.injective
    rw [hr] at hh; exact hh
  · have hh := hp.submatrix (Centering.interleave N).symm.injective
    rw [hr] at hh; exact hh

/--
The stated quantitative bound `«2606.16671v2».opNorm J.lift.matrix < 1`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem A.1.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.pencils_of_contractive`,
`«2610.05164v2».Jacobi.lift_pencils`, `«2610.05164v2».Jacobi.contractive_of_pencils` with the
arguments shown in the proof.
-/
theorem lift_contractive (h : «2606.16671v2».opNorm J.matrix < 1) : «2606.16671v2».opNorm J.lift.matrix < 1 := by
  obtain ⟨hm,hp⟩ := J.pencils_of_contractive h
  obtain ⟨hm',hp'⟩ := J.lift_pencils hp hm
  exact J.lift.contractive_of_pencils hm' hp'

end
end «2610.05164v2».Jacobi
