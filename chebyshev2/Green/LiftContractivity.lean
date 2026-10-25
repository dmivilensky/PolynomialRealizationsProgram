import chebyshev2.Green.LiftIdentities
import chebyshev2.Green.Contractivity

/-!
Article: chebyshev2, Theorem A.1.
Lift Contractivity.
Result: `chebyshev2.Jacobi.lift_contractive` supplies the stated article conclusion.
-/
namespace chebyshev2.Centering
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

/--
The precise assertion is `(1-blockLift B).PosDef`.

Use: `chebyshev2.Centering.blockLift_pencils` uses this assertion to establish the precise
assertion is `(1-blockLift B).PosDef ∧ (1+blockLift B).PosDef`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_contractive`.

Proof: Use the identities/estimates `chebyshev2.Centering.blockLift_pencil` with the
arguments shown in the proof.
-/
theorem blockLift_posDef (B : Matrix (Fin N) (Fin N) ℝ) (h : (1-B*Bᵀ).PosDef) :
    (1-blockLift B).PosDef := by
  -- Use the identities/estimates `chebyshev2.Centering.blockLift_pencil` with the
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

Use: `chebyshev2.Jacobi.lift_pencils` uses this assertion to establish the precise
assertion is `(1-J.lift.matrix).PosDef ∧ (1+J.lift.matrix).PosDef`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_contractive`.

Proof: Use the identities/estimates `chebyshev2.Centering.blockLift_posDef` with the
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
end chebyshev2.Centering

namespace chebyshev2.Jacobi
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
The precise assertion is `(1-J.lift.matrix).PosDef ∧ (1+J.lift.matrix).PosDef`.

Use: `chebyshev2.Jacobi.lift_contractive` uses this assertion to establish the stated
quantitative bound `chebyshev1.opNorm J.lift.matrix < 1`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_contractive`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.cholesky_factor`,
`chebyshev2.Centering.blockLift_pencils`, `chebyshev2.Jacobi.lift_grouped_matrix` with
the arguments shown in the proof.
-/
theorem lift_pencils (h : (1+J.matrix).PosDef) (hm : (1-J.matrix).PosDef) :
    (1-J.lift.matrix).PosDef ∧ (1+J.lift.matrix).PosDef := by
  -- Use the identities/estimates `chebyshev2.Jacobi.cholesky_factor`,
  -- `chebyshev2.Centering.blockLift_pencils`, `chebyshev2.Jacobi.lift_grouped_matrix`
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
The stated quantitative bound `chebyshev1.opNorm J.lift.matrix < 1`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem A.1.

Proof: Use the identities/estimates `chebyshev2.Jacobi.pencils_of_contractive`,
`chebyshev2.Jacobi.lift_pencils`, `chebyshev2.Jacobi.contractive_of_pencils` with the
arguments shown in the proof.
-/
theorem lift_contractive (h : chebyshev1.opNorm J.matrix < 1) : chebyshev1.opNorm J.lift.matrix < 1 := by
  obtain ⟨hm,hp⟩ := J.pencils_of_contractive h
  obtain ⟨hm',hp'⟩ := J.lift_pencils hp hm
  exact J.lift.contractive_of_pencils hm' hp'

end
end chebyshev2.Jacobi
