import krylov.LinearAlgebra.Pseudoinverse
import Mathlib.Tactic.NoncommRing

/-!
Article: main_krylov, apA:galerkin(f), generalized Schur completion.
Use: retain singular endpoint blocks through a solved range equation instead
of silently replacing their inverse by a nonsingular inverse.
Source: Albert69, generalized Schur criterion; the factorization is proved here.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped Matrix MatrixOrder
variable {n p : ℕ}

/-- A block diagonal form is positive semidefinite when both actual blocks are.
Use: the positive diagonal factor in the generalized Schur congruence.
Article: main_krylov, apA:galerkin(f).
Proof: its quadratic form splits into the two nonnegative block forms. -/
theorem blockDiagonal_posSemidef (Y : Matrix (Fin p) (Fin p) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hY : Y.PosSemidef) (hA : A.PosSemidef) :
    (fromBlocks Y 0 0 A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.IsHermitian.fromBlocks hY.1 (by simp) hA.1)
  intro v
  have h := add_nonneg (hY.dotProduct_mulVec_nonneg (v ∘ Sum.inl))
    (hA.dotProduct_mulVec_nonneg (v ∘ Sum.inr))
  simpa only [star_trivial, fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply] using h

/-- The exact lower-triangular congruence for a solved cross-block range equation.
Use: no inverse or strict positivity of A is required for this factorization.
Article: main_krylov, apA:galerkin(f), generalized Schur complement.
Proof: multiply the block matrices and use AZ=X and its transposed equation. -/
theorem schur_factorization (Y : Matrix (Fin p) (Fin p) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (X Z : Matrix (Fin n) (Fin p) ℝ) (hAZ : A * Z = X) :
    (fromBlocks (1 : Matrix (Fin p) (Fin p) ℝ) 0 Z 1)ᵀ *
      fromBlocks (Y - Xᵀ * Z) 0 0 A * fromBlocks 1 0 Z 1 = fromBlocks Y Xᵀ X A := by
  have hZA : Zᵀ * A = Xᵀ := by
    simpa only [transpose_mul, hA.eq] using congrArg Matrix.transpose hAZ
  simp only [fromBlocks_transpose, transpose_one, transpose_zero, fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    hAZ, hZA, sub_add_cancel]

/-- The Schur complement is positive exactly when the completed block is positive,
provided the stated range equation is actually solved.
Use: the singular criterion after constructing Z=A⁺X from the range condition.
Article: main_krylov, apA:galerkin(f), the positive-semidefinite Schur equivalence.
Proof: a lower shear gives the forward compressed form; the inverse congruence
factorization gives the converse from the two positive diagonal blocks. -/
theorem schur_iff_of_range_solution (Y : Matrix (Fin p) (Fin p) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (X Z : Matrix (Fin n) (Fin p) ℝ) (hAZ : A * Z = X) :
    (fromBlocks Y Xᵀ X A).PosSemidef ↔ (Y - Xᵀ * Z).PosSemidef := by
  constructor
  · intro h
    -- Test the original form on (u,−Zu), the exact minimizing lower-block lift.
    let C : Matrix (Fin p ⊕ Fin n) (Fin p ⊕ Fin n) ℝ := fromBlocks 1 0 (-Z) 1
    have hc := h.conjTranspose_mul_mul_same C
    have hZA : Zᵀ * A = Xᵀ := by
      simpa only [transpose_mul, hA.1.isSymm.eq] using congrArg Matrix.transpose hAZ
    have hZX : Zᵀ * X = Xᵀ * Z := by
      conv_lhs => rw [← hAZ]
      rw [← Matrix.mul_assoc, hZA]
    have he : Cᵀ * fromBlocks Y Xᵀ X A * C = fromBlocks (Y - Xᵀ * Z) 0 0 A := by
      simp only [C, fromBlocks_transpose, transpose_one, transpose_zero, transpose_neg,
        fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
        Matrix.mul_zero, Matrix.mul_neg, Matrix.neg_mul, hZA, hAZ, hZX,
        add_neg_cancel, neg_zero, zero_add, add_zero, sub_eq_add_neg]
    have hp := hc.submatrix (Sum.inl : Fin p → Fin p ⊕ Fin n)
    have hsub : (fromBlocks (Y - Xᵀ * Z) 0 0 A).submatrix
        (Sum.inl : Fin p → Fin p ⊕ Fin n) Sum.inl = Y - Xᵀ * Z := by ext i j; rfl
    simpa only [conjTranspose_eq_transpose_of_trivial, he, hsub] using hp
  · intro h
    have hdiag := blockDiagonal_posSemidef (Y - Xᵀ * Z) A h hA
    have h := hdiag.conjTranspose_mul_mul_same
      (fromBlocks (1 : Matrix (Fin p) (Fin p) ℝ) 0 Z (1 : Matrix (Fin n) (Fin n) ℝ))
    simpa only [conjTranspose_eq_transpose_of_trivial,
      schur_factorization Y A hA.1.isSymm X Z hAZ] using h

/-- A null vector of a positive block diagonal corner annihilates the cross block.
Use: prove necessity of the singular range condition instead of imposing it as an axiom.
Article: main_krylov, apA:galerkin(f), null-direction argument.
Proof: the lifted vector (0,v) has zero quadratic form; positive semidefiniteness
forces its full block action, including the cross action, to vanish. -/
theorem block_kernel_cross (Y : Matrix (Fin p) (Fin p) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (X : Matrix (Fin n) (Fin p) ℝ)
    (h : (fromBlocks Y Xᵀ X A).PosSemidef) (v : Fin n → ℝ) (hv : A *ᵥ v = 0) :
    Xᵀ *ᵥ v = 0 := by
  -- A zero lower-block quadratic form forces the complete lifted block action to vanish.
  let w : Fin p ⊕ Fin n → ℝ := Sum.elim 0 v
  have hq : star w ⬝ᵥ (fromBlocks Y Xᵀ X A *ᵥ w) = 0 := by
    rw [star_trivial, dotProduct_block, fromBlocks_mulVec]
    change 0 ⬝ᵥ (Y *ᵥ 0 + Xᵀ *ᵥ v) + v ⬝ᵥ (X *ᵥ 0 + A *ᵥ v) = 0
    simp [hv]
  have hz := h.dotProduct_mulVec_zero_iff.mp hq
  ext i
  have hi := congrFun hz (Sum.inl i)
  rw [fromBlocks_mulVec] at hi
  change (Y *ᵥ 0 + Xᵀ *ᵥ v) i = 0 at hi
  simpa only [Matrix.mulVec_zero, zero_add, Pi.zero_apply] using hi

/-- A positive-semidefinite completed block necessarily has compatible cross-block range.
Use: singular endpoint feasibility includes the actual range condition.
Article: main_krylov, apA:galerkin(f), ran X ⊆ ran A.
Proof: the kernel projector I−AA⁺ consists of null directions; its cross action
vanishes, and symmetry turns that equation into AA⁺X=X. -/
theorem block_range_necessary (Y : Matrix (Fin p) (Fin p) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (X : Matrix (Fin n) (Fin p) ℝ) (h : (fromBlocks Y Xᵀ X A).PosSemidef) :
    LinearMap.range X.mulVecLin ≤ LinearMap.range A.mulVecLin := by
  -- Test the full block on every direction in the explicit complementary kernel projector.
  let B := chebyshev1.SpectralBasis.ofHermitian A hA.1
  let Q := 1 - A * pseudoinverseInBasis B
  have hQ : Q.IsSymm := by
    simp only [Q, Matrix.IsSymm, transpose_sub, transpose_one,
      (pseudoinverse_projector_isSymm B hA.1.isSymm).eq]
  have hAQ : A * Q = 0 := pseudoinverse_kernel_projector B
  have hXQ : Xᵀ * Q = 0 := by
    ext i j
    have hv : A *ᵥ (Q *ᵥ Pi.single j 1) = 0 := by
      rw [mulVec_mulVec, hAQ, Matrix.zero_mulVec]
    have hi := congrFun (block_kernel_cross Y A X h _ hv) i
    rw [mulVec_mulVec, Matrix.mulVec_single, op_smul_eq_smul, one_smul] at hi
    exact hi
  have hQX : Q * X = 0 := by
    have ht := congrArg Matrix.transpose hXQ
    simpa only [transpose_mul, hQ.eq, transpose_transpose, transpose_zero] using ht
  apply (pseudoinverse_range_iff B X).mpr
  change (1 - A * pseudoinverseInBasis B) * X = 0 at hQX
  rw [Matrix.sub_mul, Matrix.one_mul] at hQX
  exact (sub_eq_zero.mp hQX).symm

/-- The full generalized Schur criterion with the actual Moore--Penrose inverse.
Use: includes singular blocks, both directions and the necessary range condition.
Article: main_krylov, apA:galerkin(f), generalized positive-semidefinite completion.
Source: Albert69; the singular range and factorization proofs above discharge every premise.
Proof: lift X by A⁺ exactly on its proved range, then apply the exact shear criterion. -/
theorem generalized_schur_iff (Y : Matrix (Fin p) (Fin p) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (X : Matrix (Fin n) (Fin p) ℝ) :
    (fromBlocks Y Xᵀ X A).PosSemidef ↔
      (LinearMap.range X.mulVecLin ≤ LinearMap.range A.mulVecLin) ∧
      (Y - Xᵀ * pseudoinverse A hA.1 * X).PosSemidef := by
  -- Range compatibility supplies the actual solved lift A⁺X in both directions.
  let B := chebyshev1.SpectralBasis.ofHermitian A hA.1
  constructor
  · intro h
    have hr := block_range_necessary Y A hA X h
    refine ⟨hr, ?_⟩
    have hs := (schur_iff_of_range_solution Y A hA X
      (pseudoinverseInBasis B * X)
      (by simpa only [Matrix.mul_assoc] using (pseudoinverse_range_iff B X).mp hr)).mp h
    simpa only [pseudoinverse, Matrix.mul_assoc] using hs
  · rintro ⟨hr, hs⟩
    apply (schur_iff_of_range_solution Y A hA X (pseudoinverseInBasis B * X)
      (by simpa only [Matrix.mul_assoc] using (pseudoinverse_range_iff B X).mp hr)).mpr
    simpa only [pseudoinverse, Matrix.mul_assoc] using hs

end
end krylov.LinearAlgebra
