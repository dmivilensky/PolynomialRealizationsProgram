import krylov.Envelope.AbsorbedCompression
import krylov.LinearAlgebra.NuclearSupport

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:DK, true canonical projection matrices.
Use: identify the source complementary canonical flag projector matrices
with their genuine actual orthogonal projection operators and transfer
real absorbed Frobenius functionals to the printed compressed target matrices.
Source: actual finite matrix/operator equivalence, standard true
orthogonal projection symmetry and idempotence, and real cyclic trace identities.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.LinearAlgebra Matrix
open scoped Matrix.Norms.L2Operator BigOperators
variable {n : ℕ}

/-- The genuine finite matrix of the true complementary canonical CG flag projector.
Use: The genuine finite matrix of the true complementary canonical CG flag projector.
Article: main_krylov, thm:select and apB:lem:DK, true canonical projection matrices.
Proof: Recover the real finite matrix of the actual orthogonal projection through the genuine matrix/operator equivalence. -/
def canonicalComplementMatrix (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (l : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.symm ((exploredFlag base g (l+1))ᗮ.starProjection)

/-- The actual complementary canonical projector matrix acts exactly as its genuine true orthogonal projection.
Use: The actual complementary canonical projector matrix acts exactly as its genuine true orthogonal projection.
Article: main_krylov, thm:select and apB:lem:DK, true canonical projection matrices.
Proof: Cancel the real matrix/operator equivalence. -/
theorem canonicalComplementMatrix_operator (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (l : ℕ) :
    cgOperator (canonicalComplementMatrix base g l)=(exploredFlag base g (l+1))ᗮ.starProjection :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.apply_symm_apply _

/-- The genuine complementary canonical projector matrix is actually symmetric.
Use: The genuine complementary canonical projector matrix is actually symmetric.
Article: main_krylov, thm:select and apB:lem:DK, true canonical projection matrices.
Proof: Transfer the true orthogonal projector inner-product symmetry through the actual finite matrix/operator identification. -/
theorem canonicalComplementMatrix_symm (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (l : ℕ) :
    (canonicalComplementMatrix base g l).IsSymm := by
  apply Matrix.isHermitian_iff_isSymm.mp
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  change (cgOperator (canonicalComplementMatrix base g l)).toLinearMap.IsSymmetric
  rw [canonicalComplementMatrix_operator]
  exact (exploredFlag base g (l+1))ᗮ.starProjection_isSymmetric

/-- The actual complementary canonical projector matrix is genuinely idempotent.
Use: The actual complementary canonical projector matrix is genuinely idempotent.
Article: main_krylov, thm:select and apB:lem:DK, true canonical projection matrices.
Proof: Transfer the real orthogonal projector idempotence through the true multiplicative matrix/operator equivalence. -/
theorem canonicalComplementMatrix_idempotent (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (l : ℕ) :
    canonicalComplementMatrix base g l*canonicalComplementMatrix base g l=canonicalComplementMatrix base g l := by
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective
  rw [map_mul]
  change cgOperator (canonicalComplementMatrix base g l)*cgOperator (canonicalComplementMatrix base g l)=cgOperator (canonicalComplementMatrix base g l)
  rw [canonicalComplementMatrix_operator]
  exact (exploredFlag base g (l+1))ᗮ.isIdempotentElem_starProjection

/-- Actual absorbed canonical increments are exactly the genuine printed two-sided complementary-projector matrix compressions.
Use: Actual absorbed canonical increments are exactly the genuine printed two-sided complementary-projector matrix compressions.
Article: main_krylov, thm:select and apB:lem:DK, true canonical projection matrices.
Proof: The real matrix/operator identification preserves true products and the actual absorbed projector action. -/
theorem absorbedIncrements_matrix (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    absorbedIncrements base g E l=canonicalComplementMatrix base g l*E l*canonicalComplementMatrix base g l := by
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective
  change cgOperator (absorbedIncrements base g E l)=_
  rw [absorbedIncrements_operator,map_mul,map_mul]
  change _=cgOperator (canonicalComplementMatrix base g l)*cgOperator (E l)*cgOperator (canonicalComplementMatrix base g l)
  rw [canonicalComplementMatrix_operator]
  rfl

/-- The genuine actual absorbed increment trace functional equals the true original increment functional on its actual compressed target.
Use: The genuine actual absorbed increment trace functional equals the true original increment functional on its actual compressed target.
Article: main_krylov, thm:select and apB:lem:DK, true canonical projection matrices.
Proof: Use the real two-sided projector compression and standard genuine cyclic trace invariance. -/
theorem absorbedIncrements_trace_pairing (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ) (Z : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (absorbedIncrements base g E l*Z)=
      Matrix.trace (E l*(canonicalComplementMatrix base g l*Z*canonicalComplementMatrix base g l)) := by
  rw [absorbedIncrements_matrix]
  let P := canonicalComplementMatrix base g l
  change Matrix.trace (P*E l*P*Z)=Matrix.trace (E l*(P*Z*P))
  rw [Matrix.mul_assoc P (E l) P,Matrix.mul_assoc P (E l*P) Z,Matrix.trace_mul_comm P]
  simp only [Matrix.mul_assoc]
/-- A genuine symmetric real matrix has its actual Frobenius functional equal to the true product trace.
Use: A genuine symmetric real matrix has its actual Frobenius functional equal to the true product trace.
Article: main_krylov, thm:select and apB:lem:DK, true canonical projection matrices.
Proof: Expand the actual real finite entry pairing, swap true finite indices and use genuine matrix symmetry. -/
theorem symmetric_frobenius_trace (E Z : Matrix (Fin n) (Fin n) ℝ) (hE : E.IsSymm) :
    inner ℝ (frobeniusVector E) (frobeniusVector Z)=Matrix.trace (E*Z) := by
  -- Genuine symmetry identifies the actual finite entry pairing with the true product trace after exchanging real indices.
  rw [inner_frobeniusVector]
  change (∑ i, ∑ j, E i j*Z i j)=∑ i, ∑ j, E i j*Z j i
  rw [Finset.sum_comm (f := fun i j => E i j*Z j i)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : E j i=E i j := congrFun (congrFun hE.eq i) j
  rw [he]

/-- The genuine Frobenius functional of actual absorbed symmetric increments is the true original-increment functional on the printed real compressed target matrix.
Use: The genuine Frobenius functional of actual absorbed symmetric increments is the true original-increment functional on the printed real compressed target matrix.
Article: main_krylov, thm:select and apB:lem:DK, true canonical projection matrices.
Proof: Transfer the actual symmetric Frobenius pairings to real traces, apply genuine cyclic absorbed compression and return to the true Frobenius functional. -/
theorem absorbedIncrements_frobenius_pairing (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ) (hE : (E l).IsSymm) (Z : Matrix (Fin n) (Fin n) ℝ) :
    inner ℝ (frobeniusVector (absorbedIncrements base g E l)) (frobeniusVector Z)=
      inner ℝ (frobeniusVector (E l))
        (frobeniusVector (canonicalComplementMatrix base g l*Z*canonicalComplementMatrix base g l)) := by
  rw [symmetric_frobenius_trace _ _ (absorbedIncrements_symm base g E l hE),
    absorbedIncrements_trace_pairing,symmetric_frobenius_trace _ _ hE]

end
end krylov.Envelope
