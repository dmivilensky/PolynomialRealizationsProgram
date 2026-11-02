import krylov.Information.CommonTerminal
import krylov.Correction.DiagonalModelChange
import krylov.Secant.NormalizedModel

/-!
Article: main_krylov, s4:cor-Q, common physical latest-information centre.
Use: Actual physical latest-information centres and their query-scale invariance.
Source: true matrix congruence, finite permutation identities and the
existing physical inverse-congruence and observed-compression theorems.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The physical latest-information centre in a genuine chronological direction basis.
Use: Compare true observed centres after changing individual physical query scales.
Article: main_krylov, s4:cor-Q, actual common physical centre. -/
def observedPhysicalCentre (D : Matrix (Fin n) (Fin n) ℝ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := inverseCongruence D (latest (Dᵀ*pairImages D A))

/-- Observed chronological query images have the same actual right diagonal column scaling as the query basis.
Use: Transport true observations under individual nonzero query rescalings.
Article: main_krylov, s4:cor-Q, actual common physical centre.
Proof: Expand each true chronological image column and its diagonal factor. -/
theorem pairImages_right_rescale (D : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) :
    pairImages (D*diagonal s) A=pairImages D A*diagonal s := by
  ext i j
  simp only [pairImages,← Matrix.mul_assoc,Matrix.mul_diagonal]

/-- The actual physical observed centre is unchanged by any nonsingular diagonal column scaling.
Use: Cancel the real CG step lengths when identifying the native RFC model.
Article: main_krylov, s4:cor-Q, actual common physical centre.
Proof: The actual observed pairing matrix transforms by diagonal congruence. The latest-information symmetrization respects that congruence, and the physical inverse congruence cancels the same true diagonal factors. -/
theorem observedPhysicalCentre_rescale (D : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) (hs : IsUnit (diagonal s).det) :
    observedPhysicalCentre (D*diagonal s) A=observedPhysicalCentre D A := by
  have hc : (D*diagonal s)ᵀ*pairImages (D*diagonal s) A=
      diagonal s*(Dᵀ*pairImages D A)*diagonal s := by
    rw [pairImages_right_rescale,transpose_mul,diagonal_transpose]
    noncomm_ring
  unfold observedPhysicalCentre
  rw [hc,latest_diagonal_congruence]
  exact inverseCongruence_right_rescale D _ s hs

/-- Simultaneously permuting a full physical basis and both coefficient-model indices leaves its physical form unchanged.
Use: Reverse the actual newest-first stored model into chronological observation coordinates.
Article: main_krylov, s4:cor-Q, actual common physical centre.
Proof: The nonsingular-inverse reindexing identity and finite equivalence sums cancel the two genuine internal index permutations. -/
theorem inverseCongruence_reindex (D H : Matrix (Fin n) (Fin n) ℝ) (e : Equiv.Perm (Fin n)) :
    inverseCongruence (D.submatrix id e) (H.submatrix e e)=inverseCongruence D H := by
  simp only [inverseCongruence,transpose_submatrix]
  change (Dᵀ.submatrix e (Equiv.refl (Fin n)))⁻¹ * H.submatrix e e *
    (D.submatrix (Equiv.refl (Fin n)) e)⁻¹=_
  rw [inv_submatrix_equiv,inv_submatrix_equiv]
  rw [submatrix_mul_equiv,submatrix_mul_equiv]
  rfl

end
end krylov.Information
