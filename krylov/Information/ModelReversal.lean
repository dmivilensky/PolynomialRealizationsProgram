import krylov.Information.CommonTerminal

/-!
Article: main_krylov, s4:cor-Q, common physical latest-information centre.
Use: Exact reversal from actual newest-first pair storage to chronological latest information.
Source: true matrix congruence, finite permutation identities and the
existing physical inverse-congruence and observed-compression theorems.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- Each actual chronological observed pairing entry is the true physical query-image inner product.
Use: Identify the real recorded pairings with the chronological observation matrix.
Article: main_krylov, s4:cor-Q, actual common physical centre.
Proof: Use the observed-compression column identity and the true Euclidean matrix pairing. -/
theorem observedPairMatrix_entry (u : Fin (N+1) → EuclideanSpace ℝ (Fin (N+1)))
    (A : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i j : Fin (N+1)) :
    ((fullBasisMatrix u)ᵀ*pairImages (fullBasisMatrix u) A) i j=
      inner ℝ (u i) (cgOperator (A j.val) (u j)) := by
  rw [← observed_compression]
  change ((fullBasisMatrix u)ᵀ*A j.val*fullBasisMatrix u) i j=_
  exact compressed_entry_pairing _ _ _ _

/-- The actual newest-first pair model is exactly the reversed chronological latest-information model.
Use: Retain the true native storage order in the common-centre RFC solve.
Article: main_krylov, s4:cor-Q, actual common physical centre.
Proof: Reversal interchanges the two ordered index extremes; the actual observed column identity then identifies both physical pairings. -/
theorem pairModel_reverse_observations (u : Fin (N+1) → EuclideanSpace ℝ (Fin (N+1)))
    (A : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    pairModel (fun i => u i.rev) (fun i => cgOperator (A i.rev.val) (u i.rev))=
      (latest ((fullBasisMatrix u)ᵀ*pairImages (fullBasisMatrix u) A)).submatrix Fin.rev Fin.rev := by
  ext i j
  simp only [pairModel,Matrix.submatrix_apply,latest,observedPairMatrix_entry]
  rcases le_total i j with hij | hji
  · have hr : j.rev ≤ i.rev := Fin.rev_le_rev.mpr hij
    simp only [max_eq_right hij,min_eq_left hij,min_eq_right hr,max_eq_left hr]
  · have hr : i.rev ≤ j.rev := Fin.rev_le_rev.mpr hji
    simp only [max_eq_left hji,min_eq_right hji,min_eq_left hr,max_eq_right hr]

end
end krylov.Information
