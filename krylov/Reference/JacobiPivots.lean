import krylov.Reference.JacobiSequence
import krylov.Realization.RawCGCoefficients
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), measured Jacobi pivot recurrence.
Use: recover common finite-CG coefficients and their scalar LDL recurrence directly from the original principal determinants.
Source: the existing raw-matrix CG dictionary, leading-block coherence and tridiagonal LDL diagonal identity.
-/

namespace krylov.Reference
noncomputable section
open krylov.Realization Matrix

/-- The leading determinant ratio of the original Jacobi sequence.
Use: The leading determinant ratio of the original Jacobi sequence.
Article: main_krylov, prop:phi(c), measured Jacobi pivot recurrence.
Proof: Form consecutive principal determinants of the same matrix sequence. -/
def jacobiPivot (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  (jacobiPrefix A B (n+1)).det/(jacobiPrefix A B n).det

/-- The initial determinant pivot is the first original diagonal entry.
Use: The initial determinant pivot is the first original diagonal entry.
Article: main_krylov, prop:phi(c), measured Jacobi pivot recurrence.
Proof: Evaluate the empty and one-site determinants. -/
theorem jacobiPivot_zero (A B : ℕ → ℝ) : jacobiPivot A B 0=A 0 := by
  simp [jacobiPivot,jacobiPrefix]

/-- Every principal pivot is positive when the original Jacobi prefixes are positive definite.
Use: Every principal pivot is positive when the original Jacobi prefixes are positive definite.
Article: main_krylov, prop:phi(c), measured Jacobi pivot recurrence.
Proof: Both consecutive principal determinants are positive. -/
theorem jacobiPivot_pos (A B : ℕ → ℝ) (hpos : ∀ N,(jacobiPrefix A B N).PosDef) (n : ℕ) :
    0 < jacobiPivot A B n :=
  div_pos (hpos (n+1)).det_pos (hpos n).det_pos

/-- Each used raw CG line length is the reciprocal of the corresponding original determinant pivot.
Use: Each used raw CG line length is the reciprocal of the corresponding original determinant pivot.
Article: main_krylov, prop:phi(c), measured Jacobi pivot recurrence.
Proof: Apply the raw determinant identity and identify both leading blocks. -/
theorem rawAlpha_jacobiPivot (A B : ℕ → ℝ) (hB : ∀ n,0 < B n) (N : ℕ)
    (hT : (jacobiPrefix A B N).PosDef) (r : ℕ) (hr : r<N) :
    rawAlpha (jacobiPrefix A B N) r=(jacobiPivot A B r)⁻¹ := by
  rw [rawAlpha_det _ hT (jacobiPrefix_tridiagonal A B N) (jacobiPrefix_adjacent_neg A B hB N) r hr,
    jacobiPrefix_leading A B N r hr.le,jacobiPrefix_leading A B N (r+1) (by omega),jacobiPivot,inv_div]

/-- The original determinant pivots satisfy the exact Jacobi Riccati recurrence.
Use: The original determinant pivots satisfy the exact Jacobi Riccati recurrence.
Article: main_krylov, prop:phi(c), measured Jacobi pivot recurrence.
Proof: Read the original LDL diagonal identity and substitute the measured reciprocal pivot and squared physical edge. -/
theorem jacobiPivot_recurrence (A B : ℕ → ℝ) (hB : ∀ n,0 < B n)
    (hpos : ∀ N,(jacobiPrefix A B N).PosDef) (n : ℕ) :
    jacobiPivot A B (n+1)=A (n+1)-(B n)^2/jacobiPivot A B n := by
  -- Use one additional original site so both adjacent pivots and the physical edge belong to the same computed finite matrix.
  let T := jacobiPrefix A B (n+2)
  let i : Fin (n+2) := ⟨n,by omega⟩
  let j : Fin (n+2) := ⟨n+1,by omega⟩
  have hdiag := raw_ldl_diagonal T (hpos (n+2)) (jacobiPrefix_tridiagonal A B (n+2))
    (jacobiPrefix_adjacent_neg A B hB (n+2)) j
  have hdg : (rawAlpha T (n+1))⁻¹+rawBeta T n/rawAlpha T n=A (n+1) := by
    simpa only [T,j,Fin.val_mk,Nat.add_sub_cancel,Nat.zero_lt_succ,ite_true,jacobiPrefix_diagonal] using hdiag
  have hedge : T i j= -B n := by
    simp [T,i,j,jacobiPrefix,Fin.ext_iff]
  rw [rawBeta_edge T i j rfl,hedge,
    rawAlpha_jacobiPivot A B hB (n+2) (hpos (n+2)) (n+1) (by omega),
    rawAlpha_jacobiPivot A B hB (n+2) (hpos (n+2)) n (by omega),inv_inv] at hdg
  -- Cancel the preceding positive pivot only after its principal determinant domain has been proved.
  have he : ((-B n)*(jacobiPivot A B n)⁻¹)^2/(jacobiPivot A B n)⁻¹=
      (B n)^2/jacobiPivot A B n := by
    field_simp [(jacobiPivot_pos A B hpos n).ne']
  rw [he] at hdg
  linarith
end
end krylov.Reference
