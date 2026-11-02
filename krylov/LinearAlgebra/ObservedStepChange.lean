import krylov.Stability.ContDiffSpectralMatrix
import krylov.Stability.ContDiffSolve
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual observed step/direction basis change.
Use: assemble the genuine finite triangular change from native replay
directions to recorded evaluated steps without assuming a basis dictionary.
Source: exact newest-age indexing, real finite synthesis and primitive
smooth coefficient calculus; the reference change is genuinely diagonal.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Finset krylov.Methods krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {k : ℕ} {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual old-prefix entry embedded in its complete newest-age
window: older directions lie strictly below the current column index.
Use: compare real recorded step columns with native replay directions.
Article: main_krylov, thm:local(a), true observed prefix embedding. -/
def oldColumnIndex (j : Fin k) (r : Fin (k-1-j.val)) : Fin k := ⟨j.val+1+r.val,by omega⟩

/-- The genuine chronological age of the embedded old direction is its
original old-prefix newest-age coordinate.
Use: finite synthesis reads the actual same physical replay direction.
Article: main_krylov, thm:local(a), exact native age dictionary.
Proof: both finite index bounds give the exact natural subtraction identity. -/
theorem oldColumnIndex_age (j : Fin k) (r : Fin (k-1-j.val)) :
    k-1-(oldColumnIndex j r).val=(k-1-j.val)-1-r.val := by
  dsimp only [oldColumnIndex]
  omega

/-- The actual coefficient matrix for old virtual corrections plus the
real selected trial in each genuine evaluated step column.
Use: its columns reconstruct actual steps and their observed images by
the same true data-only replay coefficients, with no operator substitution.
Article: main_krylov, thm:local(a), original observed triangular change. -/
def observedStepChange (tau : Fin k → ℝ) (w : (j : Fin k) → Fin (k-1-j.val) → ℝ) :
    Matrix (Fin k) (Fin k) ℝ := fun i j =>
  (∑ r : Fin (k-1-j.val),if i=oldColumnIndex j r then w j r else 0)+if i=j then tau j else 0

/-- Every genuine evaluated-step change column synthesizes exactly its
real old-prefix virtual correction plus its selected current trial step.
Use: the same exact finite dictionary applies to actual directions and
their returned-gradient replay images.
Article: main_krylov, thm:local(a), true observed column synthesis.
Proof: distribute true finite coefficient synthesis, exchange its finite
old/global sums and select each exact embedded old coordinate. -/
theorem observedStepChange_column (u : Fin k → E) (tau : Fin k → ℝ)
    (w : (j : Fin k) → Fin (k-1-j.val) → ℝ) (j : Fin k) :
    combine u (fun i => observedStepChange tau w i j)=
      combine (fun r => u (oldColumnIndex j r)) (w j)+tau j • u j := by
  simp only [combine,observedStepChange,add_smul,Finset.sum_smul,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [ite_smul,zero_smul,Finset.sum_ite_eq',mem_univ,ite_true]

/-- Vanishing real virtual correction weights make the genuine observed
change matrix exactly diagonal with the actual selected trials.
Use: calibrated CG reference lengths give its real nonsingular diagonal.
Article: main_krylov, thm:local(a), true reference basis-change scales.
Proof: every old-prefix coefficient is zero; each genuine current column
has exactly its own selected diagonal trial coefficient. -/
theorem observedStepChange_zero_weights (tau : Fin k → ℝ)
    (w : (j : Fin k) → Fin (k-1-j.val) → ℝ) (hw : ∀ j r,w j r=0) :
    observedStepChange tau w=diagonal tau := by
  ext i j
  simp only [observedStepChange,hw,ite_self,sum_const_zero,zero_add]
  by_cases hij : i=j
  · subst i
    simp only [ite_true,diagonal_apply_eq]
  · simp only [ite_eq_right hij,diagonal_apply_ne _ hij]

/-- Genuine primitive C-one trial and virtual coefficient arrays give
a C-one actual observed change matrix in the true spectral matrix norm.
Use: the native basis-change model remainder has all smoothness premises
derived from the actual real coefficient program.
Article: main_krylov, thm:local(a), primitive observed change regularity.
Proof: each actual finite entry is a finite sum of real C-one observed
coefficients selected by fixed indices; assemble the true spectral matrix. -/
theorem observedStepChange_contDiffAt
    (tau : X → Fin k → ℝ) (w : (z : X) → (j : Fin k) → Fin (k-1-j.val) → ℝ)
    (htau : ∀ j,ContDiffAt ℝ 1 (fun z => tau z j) 0)
    (hw : ∀ j r,ContDiffAt ℝ 1 (fun z => w z j r) 0) :
    ContDiffAt ℝ 1 (fun z => observedStepChange (tau z) (w z)) 0 := by
  apply contDiff_spectral_matrix
  intro i j
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro r _
    by_cases hi : i=oldColumnIndex j r
    · simpa only [ite_eq_left hi] using hw j r
    · simp only [ite_eq_right hi]
      exact contDiffAt_const
  · by_cases hij : i=j
    · simpa only [ite_eq_left hij] using htau j
    · simp only [ite_eq_right hij]
      exact contDiffAt_const

end
end krylov.LinearAlgebra
