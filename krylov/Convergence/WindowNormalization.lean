import krylov.Methods.NormalizedCorrection

/-!
Article: main_krylov, apG:local, actual normalized observed windows.
Use: replace raw rectangular secant pairs by unit step columns without
changing the computed FC direction. Source: exact nonsingular diagonal
coordinate change in the genuine observed coefficient solve.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

/-- Exact two-sided observed cross-Gram normalization for an arbitrary
rectangular physical window. -/
theorem window_crossGram_rescale (s y : ι → E) (c : ι → ℝ) :
    crossGram (rescaleWindow s c) (rescaleWindow y c)=rescaleModel (crossGram s y) c := by
  ext i j
  simp only [crossGram,rescaleWindow,real_inner_smul_left,real_inner_smul_right,
    rescaleModel,diagonal_mul,mul_diagonal]
  ring

/-- Arbitrary nonzero individual pair normalizers leave the actual
observed FC direction exactly unchanged, even on a totalized singular
cross-Gram branch. No square physical basis is required. -/
theorem conjugacyDirection_rescale (s y : ι → E) (c : ι → ℝ)
    (hc : IsUnit (diagonal c).det) (g : E) :
    conjugacyDirection (rescaleWindow s c) (rescaleWindow y c) g=conjugacyDirection s y g := by
  simp only [conjugacyDirection]
  congr 1
  rw [combine_rescale,conjugacyCoefficients,window_crossGram_rescale,coordinates_rescale,
    mulVec_mulVec,mulVec_mulVec,rescaleModel_inverse _ _ hc]
  rfl

end
end krylov.Convergence
