import krylov.Methods.OneGradientChronological
import krylov.Stability.ContDiffSolve
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine chronological virtual coefficient regularity.
Use: differentiate actual chronological virtual injections and output-segment defects using native coefficients of the real finite observed solve.
Source: genuine full-memory array coordinates, original latest pair-model entries and proved C-r inverse-model coefficient calculus.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Each genuine chronological native virtual-solve coefficient is C-r in the actual C-r executed observations on its true model determinant domain.
Use: Each genuine chronological native virtual-solve coefficient is C-r in the actual C-r executed observations on its true model determinant domain.
Article: main_krylov, thm:E1, genuine chronological virtual coefficient regularity.
Proof: Use the actual newest-age arrays in the real pair model, derive every genuine entry regularity and read its actual reversed chronological coordinate. -/
theorem oneGradient_virtualCoefficients_contDiffAt {r : WithTop ℕ∞} (m : OneGradientMethod E)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (k : ℕ)
    (hA : ∀ j<k,ContDiffAt ℝ r (fun t => A t j) x)
    (hs : ∀ j<k,ContDiffAt ℝ r (fun t => oneGradientStep m (A t) (g t) j) x)
    (hG : ContDiffAt ℝ r (fun t => oneGradientGradient m (A t) (g t) k) x)
    (hM : (pairModel
      (fun i : Fin k => oneGradientStep m (A x) (g x) (k-1-i.val))
      (fun i : Fin k => A x (k-1-i.val) (oneGradientStep m (A x) (g x) (k-1-i.val)))).det≠0)
    (i : Fin k) : ContDiffAt ℝ r (fun t => oneGradientVirtualCoefficients m (A t) (g t) k i) x := by
  let S := fun t (j : Fin k) => oneGradientStep m (A t) (g t) (k-1-j.val)
  let Y := fun t (j : Fin k) => A t (k-1-j.val) (S t j)
  have hS (j : Fin k) : ContDiffAt ℝ r (fun t => S t j) x := hs _ (by omega)
  have hY (j : Fin k) : ContDiffAt ℝ r (fun t => Y t j) x := (hA _ (by omega)).clm_apply (hS j)
  exact contDiff_modelCoefficients S (fun t => pairModel (S t) (Y t)) _ x hS
    (fun j l => (hS (max j l)).inner ℝ (hY (min j l))) hG hM i.rev
end
end krylov.Stability
