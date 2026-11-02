import krylov.XR.LocalRawWindow
import krylov.XR.LocalWindowQuotient

/-!
Article: main_krylov, apG:local and thm:grow, genuine full-window branch.
Use: derive zero new direction for the actual observed full basis, rather
than assuming it, and identify the literal branch with the proved local
model-step bounds. Source: the genuine nonsingular image-conjugacy solve
and full physical span of an independent n-column Euclidean window.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- On a full physical window the actual computed image-conjugacy
direction is zero; this needs no symmetry of the observed images. -/
theorem modelDirection_zero_of_full_span (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hinv : IsUnit (crossGram y s).det)
    (hspan : Submodule.span ℝ (range s) = ⊤) (g : E) : modelDirection s y T g = 0 := by
  apply conjugacyDirection_unique s y _ 0 hinv
  · rw [zero_add, hspan]
    exact Submodule.mem_top
  · ext i
    change inner ℝ (y i) (0 : E) = 0
    simp only [inner_zero_right]

/-- Actual independent square physical columns have full span, including
the vacuous zero-dimensional case. -/
theorem fullWindow_span {n : ℕ} (s : Fin n → EuclideanSpace ℝ (Fin n))
    (hs : LinearIndependent ℝ s) : Submodule.span ℝ (range s) = ⊤ := by
  apply hs.span_eq_top_of_card_eq_finrank'
  simp only [Fintype.card_fin, finrank_euclideanSpace]

/-- The real full-window solve has zero new direction on the inverse
domain already derived from primitive local source data. -/
theorem modelDirection_zero_full_window {n : ℕ}
    (s y : Fin n → EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin n) (Fin n) ℝ)
    (hs : LinearIndependent ℝ s) (hinv : IsUnit (crossGram y s).det) (g : EuclideanSpace ℝ (Fin n)) :
    modelDirection s y T g = 0 := modelDirection_zero_of_full_span s y T hinv (fullWindow_span s hs) g

end
end krylov.XR
