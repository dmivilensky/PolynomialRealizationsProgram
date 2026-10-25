import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
Article: first part, Theorem `thm:interpolation` and Appendix A.
Use: arbitrary indexed value/gradient tables and the symmetric interpolation
inequalities, with their exact conversion to convex 2-smooth interpolation.
Proof: real inner-product identities and polynomial algebra.
-/

noncomputable section

namespace polyak.Interpolation

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: `Tᵢⱼ` in (interpolation). Use: signed interpolation discrepancy. -/
def datumT (x σ : I → E) (values : I → ℝ) (i j : I) : ℝ :=
  values j - values i - (1 / 2 : ℝ) * inner ℝ (σ i + σ j) (x j - x i)

/-- Article: `Rᵢⱼ` in (interpolation). Use: symmetric interpolation radius. -/
def datumR (x σ : I → E) (i j : I) : ℝ :=
  (1 / 4 : ℝ) * (‖x j - x i‖ ^ 2 - ‖σ j - σ i‖ ^ 2)

/-- Article: (interpolation). Use: feasibility without restrictions on index set or data. -/
def TableFeasible (x σ : I → E) (values : I → ℝ) : Prop :=
  ∀ i j, |datumT x σ values i j| ≤ datumR x σ i j

/-- Article: Appendix A, `Fᵢ`. Use: convexified function values. -/
def convexValue (x : I → E) (values : I → ℝ) (i : I) : ℝ :=
  values i + (1 / 2 : ℝ) * ‖x i‖ ^ 2

/-- Article: Appendix A, `Gᵢ`. Use: convexified gradients. -/
def convexGradient (x σ : I → E) (i : I) : E := σ i + x i

/-- Article: (convexinterp). Use: convex 2-smooth interpolation condition. -/
def ConvexTableFeasible (x G : I → E) (F : I → ℝ) : Prop :=
  ∀ i j, F j + inner ℝ (G j) (x i - x j) + (1 / 4 : ℝ) * ‖G i - G j‖ ^ 2 ≤ F i

omit [InnerProductSpace ℝ E] in
/-- Article: (interpolation). Proof: symmetry of squared distance. -/
theorem datumR_symm (x σ : I → E) (i j : I) : datumR x σ i j = datumR x σ j i := by
  simp only [datumR, norm_sub_rev (x j) (x i), norm_sub_rev (σ j) (σ i)]

/-- Article: (interpolation). Proof: exchange of endpoints reverses the discrepancy. -/
theorem datumT_antisymm (x σ : I → E) (values : I → ℝ) (i j : I) :
    datumT x σ values j i = -datumT x σ values i j := by
  simp only [datumT, inner_add_left, inner_sub_right]
  ring

/-- Article: Appendix A, first algebraic reduction. Proof: expand all squared norms. -/
theorem convex_gap_eq (x σ : I → E) (values : I → ℝ) (i j : I) :
    convexValue x values i - (convexValue x values j +
      inner ℝ (convexGradient x σ j) (x i - x j) +
      (1 / 4 : ℝ) * ‖convexGradient x σ i - convexGradient x σ j‖ ^ 2) =
      datumR x σ i j - datumT x σ values i j := by
  simp only [convexValue, convexGradient, datumR, datumT,
    norm_sub_sq_real, norm_add_sq_real, inner_add_left, inner_add_right,
    inner_sub_right, real_inner_self_eq_norm_sq]
  simp only [real_inner_comm (x i) (σ j), real_inner_comm (x j) (x i),
    real_inner_comm (σ j) (σ i)]
  ring

/-- Article: Appendix A, equivalence with (convexinterp).
Use: exact reduction, preserving arbitrary index sets and both signs.
Proof: one signed inequality and its reversed-index counterpart. -/
theorem tableFeasible_iff_convex (x σ : I → E) (values : I → ℝ) :
    TableFeasible x σ values ↔
      ConvexTableFeasible x (convexGradient x σ) (convexValue x values) := by
  constructor
  · intro h i j
    have hu := (abs_le.mp (h i j)).2
    have he := convex_gap_eq x σ values i j
    linarith
  · intro h i j
    have hi := h i j
    have hj := h j i
    have hei := convex_gap_eq x σ values i j
    have hej := convex_gap_eq x σ values j i
    rw [datumR_symm x σ j i, datumT_antisymm x σ values i j] at hej
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end polyak.Interpolation
