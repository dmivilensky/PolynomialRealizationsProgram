import krylov.Functions.CubicValueModel
import krylov.Functions.QuadraticHiddenFamily

/-!
Article: main_krylov, thm:Fexact, all scalar polynomials of degree at most three.
Use: add arbitrary symmetric quadratic, linear and constant terms to the cubic
without changing its exact defect or corrected-diagonal remainder.
Source: Appendix G; the actual derivative rules and exact polynomial algebra.
-/

namespace krylov.Functions
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An arbitrary scalar polynomial through degree three, in coordinate-free tensor form.
Article: main_krylov, thm:Fexact. -/
def cubicPolynomial (A : E →L[ℝ] E →L[ℝ] ℝ) (b : E →L[ℝ] ℝ)
    (T : SymmetricCubic E) (c : ℝ) (x : E) : ℝ :=
  c + quadraticPotential A b x + T.potential x

/-- The displayed first differential is the actual Frechet derivative of the full polynomial.
Article: main_krylov, thm:Fexact. -/
theorem cubicPolynomial_hasFDerivAt (A : E →L[ℝ] E →L[ℝ] ℝ) (b : E →L[ℝ] ℝ)
    (hA : ∀ u v, A u v = A v u) (T : SymmetricCubic E) (c : ℝ) (x : E) :
    HasFDerivAt (cubicPolynomial A b T c)
      (A x - b + (1 / 2 : ℝ) • T.form x x) x :=
  ((quadraticPotential_hasFDerivAt A b hA x).const_add c).add (T.potential_hasFDerivAt x)

/-- The actual first differential differentiates to the polynomial's affine Hessian.
Article: main_krylov, thm:Fexact. -/
theorem cubicPolynomial_differential_hasFDerivAt
    (A : E →L[ℝ] E →L[ℝ] ℝ) (b : E →L[ℝ] ℝ) (T : SymmetricCubic E) (x : E) :
    HasFDerivAt (fun x => A x - b + (1 / 2 : ℝ) • T.form x x) (A + T.form x) x :=
  (A.hasFDerivAt.sub_const b).add (T.differential_hasFDerivAt x)

/-- The true Hessian of the full polynomial has the given constant third derivative.
Article: main_krylov, thm:Fexact. -/
theorem cubicPolynomial_hessian_hasFDerivAt
    (A : E →L[ℝ] E →L[ℝ] ℝ) (T : SymmetricCubic E) (x : E) :
    HasFDerivAt (fun x => A + T.form x) T.form x :=
  (T.hessian_hasFDerivAt x).const_add (𝕜 := ℝ) A

/-- All lower-order polynomial terms cancel from the actual function-value defect.
Article: main_krylov, thm:Fexact, delta_tr=-T(s,s,s)/12 on all cubics. -/
theorem cubicPolynomial_value_defect (A : E →L[ℝ] E →L[ℝ] ℝ) (b : E →L[ℝ] ℝ)
    (hA : ∀ u v, A u v = A v u) (T : SymmetricCubic E) (c : ℝ) (a s : E) :
    segmentValueDefect (cubicPolynomial A b T c)
      (fun x => A x - b + (1 / 2 : ℝ) • T.form x x) a s = -T.form s s s / 12 := by
  have hq := quadraticPotential_trapezoid A b hA a s
  have hc := T.trapezoid_defect a s
  simp only [segmentValueDefect, cubicPolynomial, add_apply, smul_apply, smul_eq_mul]
  linarith only [hq, hc]

/-- The whole observed diagonal has zero remainder on every scalar cubic polynomial.
Article: main_krylov, thm:Fexact, R=0 with arbitrary anchor and split. -/
theorem cubicPolynomial_corrected_diagonal
    (A : E →L[ℝ] E →L[ℝ] ℝ) (b : E →L[ℝ] ℝ)
    (hA : ∀ u v, A u v = A v u) (T : SymmetricCubic E) (c : ℝ)
    (a s x : E) (l : ℝ) :
    correctedValueDiagonal (cubicPolynomial A b T c)
      (fun x => A x - b + (1 / 2 : ℝ) • T.form x x) a s l - (A + T.form x) s s =
      -T.form (x - (a + (1 / 2 : ℝ) • s) - l • s) s s := by
  rw [correctedValueDiagonal, cubicPolynomial_value_defect A b hA T c a s]
  rw [show A (a + s) = A a + A s from map_add A a s]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
  have hm := T.midpoint_diagonal a s
  have he : 1 / 2 * T.form (a + s) (a + s) s - 1 / 2 * T.form a a s =
      T.form (a + (1 / 2 : ℝ) • s) s s := by linarith only [hm]
  have hh : T.form (x - (a + (1 / 2 : ℝ) • s) - l • s) s s =
      T.form x s s - T.form (a + (1 / 2 : ℝ) • s) s s - l * T.form s s s := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
  rw [hh]
  linarith only [he]

end
end krylov.Functions
