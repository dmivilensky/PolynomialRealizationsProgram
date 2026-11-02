import krylov.Functions.PolynomialValueModel
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
Article: main_krylov, prop:Fcycle(i), the function-value diagonal substitution.
Use: identify the actual normalized cubic defect correction and prove that it
replaces each diagonal tensor argument zeta by zeta-lambda sigma. The native
uniform cycle-transfer theorem supplies the corresponding little-o remainder.
Source: Appendix G, the proved cubic defect and exact trilinear algebra.
-/

namespace krylov.Functions
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalizing an actual cubic value correction gives the precise tensor diagonal.
Article: main_krylov, prop:Fcycle(i), Delta_H,aa/c_a.
Proof: use the genuine observed polynomial defect, then cancel the nonzero step scale. -/
theorem normalized_cubic_value_correction
    (A : E →L[ℝ] E →L[ℝ] ℝ) (b : E →L[ℝ] ℝ)
    (hA : ∀ u v, A u v = A v u) (T : SymmetricCubic E) (c : ℝ)
    (a h : E) (q : ℝ) (hq : q ≠ 0) (l : ℝ) :
    (-12 * l * segmentValueDefect (cubicPolynomial A b T c)
      (fun x => A x - b + (1 / 2 : ℝ) • T.form x x) a (q • h)) / q ^ 2 =
      T.form (l • (q • h)) h h := by
  rw [cubicPolynomial_value_defect A b hA T c a (q • h)]
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp

/-- The tensor form of the reference latest-information model in step coordinates.
Article: main_krylov, equation (tensor-product). -/
def tensorWindowModel {n : ℕ} (T : SymmetricCubic E) (h ζ : Fin n → E) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => T.form (ζ (max i j)) (h i) (h j)

/-- The exact function-value correction changes only the diagonal tensor arguments.
Article: main_krylov, prop:Fcycle(i), zeta_a replaced by zeta_a-lambda_a sigma_a.
Proof: evaluate the true diagonal correction matrix and use trilinearity. -/
theorem tensorWindowModel_correct_diagonal {n : ℕ} (T : SymmetricCubic E)
    (h ζ σ : Fin n → E) (l : Fin n → ℝ) :
    tensorWindowModel T h ζ - Matrix.diagonal (fun i => T.form (l i • σ i) (h i) (h i)) =
      fun i j => if i = j then T.form (ζ i - l i • σ i) (h i) (h i)
        else T.form (ζ (max i j)) (h i) (h j) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [tensorWindowModel, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      max_self, ↓reduceIte, map_sub, sub_apply]
  · simp only [tensorWindowModel, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij,
      hij, ↓reduceIte, sub_zero]

/-- At the reference split one-half, zeta_a=sigma_a/2+v_a becomes exactly v_a.
Article: main_krylov, prop:Fcycle(i), the printed RFC-F diagonal replacement. -/
theorem tensorWindowModel_half_split {n : ℕ} (T : SymmetricCubic E)
    (h σ v : Fin n → E) :
    tensorWindowModel T h (fun i => (1 / 2 : ℝ) • σ i + v i) -
      Matrix.diagonal (fun i => T.form ((1 / 2 : ℝ) • σ i) (h i) (h i)) =
      fun i j => if i = j then T.form (v i) (h i) (h i)
        else T.form ((1 / 2 : ℝ) • σ (max i j) + v (max i j)) (h i) (h j) := by
  rw [tensorWindowModel_correct_diagonal T h (fun i => (1 / 2 : ℝ) • σ i + v i) σ
    (fun _ => (1 / 2 : ℝ))]
  ext i j
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte, add_sub_cancel_left]
  · simp only [hij, ↓reduceIte]

end
end krylov.Functions
