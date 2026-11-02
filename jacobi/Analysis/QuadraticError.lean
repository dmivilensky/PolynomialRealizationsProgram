import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The uniform entry error controls the entire finite quadratic form by
the number of coordinates times the Euclidean squared norm. The factor
is explicit, so a vanishing mesh error remains small on growing sections.
Source: the finite Cauchy--Schwarz inequality.
Use: matrix_quadratic_error converts the source's uniform kernel error into a quantitative finite quadratic-form error.
-/
namespace jacobi.Analysis
noncomputable section
open Matrix

/-- The squared absolute coordinate sum is bounded by dimension times
the Euclidean squared norm.
Use: matrix_quadratic_error converts the source's uniform kernel error
into a quantitative finite quadratic-form error.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Source: finite Cauchy--Schwarz, mathlib's sum_mul_sq_le_sq_mul_sq.
Proof: apply Cauchy--Schwarz to the absolute values and the constant
one vector, retaining the actual finite dimension. -/
theorem sum_abs_sq_le {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (∑ i, |v i|)^2 ≤ (Fintype.card ι : ℝ) * ∑ i, (v i)^2 := by
  simpa [mul_comm] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1:ℝ)) (fun i => |v i|)

/-- A uniform entry perturbation bounds the complete finite quadratic
form with its exact dimension factor.
Use: the actual sampled two-edge Gram approximation can be compared
with the two continuum coercive forms on growing principal sections.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: take the absolute value termwise, factor the two absolute
coordinate sums and apply the proved finite Cauchy--Schwarz bound. -/
theorem matrix_quadratic_error {ι : Type*} [Fintype ι]
    (E : Matrix ι ι ℝ) {δ : ℝ} (hδ : 0≤δ)
    (hE : ∀ i j, |E i j|≤δ) (v : ι → ℝ) :
    |∑ i, ∑ j, E i j*v i*v j| ≤
      δ*(Fintype.card ι : ℝ)*∑ i, (v i)^2 := by
  -- Bound entries first; only then apply Cauchy--Schwarz to the two coordinate sums.
  calc
    _ ≤ ∑ i, ∑ j, |E i j*v i*v j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ =>
        Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, ∑ j, δ*|v i| * |v j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hE i j) (abs_nonneg _)) (abs_nonneg _)
    _ = δ*(∑ i, |v i|)^2 := by
      simp_rw [← Finset.mul_sum,← Finset.sum_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (sum_abs_sq_le v) hδ
      simpa only [mul_assoc] using hh

end
end jacobi.Analysis
