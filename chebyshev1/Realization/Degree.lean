import chebyshev1.Realization.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-! The residual of a fixed-coefficient N-step realization has degree at most N. -/
namespace chebyshev1.Realization
noncomputable section
open Polynomial
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialStep_natDegree_le (R : Realization ι) (s : ℕ) (i j : ι) :
    (R.polynomialStep s i j).natDegree≤1 := by
  unfold polynomialStep
  exact (natDegree_sub_le _ _).trans (max_le (by simp only [natDegree_C, zero_le])
    (natDegree_mul_le.trans (by simp only [natDegree_X, natDegree_C, add_zero, le_refl])))

theorem orderedPolynomial_natDegree_le (R : Realization ι) (N : ℕ) (i j : ι) :
    (orderedProduct R.polynomialStep N i j).natDegree≤N := by
  induction N generalizing i j with
  | zero =>
    simp only [orderedProduct,Matrix.one_apply]
    split_ifs <;> simp
  | succ N ih =>
    rw [orderedProduct_succ,Matrix.mul_apply]
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact natDegree_mul_le.trans (by have := R.polynomialStep_natDegree_le N i k; have := ih k j; omega)

theorem residualPolynomial_natDegree_le (R : Realization ι) (N : ℕ) :
    (R.residualPolynomial N).natDegree≤N := by
  unfold residualPolynomial
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_mul_C_le _ _).trans
    ((natDegree_C_mul_le _ _).trans (R.orderedPolynomial_natDegree_le N i j))

end
end chebyshev1.Realization
