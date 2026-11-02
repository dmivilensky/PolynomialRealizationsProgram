import bezout.Synthesis.ExactDegrees
import bezout.Synthesis.Affine
import bezout.Polynomial.Factorization
import bezout.History.Bezout
import chebyshev1.Chebyshev.Polynomial

/-!
Article: bezout, Theorem 2.1, normalized Chebyshev Bezoutian factorization.
Use: every physical Chebyshev-exact history gives the normalized separated
factorization, and every normalized graded input basis gives its unique actual
history. The diagonal value is proved by differentiating a polynomial identity.
Proof: inverse affine spectral coordinates, the physical Bezoutian identity,
graded coordinate synthesis and uniqueness of polynomial evaluations.
-/

namespace bezout
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The polynomially extended Chebyshev Bezoutian, including its diagonal.
Use: an exact function on every spectral pair for the normalized factorization. -/
def chebyshevBezout (N : ℕ) (x y : ℝ) : ℝ :=
  History.dividedDifference (T ℝ N) x y / 2

namespace History
variable {N : ℕ}

/-- Exact terminal constraint defining the article's unrestricted comparison class.
Use: keeps terminal exactness as a polynomial identity for actual histories. -/
def ChebyshevExact (h : bezout.History N) (I : chebyshev1.SpectralInterval) : Prop :=
  h.terminal = I.residual N

/-- Normalized query polynomial in the Chebyshev coordinate.
Use: the `q_s` factors in Theorem 2.1. -/
def chartQuery (h : bezout.History N) (I : chebyshev1.SpectralInterval) (s : Fin N) : ℝ[X] :=
  (h.query s).comp (GradedFamily.chart I)

/-- Normalized physical response polynomial in the Chebyshev coordinate.
Use: the factors satisfying `Phi_s=-4 epsilon f_s/Delta` in Theorem 2.1. -/
def chartFactor (h : bezout.History N) (I : chebyshev1.SpectralInterval) (s : Fin N) : ℝ[X] :=
  C (-I.delta / (4 * I.epsilon N)) * (h.response s).comp (GradedFamily.chart I)

/-- The residual in the inverse affine coordinate is the unshifted Chebyshev polynomial.
Use: normalizes the actual terminal difference before extracting its Bezoutian. -/
theorem residual_comp_chart (I : chebyshev1.SpectralInterval) :
    (I.residual N).comp (GradedFamily.chart I) = C (I.epsilon N) * T ℝ N := by
  unfold chebyshev1.SpectralInterval.residual
  rw [mul_comp, C_comp, comp_assoc, GradedFamily.coordinate_comp_chart, comp_X]
  simp only [chebyshev1.SpectralInterval.epsilon, one_div]

/-- Terminal values in the Chebyshev coordinate have exactly the required normalization.
Use: converts the physical Bezoutian to the factorization on `[-1,1]`. -/
theorem terminal_chart_eval (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (x : ℝ) :
    h.terminal.eval ((GradedFamily.chart I).eval x) = I.epsilon N * (T ℝ N).eval x := by
  change h.terminal = I.residual N at he
  rw [he, ← eval_comp, residual_comp_chart]
  simp only [eval_mul, eval_C]

/-- The inverse affine coordinate has the correct difference scale.
Use: extracts the factor `-Delta/2` from the physical terminal identity. -/
theorem chart_eval_sub (I : chebyshev1.SpectralInterval) (x y : ℝ) :
    (GradedFamily.chart I).eval x - (GradedFamily.chart I).eval y =
      -(I.delta / 2) * (x - y) := by
  simp only [GradedFamily.chart, eval_sub, eval_C, eval_mul, eval_X]
  ring

/-- Normalized factors satisfy the undivided two-variable Chebyshev identity.
Use: obtains both off-diagonal and diagonal Bezoutian values from one polynomial identity. -/
theorem chart_difference (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (x y : ℝ) :
    (T ℝ N).eval x - (T ℝ N).eval y =
      2 * (x - y) * ∑ s, (h.chartFactor I s).eval x * (h.chartQuery I s).eval y := by
  have hep : I.epsilon N ≠ 0 := by
    exact one_div_ne_zero (I.den_ne N)
  have hd := h.terminal_difference ((GradedFamily.chart I).eval x)
    ((GradedFamily.chart I).eval y)
  rw [h.terminal_chart_eval I he, h.terminal_chart_eval I he, chart_eval_sub] at hd
  have hs : (∑ s, (h.chartFactor I s).eval x * (h.chartQuery I s).eval y) =
      (-I.delta / (4 * I.epsilon N)) *
        ∑ s, (h.response s).eval ((GradedFamily.chart I).eval x) *
          (h.query s).eval ((GradedFamily.chart I).eval y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [chartFactor, chartQuery, eval_mul, eval_C, eval_comp]
    ring
  rw [hs]
  apply (mul_left_cancel₀ hep)
  field_simp
  nlinarith [hd]

/-- The normalized difference identity is an identity of polynomials in its first variable.
Use: justifies the diagonal specialization by exact differentiation. -/
theorem chart_difference_polynomial (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (y : ℝ) :
    T ℝ N - C ((T ℝ N).eval y) =
      (X - C y) * C 2 *
        ∑ s, C ((h.chartQuery I s).eval y) * h.chartFactor I s := by
  apply Polynomial.funext
  intro x
  simp only [eval_sub, eval_C, eval_mul, eval_X, eval_finsetSum]
  rw [h.chart_difference I he]
  have hs : (∑ s, (h.chartFactor I s).eval x * (h.chartQuery I s).eval y) =
      ∑ s, (h.chartQuery I s).eval y * (h.chartFactor I s).eval x := by
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hs]
  ring

/-- The normalized factorization holds at every spectral pair, including the diagonal.
Use: the complete Bezoutian factorization in Theorem 2.1. -/
theorem chart_factorization (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (x y : ℝ) :
    (∑ s, (h.chartFactor I s).eval x * (h.chartQuery I s).eval y) =
      chebyshevBezout N x y := by
  by_cases hxy : x = y
  · subst y
    have hd := congrArg (fun p : ℝ[X] => p.derivative.eval x)
      (h.chart_difference_polynomial I he x)
    simp only [derivative_sub, derivative_C, sub_zero, derivative_mul, derivative_X,
      one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
      add_zero, eval_finsetSum] at hd
    simp only [chebyshevBezout, dividedDifference, ite_true]
    rw [hd]
    have hs : (∑ s, (h.chartFactor I s).eval x * (h.chartQuery I s).eval x) =
        ∑ s, (h.chartQuery I s).eval x * (h.chartFactor I s).eval x := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hs]
    ring
  · simp only [chebyshevBezout, dividedDifference, hxy, ite_false]
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
    apply (eq_div_iff (sub_ne_zero.mpr hxy)).mpr
    rw [h.chart_difference I he]
    ring

end History
end
end bezout
