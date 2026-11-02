import bezout.History.Resolvent

/-!
Article: bezout, Theorem 2.1 (physical divided-difference identity).
Use: endpoint lower bounds for arbitrary causal histories, with arbitrary signs.
Proof: the finite causal inverse satisfies the two-parameter resolvent
identity; the diagonal identity follows by differentiating a polynomial identity.
-/

namespace bezout.History

open Polynomial
open scoped BigOperators Polynomial
noncomputable section
variable {N : ℕ}

/-- Evaluation of the physical polynomial inverse on one spectral mode.
Article: bezout, Appendix A. Use: the resolvent identity. -/
def evaluated (h : bezout.History N) (x : ℝ) : Fin N → Fin N → ℝ :=
  fun s j => (h.resolvent s j).eval x

/-- The scalar spectral pencil I+xA.
Article: bezout, Appendix A. Use: the resolvent identity. -/
def scalarPencil (h : bezout.History N) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  1 + x • Matrix.of h.a

/-- The polynomial pencil evaluates to the physical scalar pencil.
Article: bezout, Appendix A. Use: transport the inverse identities. -/
theorem pencil_eval (h : bezout.History N) (x : ℝ) :
    h.pencil.map (Polynomial.evalRingHom x) = h.scalarPencil x := by
  apply Matrix.ext
  intro i j
  change ((if i = j then 1 else 0) + X * C (h.a i j)).eval x =
    (if i = j then 1 else 0) + x * h.a i j
  split_ifs <;> simp only [eval_add, eval_one, eval_zero, eval_mul, eval_X, eval_C]

/-- The evaluated physical inverse is a right inverse.
Article: bezout, Appendix A. Use: two-parameter resolvent identity. -/
theorem scalarPencil_mul_evaluated (h : bezout.History N) (x : ℝ) :
    h.scalarPencil x * Matrix.of (h.evaluated x) = 1 := by
  have he := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ[X] =>
    M.map (Polynomial.evalRingHom x)) h.pencil_mul_resolvent
  rw [Matrix.map_mul, h.pencil_eval] at he
  have hv : (Matrix.of h.resolvent).map (Polynomial.evalRingHom x) =
      Matrix.of (h.evaluated x) := by
    apply Matrix.ext
    intro i j
    rfl
  rw [hv] at he
  simpa using he

/-- The evaluated physical inverse is a left inverse.
Article: bezout, Appendix A. Use: two-parameter resolvent identity. -/
theorem evaluated_mul_scalarPencil (h : bezout.History N) (x : ℝ) :
    Matrix.of (h.evaluated x) * h.scalarPencil x = 1 :=
  mul_eq_one_comm.mp (h.scalarPencil_mul_evaluated x)

/-- Two inverse pencils satisfy the exact finite resolvent identity.
Article: bezout, Appendix A. Use: physical Bezoutian factorization. -/
theorem evaluated_resolvent_identity (h : bezout.History N) (x y : ℝ) :
    x • Matrix.of (h.evaluated x) - y • Matrix.of (h.evaluated y) =
      (x - y) • (Matrix.of (h.evaluated x) * Matrix.of (h.evaluated y)) := by
  have hm : x • h.scalarPencil y - y • h.scalarPencil x =
      (x - y) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    apply Matrix.ext
    intro i j
    simp only [scalarPencil, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring
  calc
    x • Matrix.of (h.evaluated x) - y • Matrix.of (h.evaluated y) =
        Matrix.of (h.evaluated x) * (x • h.scalarPencil y - y • h.scalarPencil x) *
          Matrix.of (h.evaluated y) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
        h.scalarPencil_mul_evaluated, h.evaluated_mul_scalarPencil,
        Matrix.one_mul, Matrix.mul_one]
    _ = (x - y) • (Matrix.of (h.evaluated x) * Matrix.of (h.evaluated y)) := by
      rw [hm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

/-- Evaluation of a nominal query is a row sum of the physical inverse.
Article: bezout, Theorem 2.1. Use: scalar contraction of the resolvent identity. -/
theorem query_eval (h : bezout.History N) (s : Fin N) (x : ℝ) :
    (h.query s).eval x = ∑ j, h.evaluated x s j := by
  simp [query, evaluated, eval_finsetSum]

/-- Evaluation of a physical response is the weighted inverse column sum.
Article: bezout, Theorem 2.1. Use: scalar contraction of the resolvent identity. -/
theorem response_eval (h : bezout.History N) (j : Fin N) (x : ℝ) :
    (h.response j).eval x = - ∑ s, h.b s * h.evaluated x s j := by
  simp [response, evaluated, eval_finsetSum]

/-- The query-level resolvent identity, before applying the output weights.
Article: bezout, Appendix A. Use: the physical divided-difference identity. -/
theorem query_difference (h : bezout.History N) (i : Fin N) (x y : ℝ) :
    x * (h.query i).eval x - y * (h.query i).eval y =
      (x - y) * ∑ k, h.evaluated x i k * (h.query k).eval y := by
  have hr (j : Fin N) := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M i j)
    (h.evaluated_resolvent_identity x y)
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.of_apply] at hr
  calc
    _ = ∑ j, (x * h.evaluated x i j - y * h.evaluated y i j) := by
      rw [h.query_eval, h.query_eval, Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = ∑ j, ((x - y) * ∑ k, h.evaluated x i k * h.evaluated y k j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hr j
    _ = (x - y) * ∑ k, h.evaluated x i k * (h.query k).eval y := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.mul_sum, h.query_eval]

/-- Polynomial cross identity without division, valid even when x=y.
Article: bezout, Equation (5). Use: divided differences and diagonal derivatives. -/
theorem terminal_difference (h : bezout.History N) (x y : ℝ) :
    h.terminal.eval x - h.terminal.eval y =
      (x - y) * ∑ s, (h.response s).eval x * (h.query s).eval y := by
  have hfactor (t : ℝ) (f : Fin N → ℝ) :
      ∑ i, h.b i * (t * f i) = t * ∑ i, h.b i * f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hswitch : (∑ i, h.b i * ∑ k,
      h.evaluated x i k * (h.query k).eval y) =
      ∑ k, (∑ i, h.b i * h.evaluated x i k) * (h.query k).eval y := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    _ = - ∑ i, h.b i * (x * (h.query i).eval x - y * (h.query i).eval y) := by
      simp only [terminal, eval_sub, eval_one, eval_mul, eval_X, eval_finsetSum, eval_C]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [hfactor, hfactor]
      ring
    _ = - ∑ i, h.b i * ((x - y) * ∑ k,
        h.evaluated x i k * (h.query k).eval y) := by
      simp_rw [h.query_difference]
    _ = (x - y) * ∑ s, (h.response s).eval x * (h.query s).eval y := by
      rw [hfactor, hswitch]
      simp_rw [h.response_eval, neg_mul, Finset.sum_neg_distrib]
      ring

/-- The physical factorization is a polynomial identity in the output parameter.
Article: bezout, Theorem 2.1. Use: specialize the diagonal without division. -/
theorem terminal_difference_polynomial (h : bezout.History N) (y : ℝ) :
    h.terminal - C (h.terminal.eval y) =
      (X - C y) * ∑ s, C ((h.query s).eval y) * h.response s := by
  apply Polynomial.funext
  intro x
  simp only [eval_sub, eval_C, eval_mul, eval_X, eval_finsetSum]
  rw [h.terminal_difference]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The physical Bezoutian identity away from the diagonal.
Article: bezout, Equation (5). Use: corner evaluation of every causal history. -/
theorem physical_bezout (h : bezout.History N) (x y : ℝ) (hxy : x ≠ y) :
    (∑ s, (h.response s).eval x * (h.query s).eval y) =
      (h.terminal.eval x - h.terminal.eval y) / (x - y) := by
  apply (eq_div_iff (sub_ne_zero.mpr hxy)).mpr
  rw [mul_comm]
  exact (h.terminal_difference x y).symm

/-- The diagonal physical Bezoutian identity is the terminal derivative.
Article: bezout, Theorem 2.1. Use: the endpoint Cauchy--Schwarz lower bound. -/
theorem physical_bezout_diagonal (h : bezout.History N) (x : ℝ) :
    (∑ s, (h.response s).eval x * (h.query s).eval x) =
      h.terminal.derivative.eval x := by
  have hd := congrArg (fun p : ℝ[X] => p.derivative.eval x)
    (h.terminal_difference_polynomial x)
  simp only [derivative_sub, derivative_C, sub_zero, derivative_mul, derivative_X,
    one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    add_zero, eval_finsetSum] at hd
  rw [hd]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Divided difference with its polynomially continuous diagonal value.
Article: bezout, Theorem 2.1. Use: one identity for all spectral pairs. -/
def dividedDifference (p : ℝ[X]) (x y : ℝ) : ℝ :=
  if x = y then p.derivative.eval x else (p.eval x - p.eval y) / (x - y)

/-- Every physical response/query factorization equals the complete divided difference.
Article: bezout, Theorem 2.1. Use: normalized Chebyshev factorization and sharp corners. -/
theorem physical_bezout_all (h : bezout.History N) (x y : ℝ) :
    (∑ s, (h.response s).eval x * (h.query s).eval y) =
      dividedDifference h.terminal x y := by
  by_cases hxy : x = y
  · subst y
    simpa [dividedDifference] using h.physical_bezout_diagonal x
  · simpa [dividedDifference, hxy] using h.physical_bezout x y hxy

end
end bezout.History
