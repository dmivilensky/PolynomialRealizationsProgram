import bezout.Comparisons.Competitors.Propagation
import chebyshev1.Stepsize.Basic
import bezout.History.Realization

/-!
Article: bezout, LF/fractal configuration and Equation `eq:competitor-transfer`.
Use: an arbitrary scalar stepsize schedule is an actual oracle history, with
its exact terminal product, physical suffix responses and two-variable kernel.
Proof: the zero-momentum two-by-two products have a scalar first row, including
empty prefixes and suffixes. The generic physical propagation theorem applies.
-/

namespace bezout.Comparisons.Competitors.Stepsize
noncomputable section
open chebyshev1 Polynomial
open scoped BigOperators Matrix

/-- Literal gradient steps with the prescribed scalar schedule. -/
def config (gamma : ℕ → ℝ) : Momentum where
  alpha := gamma
  beta _ := 0
  extrapolated := false
  reset _ := false

/-- The actual N-call causal history of the scalar gradient-step schedule. -/
def history (N : ℕ) (gamma : ℕ → ℝ) : bezout.History N := (config gamma).history N

/-- The exact zero-momentum spectral matrix. -/
theorem matrix_eq (gamma : ℕ → ℝ) (s : ℕ) (lam : ℝ) :
    (config gamma).matrix s lam = !![1-gamma s*lam,0;1,0] := by
  simp [Momentum.matrix,Momentum.baseMatrix,config]

/-- Every finite ordered product has precisely the scalar residual in its first row. -/
theorem product_row (gamma : ℕ → ℝ) (start n : ℕ) (lam : ℝ) :
    (orderedProduct (fun i => (config gamma).matrix (start+i) lam) n) 0 =
      ![orderedProduct (fun i => 1-gamma (start+i)*lam) n,0] := by
  induction n with
  | zero => ext j; fin_cases j <;> simp
  | succ n ih =>
    have h0 := congrFun ih 0
    have h1 := congrFun ih 1
    ext j
    fin_cases j <;>
      simp [orderedProduct_succ, Matrix.mul_apply, Fin.sum_univ_two, matrix_eq gamma (start+n) lam, h0, h1]

/-- The scalar first row acts independently of the initial previous-state slot. -/
theorem product_action (gamma : ℕ → ℝ) (start n : ℕ) (lam x p : ℝ) :
    (orderedProduct (fun i => (config gamma).matrix (start+i) lam) n *ᵥ ![x,p]) 0 =
      orderedProduct (fun i => 1-gamma (start+i)*lam) n * x := by
  have h0 := congrFun (product_row gamma start n lam) 0
  have h1 := congrFun (product_row gamma start n lam) 1
  simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, h0, h1]

/-- The actual terminal is exactly the existing scalar stepsize residual polynomial. -/
theorem terminal (N : ℕ) (gamma : ℕ → ℝ) :
    (history N gamma).terminal = chebyshev1.Stepsize.polynomial gamma N := by
  apply Polynomial.funext
  intro lam
  rw [history, Momentum.terminal_eval]
  have hp := product_action gamma 0 N lam 1 1
  rw [chebyshev1.Stepsize.polynomial_eval, chebyshev1.Stepsize.scalarTransfer_eq]
  simpa only [Nat.zero_add,mul_one] using hp

/-- The nominal physical query is the scalar prefix product before that call. -/
theorem query_eval (N : ℕ) (gamma : ℕ → ℝ) (s : Fin N) (lam : ℝ) :
    ((history N gamma).query s).eval lam =
      orderedProduct (fun i => 1-gamma i*lam) s.val := by
  rw [history, Momentum.query_eval_actual, Momentum.queryAt_eq]
  simp only [Momentum.query, config, Bool.false_eq_true, ite_false]
  have hp := (config gamma).scalarState_eq_linearRun N lam 1 (fun _ => 0) s.val
    (Nat.le_of_lt s.isLt)
  have hz : (config gamma).scalarForcing N (fun _ => 0) = fun _ => 0 := by
    funext j
    simp [Momentum.scalarForcing]
  rw [hz, linearRun_expansion] at hp
  simp only [Matrix.mulVec_zero, Finset.sum_const_zero, add_zero] at hp
  have h0 := congrFun hp 0
  simp only [Momentum.scalarState, Matrix.cons_val_zero] at h0
  change (((config gamma).program N).runPrefix (Momentum.scalarOracle N lam (fun _ => 0)) 1 s.val).vectors 0 = _
  rw [h0]
  simpa only [Nat.zero_add,mul_one] using product_action gamma 0 s.val lam 1 1

/-- Exact query-polynomial prefix identity, with no nonzero-step assumption. -/
theorem query_polynomial (N : ℕ) (gamma : ℕ → ℝ) (s : Fin N) :
    (history N gamma).query s = chebyshev1.Stepsize.polynomial gamma s.val := by
  apply Polynomial.funext
  intro lam
  rw [query_eval, chebyshev1.Stepsize.polynomial_eval, chebyshev1.Stepsize.scalarTransfer_eq]

/-- The exact physical response to an oracle error is its signed suffix product. -/
theorem response_eval (N : ℕ) (gamma : ℕ → ℝ) (s : Fin N) (lam : ℝ) :
    ((history N gamma).response s).eval lam =
      -gamma s.val * orderedProduct (fun i => 1-gamma (s.val+1+i)*lam) (N-(s.val+1)) := by
  rw [history, Momentum.response_eval]
  rw [product_action]
  simp [config]

/-- The actual history's two-variable physical kernel is exactly the established
stepsize realization kernel, including every chronological prefix and suffix. -/
theorem realization_kernel (N : ℕ) (gamma : ℕ → ℝ) (s : Fin N) (x y : ℝ) :
    (history N gamma).realization.kernel N s.val x y =
      (chebyshev1.Stepsize.realization gamma).kernel N s.val x y := by
  rw [bezout.History.realization_kernel, query_eval, response_eval,
    chebyshev1.Stepsize.kernel_formula]
  ring

end
end bezout.Comparisons.Competitors.Stepsize
