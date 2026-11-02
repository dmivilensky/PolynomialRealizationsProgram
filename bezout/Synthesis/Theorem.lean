import bezout.Synthesis.Normalized
import bezout.History.Execution
import bezout.History.Continuity

/-!
Article: bezout, Theorem 2.1 (`thm:bezout`).
Use: the realization equivalence packages the forward and constructive
converse classification into inverse actual constructions. The physical
response and normalized factorization statements are assembled alongside it.
Proof: the checked causal execution, maximal-path degrees, affine coordinate
transport and graded-basis uniqueness theorems.
-/

namespace bezout
noncomputable section
open Polynomial
open scoped BigOperators

/-- Graded families are determined by their actual polynomial vectors.
Use: the right inverse of the realization classification. -/
theorem gradedFamily_ext {N : ℕ} {P Q : GradedFamily N}
    (h : ∀ s, P.poly s = Q.poly s) : P = Q := by
  have hp : P.poly = Q.poly := funext h
  cases P
  cases Q
  simp_all

/-- The actual terminal-exact histories are equivalent to all eta-normalized
graded query families. This packages both directions and uniqueness in
Theorem 2.1, including unrestricted real coefficients and unrestricted memory. -/
def realizationEquiv (N : ℕ) (hN : 0 < N) (I : chebyshev1.SpectralInterval) :
    {h : History N // h.ChebyshevExact I} ≃
      {Q : GradedFamily N // ∀ s, (Q.poly s).eval I.eta = 1} where
  toFun h := ⟨h.val.chartGraded I hN h.property, h.val.chartQuery_eta I⟩
  invFun Q := ⟨Q.val.realize I Q.property, Q.val.realize_exact I Q.property⟩
  left_inv h := by
    apply Subtype.ext
    exact ((h.val.chartGraded I hN h.property).realize_unique I
      (h.val.chartQuery_eta I) h.val h.property (fun _ => rfl)).symm
  right_inv Q := by
    apply Subtype.ext
    apply gradedFamily_ext
    intro s
    exact Q.val.realize_chartQuery I Q.property s

/-- The complete normalized algebraic identity of Theorem 2.1 for an actual history.
Use: a single entry point records both degree orders, normalization, the physical
Bezoutian, continuous diagonal extension and the normalized factorization. -/
theorem realization_identity {N : ℕ} (h : History N) (hN : 0 < N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) :
    (∀ s, (h.query s).degree = (s.val : WithBot ℕ) ∧
      (h.response s).degree = ((N - 1 - s.val : ℕ) : WithBot ℕ)) ∧
    (∀ s, (h.chartQuery I s).degree = (s.val : WithBot ℕ) ∧
      (h.chartFactor I s).degree = ((N - 1 - s.val : ℕ) : WithBot ℕ) ∧
      (h.chartQuery I s).eval I.eta = 1) ∧
    (∀ x y : ℝ, (∑ s, (h.response s).eval x * (h.query s).eval y) =
      History.dividedDifference h.terminal x y) ∧
    Continuous (fun xy : ℝ × ℝ => History.dividedDifference h.terminal xy.1 xy.2) ∧
    (∀ x y : ℝ, (∑ s, (h.chartFactor I s).eval x * (h.chartQuery I s).eval y) =
      chebyshevBezout N x y) := by
  exact ⟨fun s => ⟨h.query_degree_eq hN (h.exact_terminal_natDegree I he) s,
      h.response_degree_eq hN (h.exact_terminal_natDegree I he) s⟩,
    fun s => ⟨h.chartQuery_degree I hN he s, h.chartFactor_degree I hN he s,
      h.chartQuery_eta I s⟩,
    h.physical_bezout_all, h.continuous_physical_bezout, h.chart_factorization I he⟩

namespace History
variable {N : ℕ}

/-- The normalized query evaluated in physical spectral coordinates is the actual query.
Use: the explicit change-of-coordinate dictionary in Theorem 2.1. -/
theorem chartQuery_physical_eval (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (s : Fin N) (lam : ℝ) :
    (h.chartQuery I s).eval (I.z lam) = (h.query s).eval lam := by
  have hc := congrArg (fun p : ℝ[X] => p.eval lam) (GradedFamily.chart_comp_coordinate I)
  simp only [eval_comp, eval_sub, eval_C, eval_mul, eval_X] at hc
  rw [← I.z_eq] at hc
  simp only [chartQuery, eval_comp, hc]

/-- The normalized factor recovers the actual physical response with the article's exact scale.
Use: transfers spectral energies of `f_s` back to physical oracle sensitivities. -/
theorem chartFactor_physical_eval (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (s : Fin N) (lam : ℝ) :
    (h.response s).eval lam =
      (-4 * I.epsilon N / I.delta) * (h.chartFactor I s).eval (I.z lam) := by
  have hd : I.delta ≠ 0 := ne_of_gt I.delta_pos
  have he : I.epsilon N ≠ 0 := one_div_ne_zero (I.den_ne N)
  have hc := congrArg (fun p : ℝ[X] => p.eval lam) (GradedFamily.chart_comp_coordinate I)
  simp only [eval_comp, eval_sub, eval_C, eval_mul, eval_X] at hc
  rw [← I.z_eq] at hc
  simp only [chartFactor, eval_mul, eval_C, eval_comp, hc]
  field_simp

end History

end
end bezout
