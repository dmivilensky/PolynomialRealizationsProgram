import bezout.Synthesis.Chebyshev

/-!
Article: bezout, Theorem 2.1, forward and converse statements in the original chart.
Use: records exact degrees, eta normalization, unique response factors and the
unique Chebyshev-exact physical history constructed from an arbitrary graded
normalized query basis. Every history appearing here is the actual causal one.
Proof: maximal-path degrees and the two inverse affine substitutions, followed
by the constructive finite-coordinate synthesis theorem.
-/

namespace bezout
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

namespace History
variable {N : ℕ}

/-- The inverse spectral coordinate has nonzero linear coefficient.
Use: chart transport preserves every query and physical-response degree. -/
theorem chart_degree (I : chebyshev1.SpectralInterval) :
    (GradedFamily.chart I).degree = 1 := by
  have hc : I.delta / 2 ≠ 0 := div_ne_zero (ne_of_gt I.delta_pos) (by norm_num)
  rw [GradedFamily.chart, ← neg_sub, degree_neg,
    degree_sub_C (by simp [degree_C_mul_X hc]), degree_C_mul_X hc]

/-- The Chebyshev comparison class has full terminal degree.
Use: applies maximal-path exact grading to every history in the class. -/
theorem exact_terminal_natDegree (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) : h.terminal.natDegree = N := by
  rw [he]
  exact I.residual_natDegree N

/-- Exact query degrees in the normalized Chebyshev coordinate.
Use: the forward graded-basis assertion of Theorem 2.1. -/
theorem chartQuery_degree (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (hN : 0 < N) (he : h.ChebyshevExact I) (s : Fin N) :
    (h.chartQuery I s).degree = (s.val : WithBot ℕ) := by
  rw [chartQuery, degree_comp (by rw [chart_degree]; norm_num), chart_degree, mul_one]
  exact h.query_degree_eq hN (h.exact_terminal_natDegree I he) s

/-- Exact physical-response degrees in the normalized Chebyshev coordinate.
Use: proves the complementary degree order of the Bezoutian factors. -/
theorem chartFactor_degree (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (hN : 0 < N) (he : h.ChebyshevExact I) (s : Fin N) :
    (h.chartFactor I s).degree = ((N - 1 - s.val : ℕ) : WithBot ℕ) := by
  have hc : -I.delta / (4 * I.epsilon N) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (ne_of_gt I.delta_pos))
      (mul_ne_zero (by norm_num) (one_div_ne_zero (I.den_ne N)))
  rw [chartFactor, degree_C_mul hc, degree_comp (by rw [chart_degree]; norm_num),
    chart_degree, mul_one]
  exact h.response_degree_eq hN (h.exact_terminal_natDegree I he) s

/-- Every charted query is normalized to one at eta.
Use: the physical-history side satisfies the exact input normalization of the converse. -/
theorem chartQuery_eta (h : bezout.History N) (I : chebyshev1.SpectralInterval) (s : Fin N) :
    (h.chartQuery I s).eval I.eta = 1 := by
  have hc := congrArg (fun p : ℝ[X] => p.eval 0) (GradedFamily.chart_comp_coordinate I)
  simp only [eval_comp, eval_sub, eval_C, eval_mul, eval_X, mul_zero, sub_zero] at hc
  simp only [chartQuery, eval_comp, hc, h.query_eval_zero]

/-- The actual normalized query family of a Chebyshev-exact history.
Use: supplies coordinate uniqueness for the complete Bezoutian factorization. -/
def chartGraded (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (hN : 0 < N) (he : h.ChebyshevExact I) : GradedFamily N where
  poly := h.chartQuery I
  degree_eq := h.chartQuery_degree I hN he

/-- The actual normalized physical response factors are the unique separated factors.
Use: the final uniqueness assertion in Theorem 2.1, on the entire real plane. -/
theorem chart_factors_unique (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (hN : 0 < N) (he : h.ChebyshevExact I) (f : Fin N → ℝ[X])
    (hf : ∀ x y : ℝ, ∑ s, (f s).eval x * (h.chartQuery I s).eval y =
      chebyshevBezout N x y) : f = h.chartFactor I := by
  apply (h.chartGraded I hN he).factors_unique
  intro x y
  exact (hf x y).trans (h.chart_factorization I he x y).symm

end History

namespace GradedFamily
variable {N : ℕ} (Q : GradedFamily N)

/-- The Chebyshev terminal meets the zero-Hessian normalization used by synthesis.
Use: the constructed physical history is terminal-exact without an extra hypothesis. -/
theorem residual_zero (I : chebyshev1.SpectralInterval) : (I.residual N).eval 0 = 1 := by
  have hz : I.z 0 = I.eta := by simp [chebyshev1.SpectralInterval.z,
    chebyshev1.SpectralInterval.eta]
  rw [I.residual_eval, hz]
  exact div_self (I.den_ne N)

/-- Degree bound of the exact terminal, in the form needed by causal synthesis.
Use: produces output weights from the complete graded query family. -/
theorem residual_degree_le (I : chebyshev1.SpectralInterval) :
    (I.residual N).degree ≤ (N : WithBot ℕ) :=
  degree_le_of_natDegree_le (le_of_eq (I.residual_natDegree N))

/-- The actual history constructed from an eta-normalized graded basis.
Use: the converse direction of Theorem 2.1 in the article's original variable. -/
def realize (I : chebyshev1.SpectralInterval)
    (hQ : ∀ s, (Q.poly s).eval I.eta = 1) : bezout.History N :=
  (Q.normalizedPhysical I hQ).history (I.residual N) (residual_degree_le I)

/-- The constructed history has precisely the prescribed Chebyshev terminal.
Use: establishes membership in the unrestricted terminal-exact comparison class. -/
theorem realize_exact (I : chebyshev1.SpectralInterval)
    (hQ : ∀ s, (Q.poly s).eval I.eta = 1) : (Q.realize I hQ).ChebyshevExact I := by
  exact (Q.normalizedPhysical I hQ).history_terminal _ _ (residual_zero I)

/-- The input query basis is recovered exactly in the original Chebyshev coordinate.
Use: the converse realization preserves all supplied basis polynomials. -/
theorem realize_chartQuery (I : chebyshev1.SpectralInterval)
    (hQ : ∀ s, (Q.poly s).eval I.eta = 1) (s : Fin N) :
    (Q.realize I hQ).chartQuery I s = Q.poly s := by
  unfold History.chartQuery realize
  rw [(Q.normalizedPhysical I hQ).history_query]
  exact Q.physical_comp_chart I s

/-- A terminal-exact physical history with the supplied charted basis is the synthesized one.
Use: identifies arbitrary histories with the actual converse construction. -/
theorem realize_unique (I : chebyshev1.SpectralInterval)
    (hQ : ∀ s, (Q.poly s).eval I.eta = 1) (h : bezout.History N)
    (he : h.ChebyshevExact I) (hq : ∀ s, h.chartQuery I s = Q.poly s) :
    h = Q.realize I hQ := by
  have hqueries : h.query = (Q.normalizedPhysical I hQ).poly := by
    funext s
    have hc := congrArg (fun p : ℝ[X] => p.comp (C I.eta - C (2 / I.delta) * X)) (hq s)
    simpa only [History.chartQuery, comp_assoc, chart_comp_coordinate, comp_X,
      normalizedPhysical, physical] using hc
  exact (Q.normalizedPhysical I hQ).history_unique _ _ (residual_zero I) h hqueries he

/-- The normalized input basis determines a unique terminal-exact physical history.
Use: completes the existence-and-uniqueness statement of Theorem 2.1. -/
theorem existsUnique_realization (I : chebyshev1.SpectralInterval)
    (hQ : ∀ s, (Q.poly s).eval I.eta = 1) :
    ∃! h : bezout.History N,
      h.ChebyshevExact I ∧ ∀ s, h.chartQuery I s = Q.poly s := by
  exact ⟨Q.realize I hQ, ⟨Q.realize_exact I hQ, Q.realize_chartQuery I hQ⟩,
    fun h hh => Q.realize_unique I hQ h hh.1 hh.2⟩

end GradedFamily
end
end bezout
