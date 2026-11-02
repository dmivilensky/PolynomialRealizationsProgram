import bezout.Balanced.Basis

/-!
Article: bezout, the Balanced construction in Theorem `thm:linear`.
Use: provides an actual terminal-exact causal history, rather than a list of
candidate factors. Its query polynomials have the exact prescribed chart basis.
Proof: apply constructive graded-basis synthesis after proving positive
normalizers and full query degrees.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The eta-normalized graded query family prescribed by Balanced. -/
def queryFamily (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    GradedFamily N where
  poly s := C (1 / normalizer I N s) * psi N s
  degree_eq s := by
    rw [degree_C_mul (one_div_ne_zero (ne_of_gt (normalizer_pos I hN s.isLt)))]
    exact psi_degree hN s.isLt

/-- Every normalized query takes value one at the zero-Hessian coordinate eta. -/
theorem queryFamily_eta (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : ((queryFamily I N hN).poly s).eval I.eta = 1 := by
  simp only [queryFamily, eval_mul, eval_C, normalizer]
  exact one_div_mul_cancel (ne_of_gt (normalizer_pos I hN s.isLt))

/-- The actual causal Balanced history produced by exact finite synthesis. -/
def history (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) : bezout.History N :=
  (queryFamily I N hN).realize I (queryFamily_eta I N hN)

/-- Balanced belongs to the full Chebyshev-exact history comparison class. -/
theorem history_exact (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (history I N hN).ChebyshevExact I :=
  (queryFamily I N hN).realize_exact I (queryFamily_eta I N hN)

/-- The constructed physical history has exactly the prescribed stopped-parity queries. -/
theorem history_chartQuery (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : (history I N hN).chartQuery I s =
      C (1 / normalizer I N s) * psi N s :=
  (queryFamily I N hN).realize_chartQuery I (queryFamily_eta I N hN) s

/-- The exact positive uniform bound on a normalized Balanced chart query. -/
theorem query_bound (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) {x : ℝ} (hx : |x| ≤ 1) :
    |((queryFamily I N hN).poly s).eval x| ≤ 1 / normalizer I N s := by
  simp only [queryFamily, eval_mul, eval_C, abs_mul,
    abs_of_pos (one_div_pos.mpr (normalizer_pos I hN s.isLt))]
  simpa using mul_le_mul_of_nonneg_left (abs_psi_eval_le_one hN s.isLt hx)
    (one_div_pos.mpr (normalizer_pos I hN s.isLt)).le

/-- All normalized chart query bounds are attained at the same endpoint. -/
theorem query_endpoint (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : ((queryFamily I N hN).poly s).eval 1 = 1 / normalizer I N s := by
  simp [queryFamily]

end
end bezout.Balanced
