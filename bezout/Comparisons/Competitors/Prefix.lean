import bezout.Comparisons.Competitors.TwoTerm
import bezout.Comparisons.Classical.History
import chebyshev1.Jacobi.Prefix

/-!
Article: bezout, classical Prefix competitor in Appendix D.
Use: the literal current-query momentum coefficients implement exactly the
classical unrestricted history used in the finite gain and variance comparisons.
Proof: normalized Jacobi coefficients reproduce the printed alpha and beta;
the actual nominal prefixes identify the unique graded causal history.
-/

namespace bezout.Comparisons.Competitors.Prefix
noncomputable section
open chebyshev1 Polynomial

/-- Literal Prefix momentum coefficients through its normalized Jacobi method. -/
def config (I : SpectralInterval) : Momentum := TwoTerm.config (chebyshev1.Prefix.jacobiData.method I)

/-- The actual N-call Prefix history. -/
def history (I : SpectralInterval) (N : ℕ) : bezout.History N := (config I).history N

/-- Fixed-point normalization holds at every noninitial Prefix call. -/
theorem fixed_point (I : SpectralInterval) (N s : ℕ) (hs : 0<s) (hsN : s<N) :
    (chebyshev1.Prefix.jacobiData.method I).a s+(chebyshev1.Prefix.jacobiData.method I).b s=1 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
  exact chebyshev1.Prefix.jacobiData.fixed_point I n
    (ne_of_gt (chebyshev1.Prefix.jacobi_admissible I N (n+2) (by omega)))

/-- The separately prescribed initial step and zero initial momentum. -/
theorem initial_coefficients (I : SpectralInterval) :
    (config I).alpha 0=2/(I.L+I.mu) ∧ (config I).beta 0=0 := by
  simp [config,TwoTerm.config,chebyshev1.Prefix.jacobi_gamma,chebyshev1.Prefix.gamma]

/-- Every later used coefficient equals the printed classical Chebyshev formula. -/
theorem coefficients_succ (I : SpectralInterval) (s : ℕ) :
    (config I).alpha (s+1)=4*I.den (s+1)/(I.delta*I.den (s+2)) ∧
      (config I).beta (s+1)=I.den s/I.den (s+2) := by
  simp [config,TwoTerm.config,chebyshev1.Prefix.jacobi_gamma,chebyshev1.Prefix.gamma,
    chebyshev1.Prefix.jacobi_b_succ]

/-- The actual terminal polynomial is the prescribed normalized Chebyshev terminal. -/
theorem terminal (I : SpectralInterval) (N : ℕ) : (history I N).terminal=I.residual N := by
  rw [history,config,TwoTerm.terminal _ N (fixed_point I N),
    ← JacobiData.realization,chebyshev1.Prefix.jacobi_realization,
    chebyshev1.Prefix.residualPolynomial_eq]

/-- Actual Prefix query polynomials are the complete normalized Chebyshev prefixes. -/
theorem query_polynomial (I : SpectralInterval) (N : ℕ) (s : Fin N) :
    (history I N).query s=I.residual s.val := by
  apply Polynomial.funext
  intro lam
  rw [history,config,TwoTerm.query_eval _ N (fixed_point I N),
    ← JacobiData.realization,chebyshev1.Prefix.jacobi_realization,chebyshev1.Prefix.scalar_exact]

/-- The literal Prefix oracle program realizes exactly the classical comparison history. -/
theorem history_eq_classical (I : SpectralInterval) (N : ℕ) :
    history I N=bezout.Classical.history I N := by
  apply (bezout.Classical.queryFamily I N).realize_unique I (bezout.Classical.queryFamily_eta I N)
  · exact terminal I N
  · intro s
    simp only [bezout.History.chartQuery,query_polynomial,chebyshev1.SpectralInterval.residual,
      mul_comp,C_comp,comp_assoc,bezout.GradedFamily.coordinate_comp_chart,comp_X]
    simp only [bezout.Classical.queryFamily,one_div]

/-- Every actual physical Prefix output is the classical history output for any oracle stream. -/
theorem output_eq_classical {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : SpectralInterval) (N : ℕ) (oracle : Fin N → E → E) (initial : E) :
    ((config I).program N).output oracle initial=(bezout.Classical.history I N).oracleOutput initial oracle := by
  rw [Momentum.output_eq_history,← history_eq_classical]
  rfl

end
end bezout.Comparisons.Competitors.Prefix
