import jacobi.Jacobi.Real

/-!
Article: jacobi, Theorem 5.1.
The original terminating community hypergeometric coefficients satisfy
the exact Jacobi recurrence, including their terminal and zero terms.
Source: DLMF 18.5.7 and the rising Pochhammer evaluation recurrence.
Use: the shifted polynomial coefficient theorem may use the original recurrence at every natural index.
-/
namespace jacobi.Jacobi
noncomputable section
open Complex Polynomial
open scoped Nat
set_option backward.isDefEq.respectTransparency false

/-- Every original Jacobi coefficient beyond the stated degree is zero.
Use: the shifted polynomial coefficient theorem may use the original recurrence at every natural index.
Article: jacobi, Theorem 5.1.
Proof: evaluate the already proved zero multilinear hypergeometric coefficient at the constant argument one. -/
theorem coefficient_terminates (a b : ℂ) {n k : ℕ} (hk : n<k) : coefficient a b n k=0 := by
  have h := congrArg (fun f => f (fun _ => (1:ℂ))) (series_terminates a b n k hk)
  simpa only [coefficient,ordinaryHypergeometricSeries_apply_eq,one_pow,smul_eq_mul,mul_one,
    zero_apply] using h

/-- The original Jacobi hypergeometric coefficients satisfy their full differential-equation recurrence.
Use: proves the actual polynomial differential equation without an assumed special-function identity.
Article: jacobi, Theorem 5.1.
Proof: substitute the three genuine next Pochhammer factors and the
next factorial. Only factorial and positive-real-part normalization
denominators are cancelled; the terminating numerator factor is retained. -/
theorem coefficient_equation {a b : ℂ} (ha : -1<a.re) (n k : ℕ) :
    (k+1:ℂ)*(a+1+k)*coefficient a b n (k+1)=
      (k-n:ℂ)*(n+a+b+1+k)*coefficient a b n k := by
  -- This identity also holds at k=n and beyond the terminal degree.
  have hP := jacobi.Bessel.pochhammer_ne_zero ha k
  have hshift := (jacobi.Bessel.order_nonzero ha k).1
  have hfac : (k.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero k
  unfold coefficient ordinaryHypergeometricCoefficient
  rw [ascPochhammer_succ_eval,ascPochhammer_succ_eval,ascPochhammer_succ_eval,Nat.factorial_succ]
  push_cast
  field_simp [hP,hshift,hfac,hk]
  ring

/-- The real parts of the actual Jacobi coefficients satisfy the genuine real Jacobi recurrence.
Use: verifies the real shifted polynomial equation used in Sturm orthogonality and zero location.
Article: jacobi, Theorem 5.1.
Proof: take real parts of the already proved complex coefficient equation; all scalar recurrence factors are real. -/
theorem real_coefficient_equation {a b : ℝ} (ha : -1<a) (n k : ℕ) :
    (k+1:ℝ)*(a+1+k)*(coefficient (a:ℂ) (b:ℂ) n (k+1)).re=
      (k-n:ℝ)*(n+a+b+1+k)*(coefficient (a:ℂ) (b:ℂ) n k).re := by
  have h := congrArg Complex.re (coefficient_equation (a := (a:ℂ)) (b := (b:ℂ)) (by simpa using ha) n k)
  simpa [Complex.mul_re] using h

end
end jacobi.Jacobi
