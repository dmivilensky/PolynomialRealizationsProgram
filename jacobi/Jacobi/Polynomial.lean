import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Tactic

/-!
Article: jacobi, Lemma C.1.
The Jacobi family is realized by its terminating community hypergeometric
series. Its normalized function is exactly a genuine finite polynomial;
termination, normalization and analyticity do not require a limiting or
zero-location hypothesis. The actual zeros and their asymptotic estimates
are separate obligations.
Source: the classical Jacobi hypergeometric formula, DLMF 18.5.7.
Use: its Mehler--Heine limit is the normalized Bessel series and its zeros define the finite edge spectrum.
-/
namespace jacobi.Jacobi
noncomputable section
open Complex Set Polynomial
open scoped Nat Topology
set_option backward.isDefEq.respectTransparency false

/-- The Jacobi polynomial normalized to one at the right endpoint.
Use: its Mehler--Heine limit is the normalized Bessel series and its zeros define the finite edge spectrum.
Article: jacobi, Lemma C.1.
-/
def normalized (a b : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ordinaryHypergeometric (-(n:ℂ)) (n+a+b+1) (a+1) ((1-x)/2)

/-- The literal terminating coefficients of the normalized Jacobi family.
Use: connects the finite Jacobi family with its rising-factorial and Bessel coefficient formulas.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
-/
def coefficient (a b : ℂ) (n k : ℕ) : ℂ :=
  ordinaryHypergeometricCoefficient (-(n:ℂ)) (n+a+b+1) (a+1) k

/-- The genuine finite normalized Jacobi polynomial over the complex coefficient field.
Use: imports the family into the existing polynomial and finite-realization foundations.
Article: jacobi, Lemma C.1.
-/
def normalizedPolynomial (a b : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k∈Finset.range (n+1),C (coefficient a b n k)*((1-X)*C (1/2:ℂ))^k

/-- The Jacobi hypergeometric series terminates exactly past its stated degree.
Use: finite polynomial identities apply to the actual defined hypergeometric function.
Article: jacobi, Lemma C.1.
Proof: the existing hypergeometric termination theorem applies to the actual first numerator parameter. -/
theorem series_terminates (a b : ℂ) (n k : ℕ) (hk : n<k) :
    ordinaryHypergeometricSeries ℂ (-(n:ℂ)) (n+a+b+1) (a+1) k=0 := by
  apply ordinaryHypergeometricSeries_eq_zero_of_neg_nat (k := n)
  · exact Or.inl (by simp)
  · exact hk

/-- The original normalized Jacobi function equals its precise finite hypergeometric sum at every complex point.
Use: proves the polynomial identification before taking asymptotic limits.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: every series term outside range(n+1) vanishes by the actual
termination theorem. Evaluate the zero multilinear coefficient at the
actual argument and apply the finite-support infinite-sum identity. -/
theorem normalized_eq_sum (a b : ℂ) (n : ℕ) (x : ℂ) :
    normalized a b n x=∑ k∈Finset.range (n+1),coefficient a b n k*((1-x)/2)^k := by
  -- The series is finite everywhere, so no unit-disc restriction is hidden in this identity.
  rw [normalized,ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  apply tsum_eq_sum
  intro k hk
  have hnk : n<k := by
    have hh : n+1≤k := by simpa only [Finset.mem_range,not_lt] using hk
    omega
  have hh := congrArg (fun f => f (fun _ => (1-x)/2)) (series_terminates a b n k hnk)
  rw [ordinaryHypergeometricSeries_apply_eq] at hh
  change coefficient a b n k*((1-x)/2)^k=0 at hh
  exact hh

/-- The normalized Jacobi function is exactly evaluation of the literal finite polynomial.
Use: connects the article's special-function definition with algebraic polynomial statements and finite realizations.
Article: jacobi, Lemma C.1.
Proof: evaluate the finite polynomial sum and use the proved exact terminating expansion. -/
theorem polynomial_eval (a b : ℂ) (n : ℕ) (x : ℂ) :
    (normalizedPolynomial a b n).eval x=normalized a b n x := by
  rw [normalized_eq_sum]
  simp only [normalizedPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_sub,eval_one,eval_X]
  congr 1
  funext k
  ring

/-- The actual normalized Jacobi polynomial has value one at its stated normalization endpoint.
Use: fixes the finite trace ratio and the normalization in the Mehler--Heine limit.
Article: jacobi, Lemma C.1.
Proof: the actual hypergeometric argument is zero and its zeroth coefficient is one. -/
theorem normalized_one (a b : ℂ) (n : ℕ) : normalized a b n 1=1 := by
  simp [normalized]

/-- The actual finite polynomial has the same exact right-endpoint normalization.
Use: algebraic arguments may evaluate the polynomial without returning to an infinite series.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: use the actual function-polynomial identity and its proved endpoint value. -/
theorem polynomial_one (a b : ℂ) (n : ℕ) : (normalizedPolynomial a b n).eval 1=1 := by
  rw [polynomial_eval,normalized_one]

/-- The actual normalized Jacobi function is entire in its polynomial argument.
Use: permits complex compact-uniform limits and Hurwitz arguments after their convergence hypotheses are proved.
Article: jacobi, Lemma C.1.
Proof: the actual function equals evaluation of its genuine finite polynomial, which is entire. -/
theorem normalized_analytic (a b : ℂ) (n : ℕ) (x : ℂ) : AnalyticAt ℂ (normalized a b n) x := by
  have he : normalized a b n=fun z => (normalizedPolynomial a b n).eval z :=
    funext fun z => (polynomial_eval a b n z).symm
  rw [he]
  exact AnalyticOnNhd.eval_polynomial (normalizedPolynomial a b n) x (mem_univ x)

end
end jacobi.Jacobi
