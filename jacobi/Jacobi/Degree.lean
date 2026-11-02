import jacobi.Jacobi.ShiftedPolynomial
import Mathlib.Algebra.Polynomial.Sequence

/-!
Article: jacobi, Proposition 6.1.
The shifted real polynomials have exactly their stated degrees throughout
alpha,beta>-1. They form the community degree-graded polynomial sequence,
which will supply all lower-degree test polynomials for orthogonality.
Source: the terminating hypergeometric formula and Polynomial.Sequence.
Use: excludes degree loss before root counting, finite factorization and trace computations.
-/
namespace jacobi.Jacobi
noncomputable section
open Complex Polynomial Set
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false

/-- The terminal original Jacobi coefficient is nonzero in the full stated real parameter range.
Use: excludes degree loss before root counting, finite factorization and trace computations.
Article: jacobi, Proposition 6.1.
Proof: the numerator Pochhammer at -n has no zero among its first n
factors; the other numerator has positive real parameter for n>0.
The normalization denominator is nonzero by the proved order range. -/
theorem coefficient_top_ne_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    coefficient (a:ℂ) (b:ℂ) n n≠0 := by
  -- Every cancellation is justified even in the exceptional alpha+beta parameter slices.
  by_cases hn : n=0
  · subst n
    simp [coefficient,ordinaryHypergeometricCoefficient]
  have h1 : (ascPochhammer ℂ n).eval (-(n:ℂ))≠0 := by
    intro hz
    obtain ⟨k,hk,he⟩ := ascPochhammer_eval_eq_zero_iff _ _ |>.mp hz
    have he : k=n := by exact_mod_cast (by simpa only [neg_neg] using he : (k:ℂ)=(n:ℂ))
    omega
  have h2 : (ascPochhammer ℂ n).eval ((n:ℂ)+(a:ℂ)+(b:ℂ)+1)≠0 := by
    intro hz
    obtain ⟨k,_,he⟩ := ascPochhammer_eval_eq_zero_iff _ _ |>.mp hz
    have h := congrArg Complex.re he
    simp only [natCast_re,neg_re,add_re,ofReal_re,one_re] at h
    have hnpos : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hkpos : (0:ℝ)≤k := Nat.cast_nonneg k
    linarith
  unfold coefficient ordinaryHypergeometricCoefficient
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)) h1) h2)
    (inv_ne_zero (jacobi.Bessel.pochhammer_ne_zero (a := (a:ℂ)) (by simpa using ha) n))

/-- The top real shifted Jacobi coefficient is nonzero.
Use: proves the actual real polynomial's degree rather than only a complex coefficient formula.
Article: jacobi, Proposition A.1.
Proof: reality identifies the original complex coefficient with the embedded real part, already proved nonzero. -/
theorem shiftedPolynomial_top_ne_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (shiftedPolynomial a b n).coeff n≠0 := by
  rw [shiftedPolynomial_coeff]
  intro h
  apply coefficient_top_ne_zero ha hb n
  have he := Complex.conj_eq_iff_re.mp (coefficient_conj a b n n)
  rw [h,Complex.ofReal_zero] at he
  exact he.symm

/-- The shifted real Jacobi polynomial has exactly the stated natural degree.
Use: finite zero counts and polynomial bases use the actual source degree.
Article: jacobi, Proposition 6.1.
Proof: coefficients past n terminate and the coefficient at n is
nonzero. Apply the community polynomial degree characterization. -/
theorem shiftedPolynomial_natDegree {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (shiftedPolynomial a b n).natDegree=n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero ?_ (shiftedPolynomial_top_ne_zero ha hb n)
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [shiftedPolynomial_coeff,coefficient_terminates _ _ hk,Complex.zero_re]

/-- The shifted real Jacobi polynomial is nonzero for every degree.
Use: degree, root multiplicity and completeness arguments never invoke the zero-polynomial convention.
Article: jacobi, Proposition A.1.
Proof: its proved nonzero coefficient at the terminal degree excludes the zero polynomial. -/
theorem shiftedPolynomial_ne_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    shiftedPolynomial a b n≠0 := by
  intro h
  exact shiftedPolynomial_top_ne_zero ha hb n (by rw [h,coeff_zero])

/-- The actual shifted Jacobi family packaged as the community degree-graded polynomial sequence.
Use: its initial segments span all lower-degree test polynomials in the orthogonality proof.
Article: jacobi, Proposition C.2.
-/
def shiftedSequence (a b : ℝ) (ha : -1<a) (hb : -1<b) : Polynomial.Sequence ℝ where
  elems' := shiftedPolynomial a b
  degree_eq' n := by rw [degree_eq_natDegree (shiftedPolynomial_ne_zero ha hb n),shiftedPolynomial_natDegree ha hb]

/-- The actual shifted Jacobi polynomial obeys the exact real differential equation at every real argument.
Use: differentiating its weighted Wronskian gives the actual Sturm orthogonality identity.
Article: jacobi, Proposition 6.1.
Proof: evaluate the already proved literal polynomial equation and collect its affine coefficient factors. -/
theorem shiftedPolynomial_equation_eval {a b : ℝ} (ha : -1<a) (n : ℕ) (t : ℝ) :
    let q := shiftedPolynomial a b n
    t*(1-t)*q.derivative.derivative.eval t+
      (a+1-(a+b+2)*t)*q.derivative.eval t+(n:ℝ)*(n+a+b+1)*q.eval t=0 := by
  have h := congrArg (fun q : Polynomial ℝ => q.eval t) (shiftedPolynomial_equation (b := b) ha n)
  simp only [eval_add,eval_sub,eval_mul,eval_X,eval_C,eval_zero] at h
  linear_combination h

end
end jacobi.Jacobi
