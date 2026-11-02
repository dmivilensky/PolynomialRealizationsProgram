import jacobi.Bessel.Convergence

/-!
Article: jacobi, Lemma C.1.
The genuine entire Bessel coefficients are expressed using the same rising
Pochhammer symbol as the existing Jacobi hypergeometric polynomial. Every
factor is proved nonzero throughout the article's admissible order range.
Source: the Gamma/Pochhammer identity proved in mathlib, DLMF 5.5.1 and 5.2.5.
Use: applies the community Gamma/Pochhammer theorem without an unproved pole-avoidance premise.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Polynomial
open scoped Nat
set_option backward.isDefEq.respectTransparency false

/-- The stated order range excludes every nonpositive-integer shifted-order pole.
Use: applies the community Gamma/Pochhammer theorem without an unproved pole-avoidance premise.
Article: jacobi, Lemma C.1.
Proof: equality with a negative natural would contradict positivity of the real shifted order. -/
theorem shifted_order_not_neg_nat {a : ℂ} (ha : -1<a.re) (n : ℕ) : a+1≠-(n:ℂ) := by
  intro hn
  have hh := congrArg Complex.re hn
  simp only [add_re,one_re,neg_re,natCast_re] at hh
  have hp : (0:ℝ)≤n := Nat.cast_nonneg n
  linarith

/-- Every rising-order Pochhammer factor is nonzero in the article's full admissible order range.
Use: finite Jacobi/Bessel coefficient comparisons cancel only genuine nonzero factors.
Article: jacobi, Proposition A.1.
Proof: the proved Gamma ratio equals the Pochhammer symbol and its two Gamma values are nonzero. -/
theorem pochhammer_ne_zero {a : ℂ} (ha : -1<a.re) (n : ℕ) :
    (ascPochhammer ℂ n).eval (a+1)≠0 := by
  rw [← Gamma_add_nat_div_Gamma_eq (a+1) (shifted_order_not_neg_nat ha)]
  exact div_ne_zero (order_nonzero ha n).2
    (by simpa only [Nat.cast_zero,add_zero] using (order_nonzero ha 0).2)

/-- The actual normalized Bessel coefficient has exactly the common Jacobi rising-factorial denominator.
Use: the Mehler--Heine proof can compare genuine finite and entire coefficients directly, without duplicate special-function definitions.
Article: jacobi, Proposition A.1.
Proof: replace the Pochhammer symbol by its proved actual Gamma ratio,
then cancel the nonzero Gamma normalization in the literal Bessel coefficient. -/
theorem coefficient_pochhammer {a : ℂ} (ha : -1<a.re) (n : ℕ) :
    coefficient a n=(-1/4:ℂ)^n/((n.factorial:ℂ)*(ascPochhammer ℂ n).eval (a+1)) := by
  -- The identity uses the article's full actual order range; no formal zero-denominator convention is invoked.
  rw [coefficient_formula,← Gamma_add_nat_div_Gamma_eq (a+1) (shifted_order_not_neg_nat ha)]
  have hg : Gamma (a+1)≠0 := by simpa only [Nat.cast_zero,add_zero] using (order_nonzero ha 0).2
  field_simp [hg]

/-- Every original normalized Bessel coefficient is nonzero throughout the full stated order range.
Use: excludes an accidentally terminating replacement for the genuine entire Bessel function.
Article: jacobi, Proposition A.1.
Proof: the scaling power, factorial and proved shifted Pochhammer factors are all nonzero. -/
theorem coefficient_ne_zero {a : ℂ} (ha : -1<a.re) (n : ℕ) : coefficient a n≠0 := by
  rw [coefficient_pochhammer ha]
  exact div_ne_zero (pow_ne_zero n (by norm_num))
    (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) (pochhammer_ne_zero ha n))

end
end jacobi.Bessel
