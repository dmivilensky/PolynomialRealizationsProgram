import jacobi.Jacobi.OrderedReflection
import jacobi.Jacobi.DerivativeIdentity

/-!
Article: jacobi, Lemma C.1.
The classical Gegenbauer function is defined by its standard terminating
community hypergeometric formula, including its Pochhammer normalization.
Its normalized polynomial is the actual equal-parameter Jacobi polynomial.
Source: the classical hypergeometric definition, DLMF 18.5.9.
Use: identifies the Jacobi specialization used for the later Poeschl--Teller reference eigenfunctions, without a second polynomial recurrence package.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Complex
open scoped Nat

/-- The classical Gegenbauer polynomial through its standard terminating 2F1 definition.
Use: identifies the Jacobi specialization used for the later Poeschl--Teller reference eigenfunctions, without a second polynomial recurrence package.
Article: jacobi, Lemma C.1.
Source: DLMF 18.5.9, the hypergeometric definition of the Gegenbauer polynomial. -/
def gegenbauer (g : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (ascPochhammer ℂ n).eval (2*g)/(n.factorial:ℂ)*
    ordinaryHypergeometric (-(n:ℂ)) (n+2*g) (g+1/2) ((1-z)/2)

/-- The genuine Gegenbauer polynomial is exactly a scalar multiple of the original equal-parameter Jacobi polynomial.
Use: all actual Jacobi analyticity, differential equations and finite zero results transfer to the reference Gegenbauer functions.
Article: jacobi, Lemma C.1.
Proof: the two original community hypergeometric functions have identical numerator, denominator and argument parameters after elementary algebra. -/
theorem gegenbauer_eq_jacobi (g : ℂ) (n : ℕ) (z : ℂ) :
    gegenbauer g n z=(ascPochhammer ℂ n).eval (2*g)/(n.factorial:ℂ)*
      normalized (g-1/2) (g-1/2) n z := by
  unfold gegenbauer normalized
  congr 2 <;> ring

/-- The actual Gegenbauer endpoint value is its precise classical Pochhammer normalization.
Use: normalization by C_n^(gamma)(1) in the reference eigenfunctions is the literal original value.
Article: jacobi, Lemma C.1.
Proof: specialize the actual Jacobi identity at its already proved normalization endpoint. -/
theorem gegenbauer_one (g : ℂ) (n : ℕ) :
    gegenbauer g n 1=(ascPochhammer ℂ n).eval (2*g)/(n.factorial:ℂ) := by
  rw [gegenbauer_eq_jacobi,normalized_one,mul_one]

/-- The genuine Gegenbauer endpoint normalization is nonzero throughout the reference parameter range.
Use: the source's normalized Gegenbauer eigenfunctions and their zero sets have no exceptional normalization case.
Article: jacobi, Lemma C.1.
Proof: the positive real part excludes every Pochhammer pole or zero;
the natural factorial is nonzero in the characteristic-zero complex field. -/
theorem gegenbauer_one_ne_zero {g : ℂ} (hg : 0<g.re) (n : ℕ) : gegenbauer g n 1≠0 := by
  rw [gegenbauer_one]
  apply div_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero n)
  have h := jacobi.Bessel.pochhammer_ne_zero (a := 2*g-1) (by
    norm_num
    linarith) n
  simpa only [sub_add_cancel] using h

/-- The normalized classical Gegenbauer polynomial is exactly the previously constructed normalized Jacobi polynomial.
Use: supplies the literal C_n^(gamma)(x)/C_n^(gamma)(1) factor in the reference eigenfunctions, reusing all finite Jacobi proofs.
Article: jacobi, Lemma C.1.
Proof: the two actual special-function definitions agree up to their
already evaluated common endpoint scalar, proved nonzero in the full range. -/
theorem gegenbauer_normalized {g : ℂ} (hg : 0<g.re) (n : ℕ) (z : ℂ) :
    gegenbauer g n z/gegenbauer g n 1=normalized (g-1/2) (g-1/2) n z := by
  have hn := gegenbauer_one_ne_zero hg n
  rw [gegenbauer_one] at hn
  rw [gegenbauer_eq_jacobi,gegenbauer_one]
  exact mul_div_cancel_left₀ _ hn

/-- The genuine Gegenbauer polynomial has precisely the same zeros as the genuine equal-parameter Jacobi polynomial.
Use: transfers the complete finite real simple-zero theory to the reference polynomials.
Article: jacobi, Lemma C.1.
Proof: cancel the actual nonzero endpoint scalar in the proved exact special-function identity. -/
theorem gegenbauer_zero_iff {g : ℂ} (hg : 0<g.re) (n : ℕ) (z : ℂ) :
    gegenbauer g n z=0 ↔ normalized (g-1/2) (g-1/2) n z=0 := by
  have hn := gegenbauer_one_ne_zero hg n
  rw [gegenbauer_one] at hn
  rw [gegenbauer_eq_jacobi,mul_eq_zero,or_iff_right hn]

end
end jacobi.Jacobi
