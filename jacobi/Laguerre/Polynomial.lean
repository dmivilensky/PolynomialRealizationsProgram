import jacobi.Bessel.Pochhammer
import Mathlib.Data.Nat.Choose.Basic

/-!
Article: jacobi, Proposition 6.1.
The standard terminating coefficients define L_n^(a)/L_n^(a)(0).
The three-term recurrence is proved from Pascal's identity, so the later
matrix identification uses the classical polynomial rather than naming a
new polynomial after the desired matrix.
Source: DLMF 18.5.12 and 18.9.1, Laguerre coefficients and recurrence.
Use: polynomial and polynomial_recurrence identify the actual recurrence matrix with the source's classical L_n^(a).
-/
namespace jacobi.Laguerre
noncomputable section
open Polynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The standard coefficient of the Laguerre polynomial normalized at zero.
Use: polynomial and polynomial_recurrence identify the actual recurrence matrix with the source's classical L_n^(a).
Article: jacobi, Proposition 6.1.
Source: DLMF 18.5.12, (-1)^k*binomial(n,k)/(a+1)_k. -/
def coefficient (a:ℝ) (n k:ℕ) : ℝ :=
  (-1:ℝ)^k*(n.choose k:ℝ)/(ascPochhammer ℝ k).eval (a+1)

/-- The actual normalized Laguerre polynomial with its classical terminating coefficients.
Use: its matrix characteristic identity and compact uniform Mehler--Heine limit concern the same original polynomial.
Article: jacobi, Proposition 6.1.
Source: DLMF 18.5.12, the finite confluent hypergeometric formula. -/
def polynomial (a:ℝ) (n:ℕ) : Polynomial ℝ :=
  ∑k∈Finset.range (n+1),C (coefficient a n k)*X^k

/-- Every actual Laguerre coefficient vanishes beyond its degree.
Use: polynomial_coeff retains the literal classical coefficient at every index, including the terminated tail.
Article: jacobi, Proposition 6.1.
Proof: the genuine natural binomial coefficient is zero past its degree. -/
theorem coefficient_terminates (a:ℝ) {n k:ℕ} (hk:n<k) : coefficient a n k=0 := by
  simp only [coefficient,Nat.choose_eq_zero_of_lt hk,Nat.cast_zero,mul_zero,zero_div]

/-- Coefficient extraction from the actual finite polynomial gives the original Laguerre coefficient at every degree.
Use: polynomial_recurrence proves an identity of the actual classical polynomials by coefficient comparison.
Article: jacobi, Proposition 6.1.
Proof: the finite monomial sum selects its matching index; outside its range the genuine coefficient terminates. -/
theorem polynomial_coeff (a:ℝ) (n k:ℕ) : (polynomial a n).coeff k=coefficient a n k := by
  classical
  simp only [polynomial,finsetSum_coeff,coeff_C_mul_X_pow,Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · exact (coefficient_terminates a (by simpa only [Finset.mem_range,not_lt,Nat.add_one_le_iff] using hk)).symm

/-- The denominator in every classical normalized Laguerre coefficient is strictly positive throughout a>-1.
Use: coefficient_recurrence clears only actual nonzero normalization factors.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: the community rising-factorial positivity theorem applies to a+1>0. -/
theorem denominator_pos {a:ℝ} (ha:-1<a) (k:ℕ) :
    0<(ascPochhammer ℝ k).eval (a+1) :=
  ascPochhammer_pos k (a+1) (by linarith)

/-- The neighboring binomial coefficients have their exact real weighted identity, with no truncated-index restriction.
Use: coefficient_recurrence proves the Laguerre recurrence even beyond either terminating degree.
Article: jacobi, Proposition 6.1.
Source: Pascal's identity and the standard binomial multiplication formula.
Proof: within range, cast the natural binomial formula and its genuine subtraction; past the range both binomial coefficients vanish. -/
private theorem choose_weight (n k:ℕ) :
    (n+1:ℝ)*(n.choose k:ℝ)=(n+1-(k:ℝ))*((n+1).choose k:ℝ) := by
  by_cases hk:k≤n+1
  · have h := congrArg (fun m:ℕ=>(m:ℝ)) (Nat.choose_mul_succ_eq n k)
    push_cast [Nat.cast_sub hk] at h
    nlinarith only [h]
  · have hn:n<k := by omega
    simp only [Nat.choose_eq_zero_of_lt hn,Nat.choose_eq_zero_of_lt (by omega : n+1<k),
      Nat.cast_zero,mul_zero]

/-- The literal classical Laguerre coefficients obey the full normalized three-term recurrence.
Use: polynomial_recurrence identifies the actual classical polynomial with the genuine Laguerre Jacobi determinant.
Article: jacobi, Section 6 (bidiagonal swap identity).
Source: DLMF 18.9.1.
Proof: Pascal's two identities and the weighted binomial identity
give the numerator recurrence. The actual rising factorial gains
a+k+1 and the alternating coefficient gains one minus sign. -/
theorem coefficient_recurrence {a:ℝ} (ha:-1<a) (n k:ℕ) :
    (n+a+2)*coefficient a (n+2) (k+1)=
      (2*n+a+3)*coefficient a (n+1) (k+1)-coefficient a (n+1) k-
        (n+1)*coefficient a n (k+1) := by
  -- All coefficient indices are unrestricted; true termination handles the finite boundary.
  have h1:((n+1).choose (k+1):ℝ)=(n.choose k:ℝ)+(n.choose (k+1):ℝ) := by
    exact_mod_cast Nat.choose_succ_succ n k
  have h2:((n+2).choose (k+1):ℝ)=((n+1).choose k:ℝ)+((n+1).choose (k+1):ℝ) := by
    exact_mod_cast Nat.choose_succ_succ (n+1) k
  have hc:(n+a+2)*((n+2).choose (k+1):ℝ)=
      (2*n+a+3)*((n+1).choose (k+1):ℝ)+(a+k+1)*((n+1).choose k:ℝ)-
        (n+1)*(n.choose (k+1):ℝ) := by
    rw [h2,h1]
    nlinarith only [choose_weight n k]
  unfold coefficient
  rw [ascPochhammer_succ_eval,pow_succ]
  have hD := (denominator_pos ha k).ne'
  have hF: a+1+(k:ℝ)≠0 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  field_simp [hD,hF]
  linear_combination -hc

/-- Every original normalized Laguerre polynomial has value one at zero.
Use: its Mehler--Heine normalization and exact matrix characteristic scale are fixed by this actual endpoint value.
Article: jacobi, Proposition 6.1.
Proof: only the classical zeroth coefficient survives evaluation at zero. -/
theorem polynomial_zero_value (a:ℝ) (n:ℕ) : (polynomial a n).eval 0=1 := by
  rw [← coeff_zero_eq_eval_zero,polynomial_coeff]
  simp [coefficient]

/-- The genuine degree-zero normalized Laguerre polynomial is one.
Use: the later recurrence-matrix identification starts at the original empty determinant.
Article: jacobi, Proposition 6.1.
Proof: the original terminating sum has its single zeroth term. -/
theorem polynomial_zero (a:ℝ) : polynomial a 0=1 := by
  simp [polynomial,coefficient]

/-- The genuine degree-one normalized Laguerre polynomial is 1-y/(a+1).
Use: the recurrence-matrix identification uses the source's exact first diagonal a+1.
Article: jacobi, Proposition 6.1.
Proof: evaluate the two original terminating coefficients. -/
theorem polynomial_one (a:ℝ) : polynomial a 1=1-C (1/(a+1))*X := by
  ext k
  cases k with
  | zero => simp [polynomial_coeff,coefficient]
  | succ k =>
    cases k with
    | zero => simp [polynomial_coeff,coefficient,coeff_one,div_eq_mul_inv]
    | succ k =>
      simp [polynomial_coeff,coefficient,coeff_one,Nat.choose_eq_zero_of_lt (by omega : 1<k+1+1)]

/-- The full classical normalized Laguerre polynomials obey their exact three-term recurrence.
Use: characteristic_polynomial proves the complete original polynomial identification, not merely equality of limiting edge data.
Article: jacobi, Section 6 (bidiagonal swap identity).
Source: DLMF 18.9.1.
Proof: the constant coefficient is one in all three polynomials.
At every positive degree the proved literal coefficient recurrence
matches the coefficient of multiplication by the actual variable. -/
theorem polynomial_recurrence {a:ℝ} (ha:-1<a) (n:ℕ) :
    C (n+a+2)*polynomial a (n+2)=
      (C (2*n+a+3)-X)*polynomial a (n+1)-C ((n:ℝ)+1)*polynomial a n := by
  -- Polynomial extensionality includes the terminated tail, so this is a global identity.
  ext k
  cases k with
  | zero =>
    simp only [coeff_C_mul,coeff_sub,sub_mul,coeff_X_mul_zero,polynomial_coeff,coefficient,
      pow_zero,Nat.choose_zero_right,Nat.cast_one,ascPochhammer_zero,eval_one,mul_one,div_one]
    ring
  | succ k =>
    simp only [sub_mul,coeff_sub,coeff_C_mul,coeff_X_mul,polynomial_coeff]
    exact coefficient_recurrence ha n k

end
end jacobi.Laguerre
