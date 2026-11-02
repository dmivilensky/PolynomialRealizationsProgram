import krylov.Convergence.CharacteristicRoots

/-!
Article: main_krylov, thm:G, thm:ss1F and Table s7-orders.
Use: prove the printed characteristic-root comparisons and genuine improved
one-gradient order, with exact treatment of dimension one.
Source: monotonicity of the characteristic polynomial above one.
-/
namespace krylov.Convergence
noncomputable section
open Set

/-- The corrected one-dimensional secant root is exactly two.
Article: main_krylov, the Davidon comparison after thm:ss1F. -/
theorem oneGradientRoot_one : oneGradientRoot 1=2 := by
  symm
  apply secantRoot_unique 0 0 le_rfl (by norm_num)
  norm_num

/-- The genuine one-gradient characteristic root decreases strictly with
its delay, proving the stated strict improvement from n+1 to n.
Article: main_krylov, thm:ss1F and Table s7-orders. -/
theorem oneGradientRoot_strictAnti {m n : ℕ} (hm : 0<m) (hmn : m<n) :
    oneGradientRoot n<oneGradientRoot m := by
  let x := oneGradientRoot m
  have hx : 1<x := secantRoot_gt_one (m-1) 0
  have hp : x^(m-1)*(x-1)=1 := by
    simpa only [x,oneGradientRoot,characteristicPolynomial,Nat.sub_zero,zero_add,pow_one] using
      secantRoot_polynomial (m-1) 0
  have hl : 1<characteristicPolynomial (n-1) 0 x := by
    have hh := mul_lt_mul_of_pos_right (pow_lt_pow_right₀ hx (by omega : m-1<n-1)) (sub_pos.mpr hx)
    simp only [characteristicPolynomial,Nat.sub_zero,zero_add,pow_one]
    linarith only [hh,hp]
  by_contra hn
  have hle : x≤oneGradientRoot n := not_lt.mp hn
  have hh := (characteristicPolynomial_strictMono (n-1) 0).monotoneOn hx.le
    (secantRoot_gt_one (n-1) 0).le hle
  rw [secantRoot_polynomial] at hh
  exact (not_le_of_gt hl) hh

/-- Taking a true positive integral root gives the exact printed real power.
Article: main_krylov, the per-iteration and per-gradient table exponents. -/
theorem rpow_inverse_nat_pow {a : ℝ} (ha : 0<a) {n : ℕ} (hn : 0<n) :
    (a^(1/(n:ℝ)))^n=a := by
  rw [←Real.rpow_mul_natCast ha.le]
  have he : (1/(n:ℝ))*(n:ℝ)=1 := by field_simp
  rw [he,Real.rpow_one]

/-- Full-conjugacy sliding order strictly exceeds the classical restarted
quadratic per-iteration guarantee. Article: main_krylov, thm:G. -/
theorem fullConjugacyRoot_gt_restarted {n : ℕ} (hn : 2≤n) :
    (2:ℝ)^(1/(n:ℝ))<fullConjugacyRoot n := by
  have hτ : 1<fullConjugacyRoot n := secantRoot_gt_one _ _
  apply lt_of_pow_lt_pow_left₀ n (zero_lt_one.trans hτ).le
  rw [rpow_inverse_nat_pow (by norm_num) (by omega : 0<n),fullConjugacyRoot_equation hn]
  linarith only [hτ]

/-- In dimension two the corrected secant and sliding FC guarantees coincide.
Article: krylov, comparison following Table s7-orders. -/
theorem oneGradientRoot_two_eq_fullConjugacyRoot :
    oneGradientRoot 2 = fullConjugacyRoot 2 := rfl

/-- Under their respective hypotheses the corrected secant exponent exceeds
the classical exact-search FC/BFGS exponent in dimensions at least three.
This compares guaranteed exponents, not exact orders of individual runs.
Article: krylov, comparison following Table s7-orders. -/
theorem fullConjugacyRoot_lt_oneGradientRoot {n : ℕ} (hn : 3≤n) :
    fullConjugacyRoot n < oneGradientRoot n := by
  let x := oneGradientRoot n
  have hx : 1<x := secantRoot_gt_one _ _
  have hp : x^(n-1)>x := by
    simpa only [pow_one] using pow_lt_pow_right₀ hx (by omega : 1<n-1)
  have he : x^(n-1)*x=x^(n-1)+1 := by
    rw [←pow_succ, show n-1+1=n by omega]
    exact oneGradientRoot_equation (by omega : 0<n)
  have hl : 1<characteristicPolynomial (n-1) (n-2) x := by
    simp only [characteristicPolynomial, show n-1-(n-2)=1 by omega,
      show n-2+1=n-1 by omega, pow_one]
    nlinarith only [hp,he]
  by_contra h
  have hh := (characteristicPolynomial_strictMono (n-1) (n-2)).monotoneOn
    hx.le (secantRoot_gt_one _ _).le (not_lt.mp h)
  rw [secantRoot_polynomial] at hh
  exact (not_le_of_gt hl) hh

end
end krylov.Convergence
