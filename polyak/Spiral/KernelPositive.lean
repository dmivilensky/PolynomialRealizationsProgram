import polyak.Spiral.KernelPolynomial

/-!
Article: Appendix B, Lemma spiralkernel.
Use: identify the natural-coefficient polynomial recurrence with the original
trigonometric kernel, then obtain nonnegativity at every lag and strict positivity off t=0.
Proof: exact initial data and uniqueness of the fourth-order recurrence.
-/

noncomputable section

namespace polyak.Spiral

open Spectral Polynomial

/-- Article: finite Chebyshev calculation used only to identify the initial kernel coefficients. -/
theorem chebT_three (x : ℝ) : chebT 3 x = 4*x^3-3*x := by
  have h := chebT_recurrence x 1
  have h₁ : chebT 1 x=x := by simp [chebT]
  have h₂ : chebT 2 x=2*x^2-1 := by simp [chebT,Polynomial.Chebyshev.T_two]
  norm_num only [Nat.reduceAdd] at h
  rw [h₁,h₂] at h
  nlinarith [h]

/-- Article: finite Chebyshev calculation for the initial coefficients. -/
theorem chebT_four (x : ℝ) : chebT 4 x = 8*x^4-8*x^2+1 := by
  have h := chebT_recurrence x 2
  norm_num [show chebT 2 x = 2*x^2-1 by simp [chebT,Polynomial.Chebyshev.T_two],
    chebT_three] at h
  nlinarith [h]

/-- Article: finite Chebyshev calculation for the initial coefficients. -/
theorem chebT_five (x : ℝ) : chebT 5 x = 16*x^5-20*x^3+5*x := by
  have h := chebT_recurrence x 3
  norm_num [chebT_three,chebT_four] at h
  nlinarith [h]

/-- Article: finite Chebyshev calculation for the initial coefficients. -/
theorem chebT_six (x : ℝ) : chebT 6 x = 32*x^6-48*x^4+18*x^2-1 := by
  have h := chebT_recurrence x 4
  norm_num [chebT_four,chebT_five] at h
  nlinarith [h]

/-- Article: first exact initial value of the two kernel recurrences. -/
theorem scaledKernel_zero_eq (t : ℝ) :
    scaledKernel t 0 = kernelPolynomialValue (G t^2-1) 0 := by
  have hg := (G_pos t).ne'
  rw [scaledKernel,kernel_eq_cheb]
  norm_num [kernelPolynomialValue,kernelPolynomial,chebT_three]
  unfold cosine
  field_simp
  ring

/-- Article: second exact initial value of the two kernel recurrences. -/
theorem scaledKernel_one_eq (t : ℝ) :
    scaledKernel t 1 = kernelPolynomialValue (G t^2-1) 1 := by
  have hg := (G_pos t).ne'
  rw [scaledKernel,kernel_eq_cheb]
  norm_num [kernelPolynomialValue,kernelPolynomial,chebT_four]
  unfold cosine
  field_simp
  ring

/-- Article: third exact initial value of the two kernel recurrences. -/
theorem scaledKernel_two_eq (t : ℝ) :
    scaledKernel t 2 = kernelPolynomialValue (G t^2-1) 2 := by
  have hg := (G_pos t).ne'
  rw [scaledKernel,kernel_eq_cheb]
  norm_num [kernelPolynomialValue,kernelPolynomial,chebT_five]
  unfold cosine
  field_simp
  ring

/-- Article: fourth exact initial value of the two kernel recurrences. -/
theorem scaledKernel_three_eq (t : ℝ) :
    scaledKernel t 3 = kernelPolynomialValue (G t^2-1) 3 := by
  have hg := (G_pos t).ne'
  rw [scaledKernel,kernel_eq_cheb]
  norm_num [kernelPolynomialValue,kernelPolynomial,chebT_six]
  unfold cosine
  field_simp
  ring

/-- Article: G^(n+1) E_(n+3) is exactly the constructed polynomial in s=G²−1.
Use: gives the original claim of nonnegative polynomial coefficients at every lag. -/
theorem scaledKernel_eq_polynomial (t : ℝ) (n : ℕ) :
    scaledKernel t n = kernelPolynomialValue (G t^2-1) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | n
    · exact scaledKernel_zero_eq t
    · exact scaledKernel_one_eq t
    · exact scaledKernel_two_eq t
    · exact scaledKernel_three_eq t
    · change scaledKernel t (n+4) = kernelPolynomialValue (G t^2-1) (n+4)
      rw [scaledKernel_order_four,kernelPolynomialValue_order_four,
        ih (n+3) (by omega),ih (n+1) (by omega),ih n (by omega)]

/-- Article: the exact original n≥3 formulation: G^(n−2) E_n has natural polynomial coefficients. -/
theorem kernel_polynomial_representation (t : ℝ) (n : ℕ) (hn : 3 ≤ n) :
    G t^(n-2)*kernel t n =
      (kernelPolynomial (n-3)).eval₂ (Nat.castRingHom ℝ) (G t^2-1) := by
  have h := scaledKernel_eq_polynomial t (n-3)
  simpa only [scaledKernel,kernelPolynomialValue,Nat.sub_add_cancel hn,
    show n-3+1=n-2 by omega] using h

/-- Article: nonnegative kernel at every lag n≥3. -/
theorem kernel_add_three_nonneg (t : ℝ) (n : ℕ) : 0 ≤ kernel t (n+3) := by
  have hs : 0 ≤ G t^2-1 := by have := one_le_G t; nlinarith
  have hp := kernelPolynomialValue_nonneg hs n
  rw [← scaledKernel_eq_polynomial,scaledKernel] at hp
  exact nonneg_of_mul_nonneg_right hp (pow_pos (G_pos t) _)

/-- Article: strict positivity of all nonactive kernel lags when t≠0. -/
theorem kernel_add_three_pos {t : ℝ} (ht : t ≠ 0) (n : ℕ) : 0 < kernel t (n+3) := by
  have hs : 0 < G t^2-1 := by
    rw [G, ← Real.sinh_sq]
    exact sq_pos_of_ne_zero (Real.sinh_ne_zero.mpr ht)
  have hp := kernelPolynomialValue_pos hs n
  rw [← scaledKernel_eq_polynomial,scaledKernel] at hp
  exact pos_of_mul_pos_right hp (pow_nonneg (G_pos t).le _)

/-- Article: all kernels are nonnegative, including E₀ and the two active zeros. -/
theorem kernel_nonneg (t : ℝ) (n : ℕ) : 0 ≤ kernel t n := by
  rcases n with _ | _ | _ | n
  · rw [kernel_zero]
    positivity
  · rw [kernel_one]
  · rw [kernel_two]
  · exact kernel_add_three_nonneg t n

/-- Article: the limiting three-cycle kernel has precisely the values zero and three. -/
theorem kernel_at_zero (n : ℕ) : kernel 0 n = if n%3 = 0 then 3 else 0 := by
  rcases n with _ | _ | _ | n
  · norm_num [kernel_zero,G]
  · norm_num [kernel_one]
  · norm_num [kernel_two]
  · have hp := scaledKernel_eq_polynomial 0 n
    simp only [scaledKernel,G,Real.cosh_zero,one_pow,one_mul,sub_self] at hp
    rw [hp,kernelPolynomialValue_zero]
    rw [show (n+1+1+1)%3 = n%3 by omega]

end polyak.Spiral
