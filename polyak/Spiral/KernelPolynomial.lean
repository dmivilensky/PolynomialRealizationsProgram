import polyak.Spiral.Data

/-!
Article: Appendix B, positivity of the spiral kernel.
Use: a polynomial with natural coefficients for every G^(n+1) E_(n+3).
Proof: the generating-function denominator yields a recurrence with nonnegative
coefficients. The recurrence is implemented directly, so the coefficient claim
does not require convergence of an analytic or formal infinite series.
-/

noncomputable section

namespace polyak.Spiral

open Polynomial Spectral

/-- Article: the nonnegative polynomial F_(n+3) in s=G²−1. -/
def kernelPolynomial : ℕ → ℕ[X]
  | 0 => (2*X+3)*(1+2*X)
  | 1 => 2*X*kernelPolynomial 0+(2*X+3)*X
  | 2 => 2*X*kernelPolynomial 1+2*X*kernelPolynomial 0+(2*X+3)*X
  | n+3 => 2*X*kernelPolynomial (n+2)+2*X*kernelPolynomial (n+1)+
      (1+5*X+2*X^2)*kernelPolynomial n+
      (3*X+X^2)*(∑ k : Fin n, kernelPolynomial k)+(2*X+3)*X
termination_by n => n
decreasing_by all_goals omega

/-- Article: evaluation in the physical nonnegative variable s. -/
def kernelPolynomialValue (s : ℝ) (n : ℕ) : ℝ :=
  (kernelPolynomial n).eval₂ (Nat.castRingHom ℝ) s

/-- Article: natural-coefficient polynomials are nonnegative on s≥0. -/
theorem natPolynomial_eval_nonneg (p : ℕ[X]) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ p.eval₂ (Nat.castRingHom ℝ) s := by
  rw [Polynomial.eval₂_eq_sum]
  unfold Polynomial.sum
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs n))

/-- Article: all spiral kernel polynomials have nonnegative coefficients, literally in ℕ. -/
theorem kernelPolynomialValue_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ kernelPolynomialValue s n := natPolynomial_eval_nonneg _ hs

/-- Article: recurrence with no negative coefficient, the coefficientwise generating-function argument. -/
theorem kernelPolynomialValue_recurrence (s : ℝ) (n : ℕ) :
    kernelPolynomialValue s (n+3) =
      2*s*kernelPolynomialValue s (n+2)+2*s*kernelPolynomialValue s (n+1)+
      (1+5*s+2*s^2)*kernelPolynomialValue s n+
      (3*s+s^2)*(∑ k : Fin n, kernelPolynomialValue s k)+(2*s+3)*s := by
  simp [kernelPolynomialValue, kernelPolynomial, Polynomial.eval₂_finsetSum]

/-- Article: strict positivity for s>0. Proof: the positive source term controls every later lag. -/
theorem kernelPolynomialValue_pos {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 < kernelPolynomialValue s n := by
  rcases n with _ | _ | _ | n
  · simp [kernelPolynomialValue, kernelPolynomial]
    positivity
  · simp [kernelPolynomialValue, kernelPolynomial]
    positivity
  · simp [kernelPolynomialValue, kernelPolynomial]
    positivity
  · rw [kernelPolynomialValue_recurrence]
    have h₁ := kernelPolynomialValue_nonneg hs.le (n+2)
    have h₂ := kernelPolynomialValue_nonneg hs.le (n+1)
    have h₃ := kernelPolynomialValue_nonneg hs.le n
    have hsum : 0 ≤ ∑ k : Fin n, kernelPolynomialValue s k :=
      Finset.sum_nonneg (fun k _ => kernelPolynomialValue_nonneg hs.le k)
    positivity

/-- Article: the exact values at s=0, with the correct residue classes modulo three. -/
theorem kernelPolynomialValue_zero (n : ℕ) :
    kernelPolynomialValue 0 n = if n%3 = 0 then 3 else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · norm_num [kernelPolynomialValue, kernelPolynomial]
    · norm_num [kernelPolynomialValue, kernelPolynomial]
    · norm_num [kernelPolynomialValue, kernelPolynomial]
    · change kernelPolynomialValue 0 (n+3) = if (n+3)%3 = 0 then 3 else 0
      rw [kernelPolynomialValue_recurrence]
      simp only [mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_add,
        add_zero, one_mul]
      rw [ih n (by omega)]
      rw [show (n+3)%3 = n%3 by omega]

/-- Article: the scalar fourth-order recurrence encoded by the rational generating function. -/
theorem kernelPolynomialValue_order_four (s : ℝ) (n : ℕ) :
    kernelPolynomialValue s (n+4) =
      (1+2*s)*kernelPolynomialValue s (n+3)+
      (1+3*s+2*s^2)*kernelPolynomialValue s (n+1)-
      (1+2*s+s^2)*kernelPolynomialValue s n := by
  have h₀ := kernelPolynomialValue_recurrence s n
  have h₁ := kernelPolynomialValue_recurrence s (n+1)
  have hsum : (∑ k : Fin (n+1), kernelPolynomialValue s k) =
      (∑ k : Fin n, kernelPolynomialValue s k)+kernelPolynomialValue s n :=
    Fin.sum_univ_castSucc _
  rw [hsum] at h₁
  simp only [show n+1+3=n+4 by omega, show n+1+2=n+3 by omega,
    show n+1+1=n+2 by omega] at h₁
  linear_combination h₁-h₀

/-- Article: the scaled actual kernel F_(n+3). -/
def scaledKernel (t : ℝ) (n : ℕ) : ℝ := G t^(n+1)*kernel t (n+3)

/-- Article: express E_n entirely with Chebyshev polynomials. -/
theorem kernel_eq_cheb (t : ℝ) (n : ℕ) :
    kernel t n = chebT n (G t)+2*G t^2*chebT n (cosine t) := by
  rw [G, chebT_cosh]
  rfl

/-- Article: elementary Chebyshev recurrence with natural indexing. -/
theorem chebT_recurrence (x : ℝ) (n : ℕ) :
    chebT (n+2) x = 2*x*chebT (n+1) x-chebT n x := by
  have h := congrArg (Polynomial.eval x) (Polynomial.Chebyshev.T_add_two ℝ (n : ℤ))
  simpa only [chebT, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X] using h

/-- Article: a power-rescaled Chebyshev sequence. -/
def weightedCheb (a x : ℝ) (d n : ℕ) : ℝ := a^(n+1)*chebT (n+d) x

/-- Article: the two quadratic denominators of the generating function. -/
theorem weightedCheb_recurrence (a x : ℝ) (d n : ℕ) :
    weightedCheb a x d (n+2) =
      (2*a*x)*weightedCheb a x d (n+1)-a^2*weightedCheb a x d n := by
  unfold weightedCheb
  rw [show n+2+d=(n+d)+2 by omega, chebT_recurrence]
  simp only [show n+1+d=(n+d)+1 by omega,
    show n+2+1=(n+1)+2 by omega, show n+1+1=(n+1)+1 by omega,
    pow_add, pow_one]
  ring

/-- Article: multiply two second-order denominator factors, with their common quadratic term. -/
theorem combined_order_four {P Q : ℕ → ℝ} (X : ℝ)
    (hP : ∀ n, P (n+2)=2*X*P (n+1)-X*P n)
    (hQ : ∀ n, Q (n+2)=-Q (n+1)-X*Q n) (n : ℕ) :
    P (n+4)+Q (n+4) =
      (2*X-1)*(P (n+3)+Q (n+3))+
      X*(2*X-1)*(P (n+1)+Q (n+1))-X^2*(P n+Q n) := by
  have hp₀ := hP n
  have hp₁ := hP (n+1)
  have hp₂ := hP (n+2)
  have hq₀ := hQ n
  have hq₁ := hQ (n+1)
  have hq₂ := hQ (n+2)
  simp only [show n+1+2=n+3 by omega, show n+1+1=n+2 by omega] at hp₁ hq₁
  simp only [show n+2+2=n+4 by omega, show n+2+1=n+3 by omega] at hp₂ hq₂
  linear_combination hp₂+hp₁+X*hp₀+hq₂-2*X*hq₁+X*hq₀

/-- Article: the actual scaled trigonometric kernel satisfies the exact same fourth-order recurrence. -/
theorem scaledKernel_order_four (t : ℝ) (n : ℕ) :
    scaledKernel t (n+4) =
      (1+2*(G t^2-1))*scaledKernel t (n+3)+
      (1+3*(G t^2-1)+2*(G t^2-1)^2)*scaledKernel t (n+1)-
      (1+2*(G t^2-1)+(G t^2-1)^2)*scaledKernel t n := by
  let P := weightedCheb (G t) (G t) 3
  let Q := fun k => 2*G t^2*weightedCheb (G t) (cosine t) 3 k
  have hp (k : ℕ) : P (k+2)=2*G t^2*P (k+1)-G t^2*P k := by
    have h := weightedCheb_recurrence (G t) (G t) 3 k
    dsimp [P]
    nlinarith [h]
  have hq (k : ℕ) : Q (k+2)=-Q (k+1)-G t^2*Q k := by
    have h := weightedCheb_recurrence (G t) (cosine t) 3 k
    have hc : 2*G t*cosine t = -1 := by
      have hg := (G_pos t).ne'
      unfold cosine
      field_simp
    rw [hc] at h
    dsimp [Q]
    linear_combination 2*G t^2*h
  have heq (k : ℕ) : scaledKernel t k = P k+Q k := by
    unfold scaledKernel
    rw [kernel_eq_cheb]
    dsimp [P,Q,weightedCheb]
    ring
  simp_rw [heq]
  have h := combined_order_four (G t^2) hp hq n
  convert h using 1
  ring

end polyak.Spiral
