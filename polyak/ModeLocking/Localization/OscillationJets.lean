import polyak.ModeLocking.Localization.Taylor

/-! The exact nondegenerate quadratic jet of the regular pinning polynomial. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels Set
open scoped BigOperators

def pinningFirst (N : Finset ℤ) (a : ℤ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ N, a n*(n:ℝ)*Real.sin ((n:ℝ)*x)

def pinningSecond (N : Finset ℤ) (a : ℤ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ N, a n*(n:ℝ)^2*Real.cos ((n:ℝ)*x)

theorem hasDerivAt_pinning (N : Finset ℤ) (a : ℤ → ℝ) (x : ℝ) :
    HasDerivAt (pinningPolynomial N a) (pinningFirst N a x) x := by
  apply HasDerivAt.fun_sum
  intro n _
  convert ((((hasDerivAt_id x).const_mul (n:ℝ)).cos).const_sub 1).const_mul (a n) using 1
  · funext y
    rfl
  · simp only [id_eq, mul_one]
    ring

theorem hasDerivAt_pinningFirst (N : Finset ℤ) (a : ℤ → ℝ) (x : ℝ) :
    HasDerivAt (pinningFirst N a) (pinningSecond N a x) x := by
  apply HasDerivAt.fun_sum
  intro n _
  convert (((hasDerivAt_id x).const_mul (n:ℝ)).sin).const_mul (a n*(n:ℝ)) using 1
  · funext y
    rfl
  · simp only [id_eq, mul_one]
    ring

theorem pinning_deriv_zero (N : Finset ℤ) (a : ℤ → ℝ) :
    deriv (pinningPolynomial N a) 0 = 0 := by
  rw [(hasDerivAt_pinning N a 0).deriv]
  simp [pinningFirst]

theorem pinning_second_zero (N : Finset ℤ) (a : ℤ → ℝ) :
    deriv (deriv (pinningPolynomial N a)) 0 = ∑ n ∈ N, a n*(n:ℝ)^2 := by
  have he : deriv (pinningPolynomial N a) = pinningFirst N a :=
    funext fun x => (hasDerivAt_pinning N a x).deriv
  rw [he, (hasDerivAt_pinningFirst N a 0).deriv]
  simp [pinningSecond]

variable {q : General.Tuning} {t : ℝ} {L : ℕ}

theorem regular_pinning_second_pos (D : RegularData q t L) :
    0 < deriv (deriv (pinningPolynomial D.lags D.dual)) 0 := by
  rw [pinning_second_zero]
  have hN : D.lags.Nonempty := by
    by_contra hn
    have he : D.lags=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hs := D.dual_sum
    rw [he,Finset.sum_empty] at hs
    exact zero_ne_one hs
  exact Finset.sum_pos (fun n hn => mul_pos (D.dual_pos n hn)
    (sq_pos_of_ne_zero (by exact_mod_cast D.lags_nonzero n hn))) hN

end polyak.ModeLocking.Localization
