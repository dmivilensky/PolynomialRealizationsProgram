import polyak.Boundary.P5.RealChebyshev

/-!
Article: Proposition p5divslack, exact values at the critical three-cycle.
Use: simplify the genuine derivative for every residue class of the lag.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral

/-- Article: all critical T values, indexed by the lag modulo three. -/
theorem chebT_cycle (n : ℕ) : chebT n (-1/2)=if n%3=0 then 1 else (-1/2 : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [chebT]
  | one => norm_num [chebT]
  | more n h0 h1 =>
    rw [Spiral.chebT_recurrence,h0,h1]
    have hn : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
    rcases hn with hn | hn | hn
    all_goals have h1 : (n+1)%3=(n%3+1)%3 := by omega
    all_goals have h2 : (n+2)%3=(n%3+2)%3 := by omega
    all_goals norm_num [hn,h1,h2]

/-- Article: all critical U values, indexed by their degree modulo three. -/
theorem chebU_cycle (n : ℕ) : chebU n (-1/2)=
    if n%3=0 then 1 else if n%3=1 then -1 else (0 : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [chebU]
  | one => norm_num [chebU]
  | more n h0 h1 =>
    rw [chebU_recurrence,h0,h1]
    have hn : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
    rcases hn with hn | hn | hn
    all_goals have h1 : (n+1)%3=(n%3+1)%3 := by omega
    all_goals have h2 : (n+2)%3=(n%3+2)%3 := by omega
    all_goals norm_num [hn,h1,h2]

/-- Article: U at degree one below the lag, in lag residue order. -/
theorem chebU_lag_cycle (n : ℕ) (hn : 1≤n) : chebU (n-1) (-1/2)=
    if n%3=0 then 0 else if n%3=1 then 1 else (-1 : ℝ) := by
  rw [chebU_cycle]
  have hmod : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases hmod with hm | hm | hm
  all_goals have hp : (n-1)%3=(n%3+2)%3 := by omega
  all_goals norm_num [hp,hm]

/-- Article: the natural-lag derivative of T is n Uₙ₋₁. -/
theorem chebT_derivative_eval (n : ℕ) (hn : 1≤n) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval x=n*chebU (n-1) x := by
  have hc : (n : ℤ)-1=((n-1 : ℕ) : ℤ) := by omega
  simp [Polynomial.Chebyshev.T_derivative_eq_U,hc,chebU]

/-- Article: the critical derivative of U without division or trigonometry. -/
theorem chebU_derivative_cycle (n : ℕ) (hn : 1≤n) :
    (3/4 : ℝ)*(Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)).derivative.eval (-1/2)=
      -1/2*chebU (n-1) (-1/2)-n*chebT n (-1/2) := by
  have hc : ((n-1 : ℕ) : ℤ)+1=(n : ℤ) := by omega
  have he := congrArg (Polynomial.eval (-1/2 : ℝ))
    (Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U (R:=ℝ) ((n-1 : ℕ) : ℤ))
  rw [hc] at he
  norm_num only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_one,
    Polynomial.eval_add,Polynomial.eval_intCast,Polynomial.eval_natCast,Polynomial.eval_X,Int.cast_natCast,
    Nat.cast_one] at he
  have hr : ((n-1 : ℕ) : ℝ)+1=(n : ℝ) := by exact_mod_cast Nat.sub_add_cancel hn
  rw [hr] at he
  change _ = -1/2*(Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)).eval (-1/2)-
    (n : ℝ)*(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (-1/2)
  nlinarith [he]

end polyak.Boundary.P5
