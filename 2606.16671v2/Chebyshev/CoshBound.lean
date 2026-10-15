import «2606.16671v2».Chebyshev.OutsideBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Data.Nat.Choose.Basic

/-!
Article: 2606.16671v2, Theorem 4.3.
The scalar estimate used for the cosh remainder in 4.3(iii).
Use: `«2606.16671v2».chebyshev_remainder_cosh_le` feeds
`«2606.16671v2».JacobiData.opNorm_driftRemainder_cosh_le` (op Norm drift Remainder cosh le).
Proof chain: `«2606.16671v2».JacobiData.opNorm_driftRemainder_cosh_le` — 2606.16671v2, Theorem 4.3;
All insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace «2606.16671v2»
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/--
The stated quantitative bound `1+y^2/2 ≤ Real.cosh y`.

Use: `«2606.16671v2».chebyshev_cosh_upper` uses this bound to establish the stated quantitative
bound `(T ℝ N).eval (1+u) ≤ Real.cosh ((N:ℝ)*Real.sqrt (2*u))`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_driftRemainder_cosh_le`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem cosh_quadratic_lower (y : ℝ) : 1+y^2/2 ≤ Real.cosh y := by
  have hs := (Real.hasSum_cosh y).summable
  have hb := hs.sum_le_tsum (Finset.range 2)
    (fun n _ => div_nonneg (even_two_mul n |>.pow_nonneg y) (by positivity))
  simpa [Finset.sum_range_succ, (Real.hasSum_cosh y).tsum_eq] using hb

/--
A fourth-order bound with its exact factorial constant.

The stated quantitative bound `Real.cosh y - 1 - y^2/2 ≤ y^4/24 * Real.cosh y`.

Use: `«2606.16671v2».chebyshev_remainder_cosh_le` uses this bound to establish the stated
quantitative bound `(T ℝ N).eval (1+u)-1-(N:ℝ)^2*u ≤ (N:ℝ)^4*u^2/6 * Real.cosh ((N:ℝ)*Real.sqrt
(2*u))`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_driftRemainder_cosh_le`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem cosh_remainder_le (y : ℝ) :
    Real.cosh y - 1 - y^2/2 ≤ y^4/24 * Real.cosh y := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  let f (n : ℕ) := y^(2*n)/(Nat.factorial (2*n) : ℝ)
  -- Prove the summability hs needed for the later infinite-sum manipulations.
  have hs : Summable f := (Real.hasSum_cosh y).summable
  -- Prove the summability ht needed for the later infinite-sum manipulations.
  have ht : Summable (fun n => f (n+2)) := (summable_nat_add_iff 2).mpr hs
  have he := hs.sum_add_tsum_nat_add 2
  have hb (n : ℕ) : f (n+2) ≤ y^4/24 * f n := by
    have hn : 24 * (2*n).factorial ≤ (2*(n+2)).factorial := by
      have hdiv := Nat.factorial_mul_factorial_dvd_factorial_add 4 (2*n)
      have hle := Nat.le_of_dvd (Nat.factorial_pos (4+2*n)) hdiv
      simpa only [show 4+2*n = 2*(n+2) by omega, show Nat.factorial 4 = 24 by norm_num] using hle
    have hn' : (24:ℝ) * (Nat.factorial (2*n) : ℝ) ≤ (Nat.factorial (2*(n+2)) : ℝ) := by
      exact_mod_cast hn
    have hp : 0 < (24:ℝ) * (Nat.factorial (2*n) : ℝ) := by positivity
    have hh := div_le_div_of_nonneg_left
      (mul_nonneg (pow_nonneg (sq_nonneg y) 2) (even_two_mul n |>.pow_nonneg y)) hp hn'
    convert hh using 1
    · dsimp [f]
      rw [show 2*(n+2) = 4+2*n by omega, pow_add]
      ring
    · dsimp [f]
      ring
  have htbound := ht.tsum_le_tsum hb (hs.mul_left (y^4/24))
  rw [tsum_mul_left, (Real.hasSum_cosh y).tsum_eq] at htbound
  have he' : 1+y^2/2 + (∑' n, f (n+2)) = Real.cosh y := by
    simpa [f, Finset.sum_range_succ, (Real.hasSum_cosh y).tsum_eq] using he
  linarith

/--
The stated quantitative bound `(T ℝ N).eval (1+u) ≤ Real.cosh ((N:ℝ)*Real.sqrt (2*u))`.

Use: `«2606.16671v2».chebyshev_remainder_cosh_le` uses this bound to establish the stated
quantitative bound `(T ℝ N).eval (1+u)-1-(N:ℝ)^2*u ≤ (N:ℝ)^4*u^2/6 * Real.cosh ((N:ℝ)*Real.sqrt
(2*u))`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_driftRemainder_cosh_le`.

Proof: Use the identities/estimates `«2606.16671v2».cosh_quadratic_lower` with the arguments
shown in the proof.
-/
theorem chebyshev_cosh_upper (N : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (T ℝ N).eval (1+u) ≤ Real.cosh ((N:ℝ)*Real.sqrt (2*u)) := by
  -- Use the identities/estimates `«2606.16671v2».cosh_quadratic_lower` with the arguments
  -- shown in the proof.
  have hx : 1 ≤ 1+u := by linarith
  have ha := Real.arcosh_nonneg hx
  have hb : Real.arcosh (1+u) ≤ Real.sqrt (2*u) := by
    have hq := cosh_quadratic_lower (Real.sqrt (2*u))
    rw [Real.sq_sqrt (by positivity)] at hq
    have hc : Real.cosh (Real.arcosh (1+u)) ≤ Real.cosh (Real.sqrt (2*u)) := by
      rw [Real.cosh_arcosh hx]; linarith
    simpa only [abs_of_nonneg ha, abs_of_nonneg (Real.sqrt_nonneg _)] using Real.cosh_le_cosh.mp hc
  rw [← Real.cosh_arcosh hx, T_real_cosh]
  apply Real.cosh_le_cosh.mpr
  simp only [Int.cast_natCast, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) ha),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N)

/--
The scalar estimate used for the cosh remainder in 4.3(iii).

The stated quantitative bound `(T ℝ N).eval (1+u)-1-(N:ℝ)^2*u ≤ (N:ℝ)^4*u^2/6 * Real.cosh
((N:ℝ)*Real.sqrt (2*u))`.

Use: `«2606.16671v2».JacobiData.opNorm_driftRemainder_cosh_le` uses this bound to establish the
stated quantitative bound `opNorm ((J.realization I).driftRemainder N H E) ≤ (2/3:ℝ)*I.epsilon
N*(N:ℝ)^4*(delta/I.delta)^2 * Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta))`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_driftRemainder_cosh_le`.

Proof: Use the identities/estimates `«2606.16671v2».cosh_remainder_le`,
`«2606.16671v2».chebyshev_cosh_upper` with the arguments shown in the proof.
-/
theorem chebyshev_remainder_cosh_le (N : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (T ℝ N).eval (1+u)-1-(N:ℝ)^2*u ≤
      (N:ℝ)^4*u^2/6 * Real.cosh ((N:ℝ)*Real.sqrt (2*u)) := by
  -- Use the identities/estimates `«2606.16671v2».cosh_remainder_le`,
  -- `«2606.16671v2».chebyshev_cosh_upper` with the arguments shown in the proof.
  have hs : ((N:ℝ)*Real.sqrt (2*u))^2 / 2 = (N:ℝ)^2*u := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hfour : ((N:ℝ)*Real.sqrt (2*u))^4/24 = (N:ℝ)^4*u^2/6 := by
    rw [show ((N:ℝ)*Real.sqrt (2*u))^4 =
      (((N:ℝ)*Real.sqrt (2*u))^2)^2 by ring, show
      ((N:ℝ)*Real.sqrt (2*u))^2 = 2*((N:ℝ)^2*u) by linarith [hs]]
    ring
  have hr := cosh_remainder_le ((N:ℝ)*Real.sqrt (2*u))
  rw [hs, hfour] at hr
  exact (sub_le_sub_right (sub_le_sub_right (chebyshev_cosh_upper N u hu) 1) _).trans hr

end
end «2606.16671v2»
