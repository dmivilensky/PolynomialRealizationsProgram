import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Defs
import chebyshev1.Analysis.MidpointQuadrature

/-! The half-shift harmonic sum, with the Euler constant normalization. -/
namespace chebyshev1.Analysis
noncomputable section
open Real Filter Topology

def halfHarmonic (N : ℕ) : ℝ := 2 * (harmonic (2 * N) : ℝ) - (harmonic N : ℝ)

def halfHarmonicError (N : ℕ) : ℝ := halfHarmonic N - log N

theorem halfHarmonicError_limit :
    Tendsto halfHarmonicError atTop (𝓝 (2 * log 2 + eulerMascheroniConstant)) := by
  have h2 := tendsto_harmonic_sub_log.comp
    (tendsto_atTop_mono (fun n : ℕ => show n ≤ 2*n by omega) tendsto_id)
  have h := ((h2.const_mul 2).sub tendsto_harmonic_sub_log).add_const (2 * log 2)
  have hc : 2 * eulerMascheroniConstant - eulerMascheroniConstant + 2 * log 2 =
      2 * log 2 + eulerMascheroniConstant := by ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_def, halfHarmonicError, halfHarmonic, Nat.cast_mul, Nat.cast_ofNat]
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0]
  ring

theorem halfHarmonic_succ (N : ℕ) :
    halfHarmonic (N + 1) - halfHarmonic N = 1 / ((N : ℝ) + 1 / 2) := by
  have hN : 2 * (N + 1) = (2*N+1)+1 := by omega
  simp only [halfHarmonic, hN, harmonic_succ]
  push_cast
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : 2 * (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem halfHarmonic_eq_sum (N : ℕ) :
    halfHarmonic N = ∑ s ∈ Finset.range N, 1/((s:ℝ)+1/2) := by
  induction N with
  | zero => simp [halfHarmonic]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    linarith [halfHarmonic_succ N]

/-- A telescoping majorant converts an increment estimate into a tail estimate. -/
theorem sequence_tail_bound {a b : ℕ → ℝ} {L C : ℝ}
    (ha : Tendsto a atTop (𝓝 L)) (hC : 0 ≤ C) (hb : ∀ n, 0 ≤ b n)
    {N : ℕ} (hstep : ∀ n, N ≤ n → |a (n+1)-a n| ≤ C*(b n-b (n+1))) :
    |a N-L| ≤ C*b N := by
  have hi (k : ℕ) : |a (N+k)-a N| ≤ C*(b N-b (N+k)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have ht := abs_add_le (a (N+k+1)-a (N+k)) (a (N+k)-a N)
      have hs := hstep (N+k) (by omega)
      rw [sub_add_sub_cancel] at ht
      change |a (N+k+1)-a N| ≤ C*(b N-b (N+k+1))
      exact ht.trans (by linarith)
  have hk : Tendsto (fun k => N+k) atTop atTop :=
    tendsto_atTop_mono (fun k => show k ≤ N+k by omega) tendsto_id
  have hl := ((ha.comp hk).sub_const (a N)).abs
  rw [abs_sub_comm]
  apply le_of_tendsto hl
  exact Eventually.of_forall (fun k => (hi k).trans (by nlinarith [hb (N+k)]))

theorem halfHarmonicError_increment (N : ℕ) (hN : 0 < N) :
    |halfHarmonicError (N+1)-halfHarmonicError N| ≤ 2 / (N : ℝ) ^ 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hf (t : ℝ) (ht : t ∈ Set.Icc (N : ℝ) (N+1)) :
      HasDerivAt (fun x : ℝ => 1/x) (-(1/t^2)) t := by
    have ht0 : t ≠ 0 := (hn.trans_le ht.1).ne'
    simpa only [one_div, inv_pow] using hasDerivAt_inv ht0
  have hf' (t : ℝ) (ht : t ∈ Set.Icc (N : ℝ) (N+1)) :
      HasDerivAt (fun x : ℝ => -(1/x^2)) (2/t^3) t := by
    have ht0 : t ≠ 0 := (hn.trans_le ht.1).ne'
    convert ((hasDerivAt_inv ht0).pow 2).neg using 1
    · funext x
      simp [one_div, inv_pow]
    · simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
      field_simp [ht0]
  have hbnd (t : ℝ) (ht : t ∈ Set.Icc (N : ℝ) (N+1)) :
      |2/t^3| ≤ 2 / (N : ℝ)^3 := by
    have htpos := hn.trans_le ht.1
    rw [abs_of_pos (by positivity : 0 < 2/t^3)]
    gcongr
    exact ht.1
  have hq := midpoint_integral_error_bound (a := (N : ℝ)) (b := (N : ℝ)+1)
    (M := 2/(N:ℝ)^3) (by linarith) (by positivity) hf hf' hbnd
  rw [integral_one_div_of_pos hn (by positivity),
    log_div (by positivity) hn.ne'] at hq
  simp only [add_sub_cancel_left, one_mul, one_pow, mul_one] at hq
  have hm : ((N : ℝ)+((N : ℝ)+1))/2 = (N : ℝ)+1/2 := by ring
  rw [hm] at hq
  convert hq using 1
  congr 1
  simp only [halfHarmonicError, Nat.cast_add, Nat.cast_one]
  rw [show halfHarmonic (N+1)-log ((N : ℝ)+1)-(halfHarmonic N-log (N : ℝ)) =
    (halfHarmonic (N+1)-halfHarmonic N)-(log ((N : ℝ)+1)-log (N : ℝ)) by ring,
    halfHarmonic_succ]

theorem halfHarmonic_error_bound (N : ℕ) (hN : 0 < N) :
    |halfHarmonic N - (log N + 2*log 2+eulerMascheroniConstant)| ≤ 8/(N:ℝ)^2 := by
  have hmajor (n : ℕ) (hn : N ≤ n) :
      |halfHarmonicError (n+1)-halfHarmonicError n| ≤
        8 * (1/(n:ℝ)^2-1/((n:ℝ)+1)^2) := by
    have hnNat : 0 < n := lt_of_lt_of_le hN hn
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
    refine (halfHarmonicError_increment n hnNat).trans ?_
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
    field_simp
    nlinarith [sq_nonneg ((n : ℝ)-1)]
  have h := sequence_tail_bound (N := N) halfHarmonicError_limit (by norm_num : (0:ℝ) ≤ 8)
    (fun n : ℕ => show 0 ≤ 1/(n:ℝ)^2 by positivity)
    (by intro n hn; simpa only [Nat.cast_add, Nat.cast_one] using hmajor n hn)
  simpa only [halfHarmonicError, div_eq_mul_inv, mul_one_div, sub_add_eq_sub_sub,
    mul_one, one_mul] using h

theorem halfHarmonic_error_isBigO :
    (fun N : ℕ => halfHarmonic N-(log N+2*log 2+eulerMascheroniConstant)) =O[atTop]
      (fun N : ℕ => 1/(N:ℝ)^2) := by
  apply Asymptotics.IsBigO.of_bound 8
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1/(N:ℝ)^2)]
  simpa only [div_eq_mul_inv, mul_one, one_mul] using halfHarmonic_error_bound N hN

end
end chebyshev1.Analysis
