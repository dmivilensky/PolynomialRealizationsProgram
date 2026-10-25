import chebyshev1.SineJacobi.EndpointRecurrence
import chebyshev1.SineJacobi.RatioBounds
import chebyshev1.Algebra.DiscreteConcavity

/-!
Article: chebyshev1, Theorem E.3.
The uniform √N bound from E.3, with the paper's explicit constant M.
Use: `chebyshev1.SineJacobi.endpoint_global_bound` feeds
`chebyshev1.SineJacobi.greenWeight_global_bound` (green Weight global bound).
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real
open scoped BigOperators

/--
Exact identity `endpoint N s = (∑ k ∈ Finset.range (s+1), ratio N k*ratio N (s-k))/ratio N s`.

Use: `chebyshev1.SineJacobi.endpoint_half_bound` rewrites with this identity to establish
the stated quantitative bound `endpoint N s ≤ (Real.pi^2/2)*Real.sqrt ((s:ℝ)+1)`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.endpoint_global_bound`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem endpoint_convolution (N s : ℕ) (hs : s < N) :
    endpoint N s = (∑ k ∈ Finset.range (s+1), ratio N k*ratio N (s-k))/ratio N s := by
  rw [endpoint_sum N s hs, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  simp [coefficient, show k ≤ s by have := Finset.mem_range.mp hk; omega]

/--
The stated quantitative bound `endpoint N s ≤ (Real.pi^2/2)*Real.sqrt ((s:ℝ)+1)`.

Use: `chebyshev1.SineJacobi.endpoint_global_bound` uses this bound to establish the stated
quantitative bound `0 < endpoint N s ∧ endpoint N s ≤ (3*Real.pi^2/2)*Real.sqrt (N:ℝ)`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.endpoint_global_bound`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.ratio_half_bounds`,
`chebyshev1.SineJacobi.ratio_pos`, `chebyshev1.SineJacobi.binomialRatio_pos` with the
arguments shown in the proof.
-/
theorem endpoint_half_bound (N s : ℕ) (hs : s < N) (hhalf : 2*s ≤ N) :
    endpoint N s ≤ (Real.pi^2/2)*Real.sqrt ((s:ℝ)+1) := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.ratio_half_bounds`,
  -- `chebyshev1.SineJacobi.ratio_pos`, `chebyshev1.SineJacobi.binomialRatio_pos` with
  -- the arguments shown in the proof.
  have hsum : (∑ k ∈ Finset.range (s+1), ratio N k*ratio N (s-k)) ≤ Real.pi^2/4 := by
    have hb : (∑ k ∈ Finset.range (s+1), ratio N k*ratio N (s-k)) ≤
        (Real.pi/2)^2*(∑ k ∈ Finset.range (s+1), binomialRatio k*binomialRatio (s-k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ s := by have := Finset.mem_range.mp hk; omega
      have ha := (ratio_half_bounds N k (by omega) (by omega)).2
      have hb := (ratio_half_bounds N (s-k) (by omega) (by omega)).2
      have hc := mul_le_mul ha hb (ratio_pos N (s-k) (by omega)).le
        (show 0 ≤ Real.pi/2*binomialRatio k by
          exact mul_nonneg (by positivity) (binomialRatio_pos _).le)
      convert hc using 1 ; ring
    rw [binomialRatio_convolution, mul_one] at hb
    convert hb using 1 ; ring
  have hr := (ratio_binomial_bounds N s hs).1
  have he : endpoint N s*ratio N s =
      ∑ k ∈ Finset.range (s+1), ratio N k*ratio N (s-k) := by
    rw [endpoint_convolution N s hs, div_mul_cancel₀ _ (ratio_pos N s hs).ne']
  have hf := mul_le_mul_of_nonneg_left hr (endpoint_pos N s hs).le
  rw [he] at hf
  have hprod := hf.trans hsum
  rcases Nat.eq_zero_or_pos s with rfl | hp
  · simp only [endpoint_zero, Nat.cast_zero, zero_add, Real.sqrt_one, mul_one]
    nlinarith [pi_gt_three]
  · have hl := binomialRatio_lower s hp
    have hn := mul_le_mul_of_nonneg_left hl (endpoint_pos N s hs).le
    have hsreal : 0 < (s:ℝ) := by exact_mod_cast hp
    have hb : endpoint N s ≤ (Real.pi^2/2)*Real.sqrt (s:ℝ) := by
      have hg := hn.trans hprod
      rw [← div_eq_mul_one_div, div_le_iff₀ (by positivity)] at hg
      nlinarith
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith : (s:ℝ) ≤ (s:ℝ)+1)) (by positivity))

/--
The stated quantitative bound `endpoint N s ≤ 3*endpoint N (N/2)`.

Use: `chebyshev1.SineJacobi.endpoint_global_bound` uses this bound to establish the stated
quantitative bound `0 < endpoint N s ∧ endpoint N s ≤ (3*Real.pi^2/2)*Real.sqrt (N:ℝ)`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.endpoint_global_bound`.

Proof: Separate `m ≤ s` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem endpoint_midpoint_control (N s : ℕ) (hN : 2 ≤ N) (hs : s ≤ N) :
    endpoint N s ≤ 3*endpoint N (N/2) := by
  -- Separate `m ≤ s` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let m := N/2
  have hm : 0 < m := by dsimp [m]; omega
  have hmN : m < N := by dsimp [m]; omega
  have hFm : 0 < endpoint N m := endpoint_pos N m hmN
  by_cases hms : m ≤ s
  · have hp : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
    have hmp : 0 < (m:ℝ) := by exact_mod_cast hm
    have hb := DiscreteConcavity.normalized_decreasing (endpoint N) N (by simp)
      (endpoint_second_difference_nonpos N) hm hms hs
    have hc := (div_le_div_iff₀ hp hmp).mp hb
    have h3 : (s:ℝ) ≤ 3*(m:ℝ) := by
      exact_mod_cast (show s ≤ 3*m by dsimp [m]; omega)
    have hmul := mul_le_mul_of_nonneg_left h3 hFm.le
    nlinarith
  · have hsm : s ≤ m := by omega
    have hrev (n : ℕ) (hn : n+1 < N) :
        endpoint N (N-(n+2))-2*endpoint N (N-(n+1))+endpoint N (N-n) ≤ 0 := by
      have hb := endpoint_second_difference_nonpos N (N-n-2) (by omega)
      rw [show N-n-2+2 = N-n by omega, show N-n-2+1 = N-(n+1) by omega,
        show N-n-2 = N-(n+2) by omega] at hb
      linarith
    have hb := DiscreteConcavity.normalized_decreasing (fun n => endpoint N (N-n)) N
      (by simpa using (endpoint_terminal N (by omega)).symm ▸ (by norm_num : (0:ℝ) ≤ 2))
      hrev (m := N-m) (s := N-s) (by omega) (by omega) (by omega)
    rw [Nat.sub_sub_self hmN.le, Nat.sub_sub_self hs] at hb
    have hp : 0 < ((N-s:ℕ):ℝ) := by exact_mod_cast (show 0 < N-s by omega)
    have hmp : 0 < ((N-m:ℕ):ℝ) := by exact_mod_cast (show 0 < N-m by omega)
    have hc := (div_le_div_iff₀ hp hmp).mp hb
    have h3 : ((N-s:ℕ):ℝ) ≤ 3*((N-m:ℕ):ℝ) := by
      exact_mod_cast (show N-s ≤ 3*(N-m) by dsimp [m]; omega)
    have hmul := mul_le_mul_of_nonneg_left h3 hFm.le
    nlinarith

/--
The uniform √N bound from E.3, with the paper's explicit constant M.

The stated quantitative bound `0 < endpoint N s ∧ endpoint N s ≤ (3*Real.pi^2/2)*Real.sqrt
(N:ℝ)`.

Use: `chebyshev1.SineJacobi.greenWeight_global_bound` uses this bound to establish the
stated quantitative bound `0 < greenWeight N s ∧ greenWeight N s ≤ (9*Real.pi^4/4)*(N:ℝ)`.

Article: chebyshev1, Theorem E.3.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.endpoint_terminal`,
`chebyshev1.SineJacobi.endpoint_pos`, `chebyshev1.SineJacobi.endpoint_midpoint_control`
with the arguments shown in the proof.
-/
theorem endpoint_global_bound (N s : ℕ) (hN : 2 ≤ N) (hs : s ≤ N) :
    0 < endpoint N s ∧ endpoint N s ≤ (3*Real.pi^2/2)*Real.sqrt (N:ℝ) := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.endpoint_terminal`,
  -- `chebyshev1.SineJacobi.endpoint_pos`,
  -- `chebyshev1.SineJacobi.endpoint_midpoint_control` with the arguments shown in the
  -- proof.
  constructor
  · rcases eq_or_lt_of_le hs with heq | hs
    · rw [heq, endpoint_terminal N (by omega)]; norm_num
    · exact endpoint_pos N s hs
  · have hm := endpoint_midpoint_control N s hN hs
    have hh := endpoint_half_bound N (N/2) (by omega) (by omega)
    have hle : ((N/2:ℕ):ℝ)+1 ≤ N := by exact_mod_cast (show N/2+1 ≤ N by omega)
    have hroot := Real.sqrt_le_sqrt hle
    have hmul := mul_le_mul_of_nonneg_left hroot (show 0 ≤ Real.pi^2/2 by positivity)
    nlinarith

end
end chebyshev1.SineJacobi
