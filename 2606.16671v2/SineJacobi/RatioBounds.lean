import «2606.16671v2».SineJacobi.RogersCoefficients
import «2606.16671v2».SineJacobi.BinomialConvolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Article: 2606.16671v2, Theorem E.3.
Ratio Bounds.
Use: `«2606.16671v2».SineJacobi.ratio_half_bounds` feeds
`«2606.16671v2».SineJacobi.endpoint_half_bound` (endpoint half bound).
Proof chain: `«2606.16671v2».SineJacobi.endpoint_global_bound` — 2606.16671v2, Theorem E.3;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real

/--
Monotonicity in decreasing order: `AntitoneOn sinc (Set.Icc (0:ℝ) Real.pi)`.

Use: `«2606.16671v2».SineJacobi.ratio_binomial_bounds` uses this assertion to establish the
stated quantitative bound `binomialRatio k ≤ ratio N k ∧ ratio N k*sinc ((k:ℝ)*h N) ≤
binomialRatio k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Proof: Separate `x = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem sinc_antitoneOn : AntitoneOn sinc (Set.Icc (0:ℝ) Real.pi) := by
  -- Separate `x = 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · rw [hx0, sinc_zero]
    exact sinc_le_one y
  have hy0 : y ≠ 0 := by intro h; subst y; exact hx0 (by linarith [hx.1])
  have hb := strictConcaveOn_sin_Icc.concaveOn.neg.secant_mono
    (a := 0) (x := x) (y := y) ⟨le_rfl, pi_pos.le⟩ hx hy hx0 hy0 hxy
  simpa only [Pi.neg_apply, sin_zero, neg_zero, sub_zero, neg_div,
    neg_le_neg_iff, sinc_of_ne_zero hx0, sinc_of_ne_zero hy0] using hb

/--
The stated quantitative bound `0 < sinc (t*h N)`.

Use: `«2606.16671v2».SineJacobi.ratio_binomial_bounds` uses this bound to establish the stated
quantitative bound `binomialRatio k ≤ ratio N k ∧ ratio N k*sinc ((k:ℝ)*h N) ≤ binomialRatio
k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.angle_mem` with the arguments
shown in the proof.
-/
theorem sinc_angle_pos (N : ℕ) (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) (htN : t < N) :
    0 < sinc (t*h N) := by
  rcases ht.eq_or_lt with ht | ht
  · simp [← ht]
  have ha := angle_mem N hN ht htN
  rw [sinc_of_ne_zero ha.1.ne']
  exact div_pos (sin_pos_of_mem_Ioo ha) ha.1

/--
Exact identity `ratio N (k+1)*sinc (((k:ℝ)+1)*h N) = ratio N k*sinc (((k:ℝ)+1/2)*h
N)*((k:ℝ)+1/2)/((k:ℝ)+1)`.

Use: `«2606.16671v2».SineJacobi.ratio_binomial_bounds` uses this identity to establish the
stated quantitative bound `binomialRatio k ≤ ratio N k ∧ ratio N k*sinc ((k:ℝ)*h N) ≤
binomialRatio k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ratio_sinc_recurrence (N k : ℕ) (hk : k+1 < N) :
    ratio N (k+1)*sinc (((k:ℝ)+1)*h N) =
      ratio N k*sinc (((k:ℝ)+1/2)*h N)*((k:ℝ)+1/2)/((k:ℝ)+1) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hN : 0 < N := by omega
  have ha := angle_mem N hN (t := (k:ℝ)+1/2) (by positivity)
    (by exact_mod_cast (show (k:ℝ)+1/2 < N by
      have hc : ((k:ℝ)+1) < N := by exact_mod_cast hk
      linarith))
  have hb := angle_mem N hN (t := (k:ℝ)+1) (by positivity) (by exact_mod_cast hk)
  rw [ratio, sinc_of_ne_zero ha.1.ne', sinc_of_ne_zero hb.1.ne']
  have hs := (sin_pos_of_mem_Ioo hb).ne'
  have hh : h N ≠ 0 := ne_of_gt (div_pos pi_pos (by exact_mod_cast hN))
  generalize sin (((k:ℝ)+1)*h N) = b at hs ⊢
  generalize sin (((k:ℝ)+1/2)*h N) = a
  field_simp [hs, hh]

/--
The stated quantitative bound `binomialRatio k ≤ ratio N k ∧ ratio N k*sinc ((k:ℝ)*h N) ≤
binomialRatio k`.

Use: `«2606.16671v2».SineJacobi.ratio_half_bounds` uses this bound to establish the stated
quantitative bound `binomialRatio k ≤ ratio N k ∧ ratio N k ≤ (Real.pi/2)*binomialRatio k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Proof: Induct on `k`; the recursive step uses the previous-stage assertion.
-/
theorem ratio_binomial_bounds (N k : ℕ) (hk : k < N) :
    binomialRatio k ≤ ratio N k ∧ ratio N k*sinc ((k:ℝ)*h N) ≤ binomialRatio k := by
  -- Induct on `k`; the recursive step uses the previous-stage assertion.
  induction k with
  | zero => simp [ratio]
  | succ k ih =>
    obtain ⟨hl, hu⟩ := ih (by omega)
    have hN : 0 < N := by omega
    have hNreal : 0 < (N:ℝ) := by exact_mod_cast hN
    have hc : ((k:ℝ)+1) < N := by exact_mod_cast hk
    have hh : 0 < h N := div_pos pi_pos hNreal
    have ha := angle_mem N hN (t := (k:ℝ)+1/2) (by positivity) (by linarith)
    have hb := angle_mem N hN (t := (k:ℝ)+1) (by positivity) hc
    have h0 : (k:ℝ)*h N ∈ Set.Icc (0:ℝ) Real.pi := by
      constructor
      · positivity
      · nlinarith [ha.2]
    have hmid := sinc_antitoneOn h0 ⟨ha.1.le, ha.2.le⟩ (by nlinarith : (k:ℝ)*h N ≤ ((k:ℝ)+1/2)*h N)
    have hright := sinc_antitoneOn ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ (by nlinarith : ((k:ℝ)+1/2)*h N ≤ ((k:ℝ)+1)*h N)
    have hr := ratio_sinc_recurrence N k hk
    rw [mul_div_assoc] at hr
    have hp := ratio_pos N k (by omega)
    have hs := sinc_angle_pos N hN (t := (k:ℝ)+1) (by positivity) hc
    have hq : 0 ≤ ((k:ℝ)+1/2)/((k:ℝ)+1) := by positivity
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hright hp.le
      have hnew := mul_le_mul_of_nonneg_right hmul hq
      rw [← hr] at hnew
      have hbnew := mul_le_mul_of_nonneg_right hl hq
      have hbnew' : binomialRatio (k+1) ≤ ratio N k * (((k:ℝ)+1/2)/((k:ℝ)+1)) := by
        simpa only [binomialRatio, mul_div_assoc] using hbnew
      apply (mul_le_mul_iff_left₀ hs).mp
      calc
        _ ≤ (ratio N k * (((k:ℝ)+1/2)/((k:ℝ)+1))) * sinc (((k:ℝ)+1)*h N) :=
          mul_le_mul_of_nonneg_right hbnew' hs.le
        _ = ratio N k*sinc (((k:ℝ)+1)*h N)*(((k:ℝ)+1/2)/((k:ℝ)+1)) := by ring
        _ ≤ _ := hnew
    · have hmul := mul_le_mul_of_nonneg_left hmid hp.le
      have hnew := mul_le_mul_of_nonneg_right (hmul.trans hu) hq
      rw [← hr] at hnew
      simpa only [binomialRatio, Nat.cast_add, Nat.cast_one, mul_div_assoc] using hnew

/--
The stated quantitative bound `binomialRatio k ≤ ratio N k ∧ ratio N k ≤
(Real.pi/2)*binomialRatio k`.

Use: `«2606.16671v2».SineJacobi.endpoint_half_bound` uses this bound to establish the stated
quantitative bound `endpoint N s ≤ (Real.pi^2/2)*Real.sqrt ((s:ℝ)+1)`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Proof: Separate `(k:ℝ)*h N = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem ratio_half_bounds (N k : ℕ) (hk : k < N) (hhalf : 2*k ≤ N) :
    binomialRatio k ≤ ratio N k ∧ ratio N k ≤ (Real.pi/2)*binomialRatio k := by
  -- Separate `(k:ℝ)*h N = 0` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  have hb := ratio_binomial_bounds N k hk
  refine ⟨hb.1, ?_⟩
  have hp := (ratio_pos N k hk).le
  have ha : (k:ℝ)*h N ∈ Set.Icc (0:ℝ) (Real.pi/2) := by
    have hN : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) (div_pos pi_pos hN).le
    · unfold h
      rw [← mul_div_assoc, div_le_iff₀ hN]
      have hk' : 2*(k:ℝ) ≤ N := by exact_mod_cast hhalf
      nlinarith [pi_pos]
  have hs : 2/Real.pi ≤ sinc ((k:ℝ)*h N) := by
    by_cases hz : (k:ℝ)*h N = 0
    · rw [hz, sinc_zero]
      apply (div_le_one pi_pos).mpr
      linarith [pi_gt_three]
    · rw [sinc_of_ne_zero hz]
      exact (le_div_iff₀ (lt_of_le_of_ne ha.1 (Ne.symm hz))).mpr (mul_le_sin ha.1 ha.2)
  have hl := (mul_le_mul_of_nonneg_left hs hp).trans hb.2
  have hm := mul_le_mul_of_nonneg_right hl (pi_pos.le : 0 ≤ Real.pi)
  have he : ratio N k*(2/Real.pi)*Real.pi = 2*ratio N k := by field_simp
  rw [he] at hm
  linarith

end
end «2606.16671v2».SineJacobi
