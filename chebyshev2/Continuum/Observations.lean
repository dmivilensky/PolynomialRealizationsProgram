import chebyshev2.Continuum.SpectralDistance
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Article: chebyshev2, Theorem 2.4.
Observations.
Use: `chebyshev2.Continuum.ground_parameter_distance` feeds
`chebyshev2.Packing.packed_ground_parameter_distance` (Theorem 2.4, equation (9): the reciprocal
leading eigenvalue).
Proof chain: `chebyshev2.Packing.packed_ground_parameter_distance` — chebyshev2, Theorem 2.4;
Uniform l1 spectral transfer, ground parameter and Fredholm/cosh observations.
-/
namespace chebyshev2.Continuum
noncomputable section
open Real
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `log x - log y ≤ x - y`.

Use: `chebyshev2.Continuum.log_abs_sub_le` uses this bound to establish the stated
quantitative bound `|log x - log y| ≤ |x - y|`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packed_fredholm_observation_distance`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem log_sub_le_sub {x y : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) : log x - log y ≤ x - y := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hy.trans hxy)
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hy
  have h := log_le_sub_one_of_pos (div_pos hxpos hypos)
  rw [log_div hxpos.ne' hypos.ne'] at h
  have hh : x / y - 1 = (x - y) / y := by field_simp
  rw [hh] at h
  exact h.trans (div_le_self (sub_nonneg.mpr hxy) hy)

/--
The stated quantitative bound `|log x - log y| ≤ |x - y|`.

Use: `chebyshev2.Continuum.spectral_log_lipschitz` uses this bound to establish the stated
quantitative bound `|log (1 + s / 2 * x) - log (1 + s / 2 * y)| ≤ s / 2 * |x - y|`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packed_fredholm_observation_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.log_sub_le_sub` with the
arguments shown in the proof.
-/
theorem log_abs_sub_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : |log x - log y| ≤ |x - y| := by
  -- Use the identities/estimates `chebyshev2.Continuum.log_sub_le_sub` with the arguments
  -- shown in the proof.
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (log_le_log (by linarith) hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have h := log_sub_le_sub hx hxy
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (log_le_log (by linarith) hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact log_sub_le_sub hy hyx

/--
The stated quantitative bound `|log (1 + s / 2 * x) - log (1 + s / 2 * y)| ≤ s / 2 * |x - y|`.

Use: `chebyshev2.Continuum.logDeterminant_distance` uses this bound to establish the stated
quantitative bound `|logDeterminant a s - logDeterminant b s| ≤ s / 2 * ∑' j, |a j - b j|`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packed_fredholm_observation_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.log_abs_sub_le` with the
arguments shown in the proof.
-/
theorem spectral_log_lipschitz {s x y : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |log (1 + s / 2 * x) - log (1 + s / 2 * y)| ≤ s / 2 * |x - y| := by
  have h := log_abs_sub_le (le_add_of_nonneg_right
    (mul_nonneg (by positivity : 0 ≤ s / 2) hx))
    (le_add_of_nonneg_right (mul_nonneg (by positivity : 0 ≤ s / 2) hy))
  have he : (1 + s / 2 * x) - (1 + s / 2 * y) = s / 2 * (x - y) := by ring
  rwa [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s / 2)] at h

/--
Defines `logDeterminant` of type `ℝ` by `∑' j, log (1 + s / 2 * a j)`.

Use: `chebyshev2.Continuum.logDeterminant_distance` rewrites with this definition to
establish the stated quantitative bound `|logDeterminant a s - logDeterminant b s| ≤ s / 2 * ∑'
j, |a j - b j|`.

Article: chebyshev2, Theorem 2.4 via `chebyshev2.Continuum.reference_logDeterminant`.
-/
def logDeterminant (a : ℕ → ℝ) (s : ℝ) : ℝ := ∑' j, log (1 + s / 2 * a j)

/--
Summability of the displayed sequence: `Summable (fun j => log (1 + s / 2 * a j))`.

Use: `chebyshev2.Continuum.logDeterminant_distance` rewrites with this summability result
to prove the bound `|logDeterminant a s - logDeterminant b s| ≤ s / 2 *
∑' j, |a j - b j|`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Continuum.reference_fredholmDeterminant`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem log_spectral_summable {a : ℕ → ℝ} (ha : Summable a) (hn : ∀ j, 0 ≤ a j)
    {s : ℝ} (hs : 0 ≤ s) : Summable (fun j => log (1 + s / 2 * a j)) := by
  -- The tactic block explicitly constructs the required witness or reduces the goal to the
  -- local facts stated below.
  apply (ha.mul_left (s / 2)).of_nonneg_of_le
  · intro j
    apply log_nonneg
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (hn j))
  · intro j
    have hj := hn j
    have h := log_le_sub_one_of_pos (show 0 < 1 + s / 2 * a j by positivity)
    linarith

/--
The stated quantitative bound `|logDeterminant a s - logDeterminant b s| ≤ s / 2 * ∑' j, |a j -
b j|`.

Use: `chebyshev2.Continuum.logDeterminant_traceBound` uses this bound to establish the
stated quantitative bound `|logDeterminant DA.eigenvalue s-logDeterminant DB.eigenvalue s| ≤
s/2*C`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packed_fredholm_observation_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.log_spectral_summable`,
`chebyshev2.Continuum.spectral_log_lipschitz` with the arguments shown in the proof.
-/
theorem logDeterminant_distance {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (hna : ∀ j, 0 ≤ a j) (hnb : ∀ j, 0 ≤ b j) {s : ℝ} (hs : 0 ≤ s) :
    |logDeterminant a s - logDeterminant b s| ≤ s / 2 * ∑' j, |a j - b j| := by
  -- Use the identities/estimates `chebyshev2.Continuum.log_spectral_summable`,
  -- `chebyshev2.Continuum.spectral_log_lipschitz` with the arguments shown in the proof.
  rw [logDeterminant, logDeterminant, ← (log_spectral_summable ha hna hs).tsum_sub
    (log_spectral_summable hb hnb hs)]
  have he := norm_tsum_le_tsum_norm ((log_spectral_summable ha hna hs).sub
    (log_spectral_summable hb hnb hs)).norm
  rw [Real.norm_eq_abs] at he
  apply he.trans
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro j
    rw [Real.norm_eq_abs]
    exact spectral_log_lipschitz hs (hna j) (hnb j)
  · exact ((log_spectral_summable ha hna hs).sub (log_spectral_summable hb hnb hs)).norm
  · exact ((ha.sub hb).abs).mul_left _

/--
The stated quantitative bound `|(∑' j, a j ^ 2) - ∑' j, b j ^ 2| ≤ 2 * ∑' j, |a j - b j|`.

Use: `chebyshev2.Packing.packed_square_trace_distance` uses this bound to establish the
stated quantitative bound `|(∑' j, packedEigenvalue J hN ht j^2)-(2/3 : ℝ)| ≤ 2*transferError
N`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packed_square_integral_distance`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem square_trace_distance {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (hna : ∀ j, 0 ≤ a j) (hnb : ∀ j, 0 ≤ b j) (ha1 : ∀ j, a j ≤ 1) (hb1 : ∀ j, b j ≤ 1) :
    |(∑' j, a j ^ 2) - ∑' j, b j ^ 2| ≤ 2 * ∑' j, |a j - b j| := by
  -- Prove the summability hsa needed for the later infinite-sum manipulations.
  have hsa : Summable (fun j => a j ^ 2) := ha.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
    nlinarith [hna j, ha1 j])
  -- Prove the summability hsb needed for the later infinite-sum manipulations.
  have hsb : Summable (fun j => b j ^ 2) := hb.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
    nlinarith [hnb j, hb1 j])
  rw [← hsa.tsum_sub hsb]
  apply (norm_tsum_le_tsum_norm (hsa.sub hsb).norm).trans
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro j
    rw [Real.norm_eq_abs, show a j ^ 2 - b j ^ 2 = (a j - b j) * (a j + b j) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (hna j) (hnb j))]
    nlinarith [abs_nonneg (a j-b j), ha1 j, hb1 j]
  · exact (hsa.sub hsb).norm
  · exact ((ha.sub hb).abs).mul_left 2

/--
The stated quantitative bound `|2 / a - 2 / b| ≤ 4 * δ / b ^ 2`.

Use: `chebyshev2.Packing.packed_ground_parameter_distance` uses this bound to establish the
stated quantitative bound `|2/packedEigenvalue J hN ht 0-Real.pi^2/4| ≤ 4*transferError
N/(referenceEigenvalue 0)^2`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packed_ground_parameter_distance`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ground_parameter_distance {a b δ : ℝ} (hb : 0 < b) (hd : |a - b| ≤ δ) (hδ : δ < b / 2) :
    |2 / a - 2 / b| ≤ 4 * δ / b ^ 2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have ha : b / 2 < a := by have h := (abs_le.mp hd).1; linarith
  have hap : 0 < a := lt_trans (half_pos hb) ha
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hd
  have he : 2 / a - 2 / b = -(2 * (a - b) / (a * b)) := by field_simp; ring
  rw [he, abs_neg, abs_div, abs_mul, abs_of_pos (mul_pos hap hb)]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |a - b| / (a * b) ≤ 2 * δ / (a * b) := by gcongr
    _ ≤ 2 * δ / (b / 2 * b) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right ha.le hb.le
    _ = 4 * δ / b ^ 2 := by field_simp; ring

end
end chebyshev2.Continuum
