import «2606.16671v2».Analysis.SincDerivatives
import «2606.16671v2».Analysis.MidpointError
import «2606.16671v2».SineJacobi.RatioBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Article: 2606.16671v2, Theorem E.3.
The smooth logarithmic correction has a uniformly bounded second derivative on [0,b].
Use: `«2606.16671v2».SineJacobi.logSinc_second_bound` feeds
`«2606.16671v2».SineJacobi.logRatio_correction_limit` (log Ratio correction limit).
Proof chain: `«2606.16671v2».SineJacobi.ratio_scaled_limit` — 2606.16671v2, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set
open scoped ContDiff

/--
Defines `logSinc` of type `ℝ` by `log (sinc (Real.pi*x))`.

Use: `«2606.16671v2».SineJacobi.logSinc_second_bound` uses this definition to establish
constructs witnesses with the exact properties `∃ M, 0 ≤ M ∧ ∀ x ∈ Icc 0 b, |deriv (deriv
logSinc) x| ≤ M`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.
-/
def logSinc (x : ℝ) : ℝ := log (sinc (Real.pi*x))

/--
Exact identity `logSinc 0 = 0`.

Use: `«2606.16671v2».SineJacobi.logRatio_error_bound` uses this identity to establish the
stated quantitative bound `|logRatio N k+logSinc ((k:ℝ)/N)/2| ≤ M*(k:ℝ)/(N:ℝ)^2`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem logSinc_zero : logSinc 0 = 0 := by simp [logSinc]

/--
The stated quantitative bound `0 < sinc (Real.pi*x)`.

Use: `«2606.16671v2».SineJacobi.logSinc_contDiff` uses this bound to establish smoothness to
the stated order: `ContDiffOn ℝ 2 logSinc (Ioo (-1:ℝ) 1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Separate `x = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem sinc_pi_pos {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : 0 < sinc (Real.pi*x) := by
  -- Separate `x = 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hz : x = 0
  · simp [hz]
  have hax : 0 < |x| := abs_pos.mpr hz
  have hab : |x| < 1 := abs_lt.mpr hx
  have ha : Real.pi*|x| ∈ Ioo (0:ℝ) Real.pi :=
    ⟨mul_pos pi_pos hax, by nlinarith [pi_pos]⟩
  have hs : sinc (Real.pi*|x|) = sinc (Real.pi*x) := by
    rcases le_total 0 x with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hn, mul_neg, sinc_neg]
  rw [← hs, sinc_of_ne_zero ha.1.ne']
  exact div_pos (sin_pos_of_mem_Ioo ha) ha.1

/--
Smoothness to the stated order: `ContDiffOn ℝ 2 logSinc (Ioo (-1:ℝ) 1)`.

Use: `«2606.16671v2».SineJacobi.logSinc_second_bound` uses this assertion to establish
constructs witnesses with the exact properties `∃ M, 0 ≤ M ∧ ∀ x ∈ Icc 0 b, |deriv (deriv
logSinc) x| ≤ M`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Use the identities/estimates `«2606.16671v2».Analysis.sinc_contDiff_two`,
`«2606.16671v2».SineJacobi.sinc_pi_pos` with the arguments shown in the proof.
-/
theorem logSinc_contDiff : ContDiffOn ℝ 2 logSinc (Ioo (-1:ℝ) 1) := by
  apply ((«2606.16671v2».Analysis.sinc_contDiff_two.comp
    (show ContDiff ℝ 2 (fun x : ℝ => Real.pi*x) by fun_prop)).contDiffOn).log
  exact fun x hx => (sinc_pi_pos hx).ne'

/--
The smooth logarithmic correction has a uniformly bounded second derivative on [0,b].

Constructs witnesses with the exact properties `∃ M, 0 ≤ M ∧ ∀ x ∈ Icc 0 b, |deriv (deriv
logSinc) x| ≤ M`.

Use: `«2606.16671v2».SineJacobi.logRatio_correction_limit` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun a =>
logRatio (N a) (k a)+logSinc ((k a:ℝ)/(N a:ℝ))/2) l (𝓝 0)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.logSinc_contDiff` with the
arguments shown in the proof.
-/
theorem logSinc_second_bound {b : ℝ} (_hb : 0 ≤ b) (hb1 : b < 1) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ Icc 0 b, |deriv (deriv logSinc) x| ≤ M := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.logSinc_contDiff` with the
  -- arguments shown in the proof.
  have hsub : Icc (0:ℝ) b ⊆ Ioo (-1:ℝ) 1 :=
    fun x hx => ⟨by linarith [hx.1], hx.2.trans_lt hb1⟩
  have h1 : ContDiffOn ℝ 1 (deriv logSinc) (Ioo (-1:ℝ) 1) :=
    logSinc_contDiff.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h2 := (h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := b)).bddAbove_image h2.norm
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  have hh := hM (mem_image_of_mem (fun x : ℝ => ‖deriv (deriv logSinc) x‖) hx)
  simp only [Real.norm_eq_abs] at hh
  exact hh.trans (le_max_left _ _)

end
end «2606.16671v2».SineJacobi
