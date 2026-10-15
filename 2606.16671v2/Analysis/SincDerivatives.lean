import «2606.16671v2».Analysis.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Article: 2606.16671v2, Theorem E.3.
Sinc Derivatives.
Use: `«2606.16671v2».Analysis.sinc_contDiff_two` feeds `«2606.16671v2».SineJacobi.logSinc_contDiff`
(log Sinc cont Diff).
Proof chain: `«2606.16671v2».SineJacobi.ratio_scaled_limit` — 2606.16671v2, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc,
Mathlib.Analysis.SpecialFunctions.Integrals.Basic — integral representation and differentiation of
sinc. The needed form is proved here.
-/
namespace «2606.16671v2».Analysis
noncomputable section
open Real Set MeasureTheory
open scoped ContDiff

/--
Defines `sinc₁` of type `ℝ` by `∫ t in (0:ℝ)..1, -t*sin (x*t)`.

Use: `«2606.16671v2».Analysis.sinc_contDiff_two` uses this definition to establish smoothness
to the stated order: `ContDiff ℝ 2 sinc`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc,
Mathlib.Analysis.SpecialFunctions.Integrals.Basic — integral representation and differentiation
of sinc.
-/
def sinc₁ (x : ℝ) : ℝ := ∫ t in (0:ℝ)..1, -t*sin (x*t)
/--
Defines `sinc₂` of type `ℝ` by `∫ t in (0:ℝ)..1, -t^2*cos (x*t)`.

Use: `«2606.16671v2».Analysis.sinc_contDiff_two` uses this definition to establish smoothness
to the stated order: `ContDiff ℝ 2 sinc`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc,
Mathlib.Analysis.SpecialFunctions.Integrals.Basic — integral representation and differentiation
of sinc.
-/
def sinc₂ (x : ℝ) : ℝ := ∫ t in (0:ℝ)..1, -t^2*cos (x*t)

/--
Exact identity `sinc x = ∫ t in (0:ℝ)..1, cos (x*t)`.

Use: `«2606.16671v2».Analysis.sinc_deriv` rewrites with this identity to establish the actual
derivative at the stated point: `HasDerivAt sinc (sinc₁ x) x`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc,
Mathlib.Analysis.SpecialFunctions.Integrals.Basic — integral representation and differentiation
of sinc.

Proof: Separate `x = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem sinc_eq_integral (x : ℝ) : sinc x = ∫ t in (0:ℝ)..1, cos (x*t) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [intervalIntegral.integral_comp_mul_left _ hx, integral_cos, mul_zero, mul_one,
    sin_zero, sub_zero, sinc_of_ne_zero hx]
  ring

/--
The actual derivative at the stated point: `HasDerivAt sinc (sinc₁ x) x`.

Use: `«2606.16671v2».Analysis.sinc_contDiff_two` uses this derivative formula to establish
smoothness to the stated order: `ContDiff ℝ 2 sinc`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc,
Mathlib.Analysis.SpecialFunctions.Integrals.Basic — integral representation and differentiation
of sinc.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sinc_deriv (x : ℝ) : HasDerivAt sinc (sinc₁ x) x := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  rw [show sinc = (fun u => ∫ t in (0:ℝ)..1, cos (u*t)) from funext sinc_eq_integral]
  apply hasDerivAt_integral_rectangle
    (fun u t => cos (u*t)) (fun u t => -t*sin (u*t))
    (lo := x-1) (hi := x+1) (by constructor <;> linarith) (by norm_num)
  · intro u _; fun_prop
  · fun_prop
  · intro u _ t _
    convert ((hasDerivAt_id u).mul_const t).cos using 1 <;> simp ; ring

/--
The actual derivative at the stated point: `HasDerivAt sinc₁ (sinc₂ x) x`.

Use: `«2606.16671v2».Analysis.sinc_contDiff_two` uses this derivative formula to establish
smoothness to the stated order: `ContDiff ℝ 2 sinc`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc,
Mathlib.Analysis.SpecialFunctions.Integrals.Basic — integral representation and differentiation
of sinc.

Proof: Use the identities/estimates `«2606.16671v2».Analysis.hasDerivAt_integral_rectangle`
with the arguments shown in the proof.
-/
theorem sinc₁_deriv (x : ℝ) : HasDerivAt sinc₁ (sinc₂ x) x := by
  apply hasDerivAt_integral_rectangle
    (fun u t => -t*sin (u*t)) (fun u t => -t^2*cos (u*t))
    (lo := x-1) (hi := x+1) (by constructor <;> linarith) (by norm_num)
  · intro u _; fun_prop
  · fun_prop
  · intro u _ t _
    convert (((hasDerivAt_id u).mul_const t).sin.const_mul (-t)) using 1 <;> simp ; ring

/--
Continuity of the displayed function: `Continuous sinc₁`.

Use: a standalone supporting continuity result for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem E.3.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc,
Mathlib.Analysis.SpecialFunctions.Integrals.Basic — integral representation and differentiation
of sinc.

Proof: Use the identities/estimates `«2606.16671v2».Analysis.sinc₁_deriv` with the arguments
shown in the proof.
-/
theorem sinc₁_continuous : Continuous sinc₁ :=
  continuous_iff_continuousAt.mpr fun x => (sinc₁_deriv x).continuousAt

/--
Continuity of the displayed function: `Continuous sinc₂`.

Use: `«2606.16671v2».Analysis.sinc_contDiff_two` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 2 sinc`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc,
Mathlib.Analysis.SpecialFunctions.Integrals.Basic — integral representation and differentiation
of sinc.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sinc₂_continuous : Continuous sinc₂ := by
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous (fun p : ℝ × ℝ => -p.2^2*cos (p.1*p.2)) := by fun_prop
  have hi := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun x t : ℝ => -t^2*cos (x*t)) hc
    (isCompact_Icc (a := (0:ℝ)) (b := 1))
  convert hi using 1
  funext x
  rw [sinc₂, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc]

/--
Smoothness to the stated order: `ContDiff ℝ 2 sinc`.

Use: `«2606.16671v2».SineJacobi.logSinc_contDiff` uses this assertion to establish smoothness
to the stated order: `ContDiffOn ℝ 2 logSinc (Ioo (-1:ℝ) 1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc,
Mathlib.Analysis.SpecialFunctions.Integrals.Basic — integral representation and differentiation
of sinc.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sinc_contDiff_two : ContDiff ℝ 2 sinc := by
  have hd1 : deriv sinc = sinc₁ := funext fun x => (sinc_deriv x).deriv
  have hd2 : deriv sinc₁ = sinc₂ := funext fun x => (sinc₁_deriv x).deriv
  have h1 : ContDiff ℝ 1 sinc₁ := by
    rw [contDiff_one_iff_deriv, hd2]
    exact ⟨fun x => (sinc₁_deriv x).differentiableAt, sinc₂_continuous⟩
  rw [show (2 : ℕ∞ω) = 1+1 by rfl, contDiff_succ_iff_deriv, hd1]
  exact ⟨fun x => (sinc_deriv x).differentiableAt, by simp, h1⟩

end
end «2606.16671v2».Analysis
