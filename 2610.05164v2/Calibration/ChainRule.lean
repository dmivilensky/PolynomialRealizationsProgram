import «2610.05164v2».Filters.Cumulative
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
Article: 2610.05164v2, Proposition 4.
Chain rules and improper FTC used by the calibration and residual.
Use: `«2610.05164v2».Calibration.continuous_mul_derivative_integrable` feeds
`«2610.05164v2».Calibration.Data.J_composition_integrable` (J composition integrable).
Proof chain: `«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` — 2610.05164v2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace «2610.05164v2».Calibration
noncomputable section
open Set MeasureTheory Filter «2610.05164v2».Sobolev
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (fun t => φ (f
t)) x y`.

Use: `«2610.05164v2».Calibration.Data.J_composition_mass` uses this identity to establish exact
identity `(∫ x, C.Jprime (C.calibrationState G x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm
hn x)^2-2*C.calibrationState G x))=C.J 2`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem locallyAC_comp_c1_interval {f φ : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, f x ∈ Icc a b) (hac : ∀ x y, AbsolutelyContinuousOnInterval f x y)
    (hφ : ContDiff ℝ 1 φ) (x y : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => φ (f t)) x y := by
  obtain ⟨K,hK⟩ := hφ.contDiffOn.exists_lipschitzOnWith (by decide) (convex_Icc a b) isCompact_Icc
  exact hK.comp_absolutelyContinuousOnInterval (fun t _ => hf t) (hac x y)

/--
Exact identity `(∫ x, d x)=hi-lo`.

Use: `«2610.05164v2».Calibration.Data.J_composition_mass` uses this identity to establish exact
identity `(∫ x, C.Jprime (C.calibrationState G x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm
hn x)^2-2*C.calibrationState G x))=C.J 2`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.locallyAC_integral_eq_sub` with the
arguments shown in the proof.
-/
theorem integral_derivative_eq_limits {f d : ℝ → ℝ} {lo hi : ℝ}
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, HasDerivAt f (d x) x) (hint : Integrable d)
    (hl : Tendsto f atBot (𝓝 lo)) (hr : Tendsto f atTop (𝓝 hi)) :
    (∫ x, d x)=hi-lo := by
  -- Use the identities/estimates `«2610.05164v2».Sobolev.locallyAC_integral_eq_sub` with the
  -- arguments shown in the proof.
  have ht := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hint.integrableOn tendsto_id
  have hb := intervalIntegral_tendsto_integral_Iic (0:ℝ) hint.integrableOn tendsto_id
  have et : (∫ x in Ioi (0:ℝ), d x)=hi-f 0 := by
    apply tendsto_nhds_unique ht
    simpa only [locallyAC_integral_eq_sub hac hd,id_eq] using hr.sub_const (f 0)
  have eb : (∫ x in Iic (0:ℝ), d x)=f 0-lo := by
    apply tendsto_nhds_unique hb
    simpa only [locallyAC_integral_eq_sub hac hd,id_eq] using hl.const_sub (f 0)
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn (b := 0),et,eb]
  ring

/--
Defines `primitive` of type `ℝ` by `∫ t in (0:ℝ)..x, f t`.

Use: `«2610.05164v2».Calibration.primitive_c1` uses this definition to establish smoothness to
the stated order: `ContDiff ℝ 1 (primitive f)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def primitive (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, f t

/--
The actual derivative at the stated point: `HasDerivAt (primitive f) (f x) x`.

Use: `«2610.05164v2».Calibration.primitive_c1` uses this derivative formula to establish
smoothness to the stated order: `ContDiff ℝ 1 (primitive f)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem primitive_derivative {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

/--
Smoothness to the stated order: `ContDiff ℝ 1 (primitive f)`.

Use: `«2610.05164v2».Calibration.Data.J_c1` uses this assertion to establish smoothness to the
stated order: `ContDiff ℝ 1 C.J`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem primitive_c1 {f : ℝ → ℝ} (hf : Continuous f) : ContDiff ℝ 1 (primitive f) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (primitive_derivative hf x).differentiableAt,?_⟩
  have he : deriv (primitive f)=f := funext (fun x => (primitive_derivative hf x).deriv)
  rwa [he]

/--
Integrability of the displayed function: `Integrable (fun x => w (f x)*d x)`.

Use: `«2610.05164v2».Calibration.Data.J_composition_integrable` uses this integrability result
to establish integrability of the displayed function: `Integrable (fun x => C.Jprime
(C.calibrationState G x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn
x)^2-2*C.calibrationState G x))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem continuous_mul_derivative_integrable {f d w : ℝ → ℝ} {B : ℝ}
    (hf : Continuous f) (hw : Continuous w) (hd : Integrable d)
    (hb : ∀ x, ‖w (f x)‖ ≤ B) : Integrable (fun x => w (f x)*d x) :=
  hd.bdd_mul (hw.comp hf).aestronglyMeasurable (Eventually.of_forall hb)

end
end «2610.05164v2».Calibration
