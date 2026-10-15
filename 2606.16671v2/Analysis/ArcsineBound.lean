import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
Article: 2606.16671v2, Theorem E.3.
Arcsine Bound.
Use: `«2606.16671v2».Analysis.arcsineBound_integrable` feeds
`«2606.16671v2».SineJacobi.convolutionIntegral_limit` (The convolution limit includes both singular
endpoints, by dominated convergence).
Proof chain: `«2606.16671v2».SineJacobi.convolutionIntegral_limit` — 2606.16671v2, Theorem E.3;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
Source: mathlib, Mathlib.Analysis.SpecialFunctions.Integrability.Basic,
Mathlib.Analysis.SpecialFunctions.Pow.Real — integrability of the beta(1/2,1/2) endpoint majorant.
The needed form is proved here.
-/
namespace «2606.16671v2».Analysis
noncomputable section
open Real Set MeasureTheory

/--
Defines `arcsineBound` of type `ℝ` by `1/(sqrt x*sqrt (1-x))`.

Use: `«2606.16671v2».Analysis.arcsineBound_integrable` uses this definition to establish
integrability on the stated domain: `IntegrableOn arcsineBound (Ioo (0:ℝ) 1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Integrability.Basic,
Mathlib.Analysis.SpecialFunctions.Pow.Real — integrability of the beta(1/2,1/2) endpoint
majorant.
-/
def arcsineBound (x : ℝ) : ℝ := 1/(sqrt x*sqrt (1-x))

/--
The stated quantitative bound `0 ≤ arcsineBound x`.

Use: `«2606.16671v2».Analysis.arcsineBound_integrable` rewrites with this bound to establish
integrability on the stated domain: `IntegrableOn arcsineBound (Ioo (0:ℝ) 1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Integrability.Basic,
Mathlib.Analysis.SpecialFunctions.Pow.Real — integrability of the beta(1/2,1/2) endpoint
majorant.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem arcsineBound_nonneg (x : ℝ) : 0 ≤ arcsineBound x := by unfold arcsineBound; positivity

/--
The stated quantitative bound `arcsineBound x ≤ 2*(1/sqrt x+1/sqrt (1-x))`.

Use: `«2606.16671v2».Analysis.arcsineBound_integrable` uses this bound to establish
integrability on the stated domain: `IntegrableOn arcsineBound (Ioo (0:ℝ) 1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Integrability.Basic,
Mathlib.Analysis.SpecialFunctions.Pow.Real — integrability of the beta(1/2,1/2) endpoint
majorant.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem arcsineBound_le {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    arcsineBound x ≤ 2*(1/sqrt x+1/sqrt (1-x)) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have ha := sqrt_pos.mpr hx.1
  have hb := sqrt_pos.mpr (by linarith [hx.2] : 0 < 1-x)
  unfold arcsineBound
  rcases le_total x (1/2:ℝ) with hl | hr
  · have hroot : (1/2:ℝ) ≤ sqrt (1-x) := le_sqrt_of_sq_le (by nlinarith)
    have hden : sqrt x/2 ≤ sqrt x*sqrt (1-x) := by nlinarith
    have hh := one_div_le_one_div_of_le (half_pos ha) hden
    have hp : 0 ≤ 1/sqrt (1-x) := by positivity
    calc
      _ ≤ 1/(sqrt x/2) := hh
      _ = 2*(1/sqrt x) := by ring
      _ ≤ _ := by linarith
  · have hroot : (1/2:ℝ) ≤ sqrt x := le_sqrt_of_sq_le (by nlinarith)
    have hden : sqrt (1-x)/2 ≤ sqrt x*sqrt (1-x) := by nlinarith
    have hh := one_div_le_one_div_of_le (half_pos hb) hden
    have hp : 0 ≤ 1/sqrt x := by positivity
    calc
      _ ≤ 1/(sqrt (1-x)/2) := hh
      _ = 2*(1/sqrt (1-x)) := by ring
      _ ≤ _ := by linarith

/--
The stated quantitative bound `IntervalIntegrable (fun x : ℝ => 1/sqrt x) volume 0 1`.

Use: `«2606.16671v2».Analysis.arcsineBound_integrable` uses this identity to establish
integrability on the stated domain: `IntegrableOn arcsineBound (Ioo (0:ℝ) 1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Integrability.Basic,
Mathlib.Analysis.SpecialFunctions.Pow.Real — integrability of the beta(1/2,1/2) endpoint
majorant.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem inverse_sqrt_intervalIntegrable :
    IntervalIntegrable (fun x : ℝ => 1/sqrt x) volume 0 1 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  apply (intervalIntegral.intervalIntegrable_rpow' (r := -(1/2:ℝ)) (by norm_num)
    (a := 0) (b := 1)).congr_uIoo
  intro x hx
  rw [uIoo_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
  change x^(-(1/2:ℝ)) = 1/sqrt x
  rw [rpow_neg hx.1.le, ← sqrt_eq_rpow]
  simp only [one_div]

/--
Integrability on the stated domain: `IntegrableOn arcsineBound (Ioo (0:ℝ) 1)`.

Use: `«2606.16671v2».SineJacobi.convolutionIntegral_limit` uses this integrability result to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun a
=> ∫ x in (0:ℝ)..1, convolutionStep (N a) (s a) x) l (𝓝 (convolutionIntegral t))`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Integrability.Basic,
Mathlib.Analysis.SpecialFunctions.Pow.Real — integrability of the beta(1/2,1/2) endpoint
majorant.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem arcsineBound_integrable : IntegrableOn arcsineBound (Ioo (0:ℝ) 1) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have h1 := inverse_sqrt_intervalIntegrable
  have h2 : IntervalIntegrable (fun x : ℝ => 1/sqrt (1-x)) volume 0 1 := by
    simpa using (h1.comp_sub_left 1).symm
  have hdom := (h1.add h2).const_mul 2
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0:ℝ) ≤ 1)] at hdom
  have hm : Measurable arcsineBound := by unfold arcsineBound; fun_prop
  apply hdom.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (arcsineBound_nonneg x)]
  exact arcsineBound_le hx

end
end «2606.16671v2».Analysis
