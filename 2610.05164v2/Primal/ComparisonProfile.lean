import «2610.05164v2».Primal.Amplitude

/-!
Article: 2610.05164v2, Theorem 3.4.
Every continuous primal logarithmic profile satisfies Definition 10.
Use: `«2610.05164v2».Primal.comparisonProfile` feeds `«2610.05164v2».Primal.comparison_speed`
(comparison speed).
Proof chain: `«2610.05164v2».Primal.comparison_density` — 2610.05164v2, Theorem 3.4; Signed
determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set Real MeasureTheory «2610.05164v2».Calibration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `regularRatio` of type `ℝ` by `(normalizedAmplitude φ κ t)^2/exp (φ t)+ (2-t^3)/(exp (φ
t)*normalizedAmplitude φ κ t)+ (normalizedAmplitude φ κ t)^3/(2-t^3)`.

Use: `«2610.05164v2».Primal.amplitude_ratio` uses this definition to establish the identity
`(amplitude φ κ q)^2/(κ*(amplitude φ κ q)^2-Q q)+ Q q/((κ*(amplitude φ κ q)^2-Q q)*amplitude φ
κ q)+ (amplitude φ κ q)^3/Q q=regularRatio φ κ (coordinate q)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def regularRatio (φ : ℝ → ℝ) (κ t : ℝ) : ℝ :=
  (normalizedAmplitude φ κ t)^2/exp (φ t)+
    (2-t^3)/(exp (φ t)*normalizedAmplitude φ κ t)+
    (normalizedAmplitude φ κ t)^3/(2-t^3)

/--
Continuity on the stated domain: `ContinuousOn (regularRatio φ κ) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Primal.comparisonProfile` uses this continuity result in the displayed
construction of `comparisonProfile`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.normalizedAmplitude_continuous`,
`«2610.05164v2».Primal.normalizedAmplitude_positive` with the arguments shown in the proof.
-/
theorem regularRatio_continuousOn {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ : ℝ} (hκ : 0<κ) : ContinuousOn (regularRatio φ κ) (Icc (0:ℝ) 1) := by
  -- Use the identities/estimates `«2610.05164v2».Primal.normalizedAmplitude_continuous`,
  -- `«2610.05164v2».Primal.normalizedAmplitude_positive` with the arguments shown in the
  -- proof.
  have hz := (normalizedAmplitude_continuous hφ κ).continuousOn (s:=Icc (0:ℝ) 1)
  have he := (continuous_exp.comp hφ).continuousOn (s:=Icc (0:ℝ) 1)
  -- Establish continuity hh before using the function at limits or in calculus arguments.
  have hh : ContinuousOn (fun t:ℝ => 2-t^3) (Icc (0:ℝ) 1) := by fun_prop
  apply ((hz.pow 2).div he (fun t _ => exp_ne_zero (φ t))).add
    (hh.div (he.mul hz) (fun t ht => mul_ne_zero (exp_ne_zero _)
      (normalizedAmplitude_positive φ hκ ht).ne')) |>.add
    ((hz.pow 3).div hh (fun t ht => ne_of_gt (by
      have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
      linarith)))

/--
Exact identity `(amplitude φ κ q)^2/(κ*(amplitude φ κ q)^2-Q q)+ Q q/((κ*(amplitude φ κ q)^2-Q
q)*amplitude φ κ q)+ (amplitude φ κ q)^3/Q q=regularRatio φ κ (coordinate q)`.

Use: `«2610.05164v2».Primal.comparisonProfile` uses this identity in the displayed construction
of `comparisonProfile`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem amplitude_ratio (φ : ℝ → ℝ) {κ q : ℝ} (hκ : 0<κ)
    (hq : q∈Ioo (0:ℝ) 2) :
    (amplitude φ κ q)^2/(κ*(amplitude φ κ q)^2-Q q)+
      Q q/((κ*(amplitude φ κ q)^2-Q q)*amplitude φ κ q)+
      (amplitude φ κ q)^3/Q q=regularRatio φ κ (coordinate q) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hqc : q∈Icc (0:ℝ) 2 := ⟨hq.1.le,hq.2.le⟩
  have ht := coordinate_mem hqc
  have htpos := coordinate_positive hq
  have hz := normalizedAmplitude_positive φ hκ ht
  have ht3 : (coordinate q)^3≤1 := pow_le_one₀ ht.1 ht.2
  have hh : 0<2-(coordinate q)^3 := by linarith
  rw [amplitude_square φ hκ hqc,Q_coordinate hqc]
  unfold amplitude speed regularRatio
  field_simp [htpos.ne',hz.ne',hh.ne',exp_ne_zero]

/--
Constructs `comparisonProfile` of type `«2610.05164v2».Comparison.Profile κ` by the displayed
record fields. Data fields specify the construction; proof fields discharge its required
properties.

Use: `«2610.05164v2».Primal.determinantDifferenceDensity_integrable` uses this definition to
establish integrability of the displayed function: `Integrable (determinantDifferenceDensity hφ
hψ κ s)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def comparisonProfile {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    «2610.05164v2».Comparison.Profile κ where
  amplitude := amplitude φ κ
  continuous := (amplitude_continuous hφ κ).continuousOn
  nonneg := fun q hq => mul_nonneg (coordinate_nonneg hq) (sqrt_nonneg _)
  positive := fun q hq => mul_pos (coordinate_positive hq)
    (normalizedAmplitude_positive φ hκ (coordinate_mem ⟨hq.1.le,hq.2.le⟩))
  speed_positive := fun q hq => by
    rw [amplitude_square φ hκ ⟨hq.1.le,hq.2.le⟩]
    exact speed_positive φ hq
  reciprocal_integrable := (reciprocal_integrable hφ).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    rw [amplitude_square φ hκ ⟨hq.1.le,hq.2.le⟩])
  C := Classical.choose (isCompact_Icc.bddAbove_image (regularRatio_continuousOn hφ hκ))
  bound := by
    intro q hq
    rw [amplitude_ratio φ hκ hq]
    exact Classical.choose_spec (isCompact_Icc.bddAbove_image (regularRatio_continuousOn hφ hκ))
      (mem_image_of_mem _ (coordinate_mem ⟨hq.1.le,hq.2.le⟩))

end
end «2610.05164v2».Primal
