import chebyshev2.PrescribedSpeed.Article
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
Article: chebyshev2, Theorem 5.1.
Definition 9's symmetric cubic-coordinate speed for an arbitrary continuous logarithmic profile.
Use: `chebyshev2.Primal.ground_exact` feeds `chebyshev2.Primal.square_trace_cubic` (square
trace cubic).
-/
namespace chebyshev2.Primal
noncomputable section
open Set MeasureTheory Real chebyshev2.PrescribedSpeed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `coordinate` of type `ℝ` by `(min q (2-q))^(1/3:ℝ)`.

Use: `chebyshev2.Primal.coordinate_reflection` rewrites with this definition to establish
exact identity `coordinate (2-q)=coordinate q`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.density_moment_cubic`.
-/
def coordinate (q : ℝ) : ℝ := (min q (2-q))^(1/3:ℝ)
/--
Defines `speed` of type `ℝ` by `(coordinate q)^2*exp (φ (coordinate q))`.

Use: `chebyshev2.Primal.reciprocal_identity` rewrites with this definition to establish
exact identity `(speed φ q)⁻¹=exp (-φ (coordinate q))*(min q (2-q))^(-(2/3:ℝ))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.density_moment_cubic`.
-/
def speed (φ : ℝ → ℝ) (q : ℝ) : ℝ := (coordinate q)^2*exp (φ (coordinate q))

/--
Continuity of the displayed function: `Continuous coordinate`.

Use: `chebyshev2.Primal.reciprocal_integrable` uses this continuity result to establish
integrability on the stated domain: `IntegrableOn (fun q => (speed φ q)⁻¹) (Ioo (0:ℝ) 2)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.ground_exact`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem coordinate_continuous : Continuous coordinate :=
  (continuous_rpow_const (by norm_num : (0:ℝ)≤1/3)).comp
    (continuous_id.min (continuous_const.sub continuous_id))

/--
The stated quantitative bound `0≤coordinate q`.

Use: `chebyshev2.Primal.coordinate_mem` uses this bound to establish membership in the
specified domain/enclosure: `coordinate q∈Icc (0:ℝ) 1`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem coordinate_nonneg {q : ℝ} (hq : q∈Icc (0:ℝ) 2) : 0≤coordinate q :=
  rpow_nonneg (le_min hq.1 (by linarith [hq.2])) _

/--
The stated quantitative bound `0<coordinate q`.

Use: `chebyshev2.Primal.speed_positive` uses this bound to establish the stated
quantitative bound `0<speed φ q`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.ground_exact`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem coordinate_positive {q : ℝ} (hq : q∈Ioo (0:ℝ) 2) : 0<coordinate q :=
  rpow_pos_of_pos (lt_min hq.1 (by linarith [hq.2])) _

/--
Exact identity `coordinate (2-q)=coordinate q`.

Use: `chebyshev2.Primal.density_moment_cubic` rewrites with this identity to establish the
precise assertion is `(∫ x,(speedData φ hφ).density κ x^((j:ℝ)/2))= ∫ t in (0:ℝ)..1,6*exp (-φ
t)*t^j*(normalizedAmplitude φ κ t)^j`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.density_moment_cubic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coordinate_reflection (q : ℝ) : coordinate (2-q)=coordinate q := by simp only [coordinate,sub_sub_cancel,min_comm]

/--
Continuity of the displayed function: `Continuous (speed φ)`.

Use: `chebyshev2.Primal.reciprocal_integrable` uses this continuity result to establish
integrability on the stated domain: `IntegrableOn (fun q => (speed φ q)⁻¹) (Ioo (0:ℝ) 2)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Primal.coordinate_continuous` with the
arguments shown in the proof.
-/
theorem speed_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) : Continuous (speed φ) :=
  (coordinate_continuous.pow 2).mul (Real.continuous_exp.comp (hφ.comp coordinate_continuous))

/--
The stated quantitative bound `0<speed φ q`.

Use: `chebyshev2.Primal.reciprocal_integrable` rewrites with this bound to establish
integrability on the stated domain: `IntegrableOn (fun q => (speed φ q)⁻¹) (Ioo (0:ℝ) 2)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.ground_exact`.

Proof: Use the identities/estimates `chebyshev2.Primal.coordinate_positive` with the
arguments shown in the proof.
-/
theorem speed_positive (φ : ℝ → ℝ) {q : ℝ} (hq : q∈Ioo (0:ℝ) 2) : 0<speed φ q :=
  mul_pos (sq_pos_of_pos (coordinate_positive hq)) (exp_pos _)

/--
Exact identity `(speed φ q)⁻¹=exp (-φ (coordinate q))*(min q (2-q))^(-(2/3:ℝ))`.

Use: `chebyshev2.Primal.reciprocal_integrable` rewrites with this identity to establish
integrability on the stated domain: `IntegrableOn (fun q => (speed φ q)⁻¹) (Ioo (0:ℝ) 2)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.ground_exact`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem reciprocal_identity (φ : ℝ → ℝ) {q : ℝ} (hq : q∈Ioo (0:ℝ) 2) :
    (speed φ q)⁻¹=exp (-φ (coordinate q))*(min q (2-q))^(-(2/3:ℝ)) := by
  have hu : 0≤min q (2-q) := (lt_min hq.1 (by linarith [hq.2])).le
  rw [speed,mul_inv_rev,← exp_neg,coordinate,← rpow_mul_natCast hu]
  norm_num only [show (1/3:ℝ)*(2:ℕ)=2/3 by norm_num]
  rw [← rpow_neg hu]

/--
Integrability on the stated domain: `IntegrableOn (fun q => (speed φ q)⁻¹) (Ioo (0:ℝ) 2)`.

Use: `chebyshev2.Primal.speedData` uses this integrability result in the displayed
construction of `speedData`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.ground_exact`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem reciprocal_integrable {φ : ℝ → ℝ} (hφ : Continuous φ) :
    IntegrableOn (fun q => (speed φ q)⁻¹) (Ioo (0:ℝ) 2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hp : IntervalIntegrable (fun q : ℝ => q^(-(2/3:ℝ))) volume 0 2 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hr : IntervalIntegrable (fun q : ℝ => (2-q)^(-(2/3:ℝ))) volume 0 2 := by
    simpa using (hp.comp_sub_left 2).symm
  have hi := ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤2)).mp hp).add
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤2)).mp hr)
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous (fun q => exp (-φ (coordinate q))) :=
    Real.continuous_exp.comp ((hφ.comp coordinate_continuous).neg)
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  apply (hi.const_mul (max M 1)).mono'
  · exact ((speed_continuous hφ).continuousOn.inv₀
      (fun q hq => (speed_positive φ hq).ne')).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    have he : exp (-φ (coordinate q))≤max M 1 :=
      (hM (mem_image_of_mem _ ⟨hq.1.le,hq.2.le⟩)).trans (le_max_left _ _)
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (speed_positive φ hq).le),reciprocal_identity φ hq]
    have hm : (min q (2-q))^(-(2/3:ℝ))≤
        q^(-(2/3:ℝ))+(2-q)^(-(2/3:ℝ)) := by
      rcases le_total q (2-q) with h|h
      · rw [min_eq_left h]
        exact le_add_of_nonneg_right (rpow_nonneg (by linarith [hq.2]) _)
      · rw [min_eq_right h]
        exact le_add_of_nonneg_left (rpow_nonneg hq.1.le _)
    exact mul_le_mul he hm (rpow_nonneg (le_min hq.1.le (by linarith [hq.2])) _)
      (le_trans zero_le_one (le_max_right _ _))

/--
Constructs `speedData` of type `SpeedData` by the displayed record fields. Data fields specify
the construction; proof fields discharge its required properties.

Use: `chebyshev2.Primal.actualRightFilter` uses this definition in the displayed
construction of `actualRightFilter`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.ground_exact`.
-/
def speedData (φ : ℝ → ℝ) (hφ : Continuous φ) : SpeedData where
  D := speed φ
  measurable := (speed_continuous hφ).measurable
  positive := fun _ hq => speed_positive φ hq
  B := max (Classical.choose (isCompact_Icc.bddAbove_image
    (speed_continuous hφ).continuousOn)) 1
  bound_positive := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  bound := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    exact (Classical.choose_spec (isCompact_Icc.bddAbove_image
      (speed_continuous hφ).continuousOn) (mem_image_of_mem _ ⟨hq.1.le,hq.2.le⟩)).trans
        (le_max_left _ _)
  reciprocal_integrable := reciprocal_integrable hφ

/--
Exact identity `speed φ (t^3)=t^2*exp (φ t)`.

Use: `chebyshev2.Primal.density_moment_cubic` rewrites with this identity to establish the
precise assertion is `(∫ x,(speedData φ hφ).density κ x^((j:ℝ)/2))= ∫ t in (0:ℝ)..1,6*exp (-φ
t)*t^j*(normalizedAmplitude φ κ t)^j`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.density_moment_cubic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem speed_cubic (φ : ℝ → ℝ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    speed φ (t^3)=t^2*exp (φ t) := by
  have hcube : t^3≤1 := pow_le_one₀ ht.1 ht.2
  have hc : coordinate (t^3)=t := by
    rw [coordinate,min_eq_left (by linarith)]
    simpa only [one_div,show ((3:ℕ):ℝ)=(3:ℝ) from rfl] using
      pow_rpow_inv_natCast ht.1 (by norm_num : (3:ℕ)≠0)
  rw [speed,hc]

/--
Exact identity `chebyshev2.GroundState.groundParameter ((speedData φ hφ).density_integrable
hκ) ((speedData φ hφ).density_nonneg hκ)=κ`.

Use: `chebyshev2.Primal.compactDensity_ground_exact` uses this identity to establish exact
identity `(compactDensity hφ hκ hM).coupling=κ`.

Article: chebyshev2, Theorem 5.1.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density` with the arguments shown in
the proof.
-/
theorem ground_exact {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    chebyshev2.GroundState.groundParameter ((speedData φ hφ).density_integrable hκ)
      ((speedData φ hφ).density_nonneg hκ)=κ :=
  (speedData φ hφ).groundParameter_density hκ

end
end chebyshev2.Primal
