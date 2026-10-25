import chebyshev2.PrescribedSpeed.Derivative
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: chebyshev2, Theorem 5.1.
The Riccati data are constructed from the actual inverse, rather than postulated as a certificate.
Use: `chebyshev2.PrescribedSpeed.SpeedData.riccati` feeds
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density` (Theorem 5.1's prescribed
parameter is the actual spectral/variational ground parameter, rather than just a parameter of a
differential equation).
Proof chain: `chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density` — chebyshev2,
Theorem 5.1; General measurable speed gives a density with the prescribed ground parameter.
-/
namespace chebyshev2.PrescribedSpeed
noncomputable section
open chebyshev2.GroundState Set MeasureTheory Real
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SpeedData
variable (S : SpeedData)

/--
Defines `Q` of type `ℝ` by `S.q x*(2-S.q x)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.Q_le_one` uses this definition to establish the
stated quantitative bound `S.Q x ≤ 1`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.
-/
def Q (x : ℝ) : ℝ := S.q x*(2-S.q x)

/--
The stated quantitative bound `0 ≤ S.Q x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` uses this bound to establish the
stated quantitative bound `0 ≤ S.density κ x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_mem` with the
arguments shown in the proof.
-/
theorem Q_nonneg (x : ℝ) : 0 ≤ S.Q x :=
  mul_nonneg (S.q_mem x).1 (sub_nonneg.mpr (S.q_mem x).2)

/--
The stated quantitative bound `S.Q x ≤ 1`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_bound` uses this bound to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume, S.density κ x ≤
(S.B+1)/κ`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Q_le_one (x : ℝ) : S.Q x ≤ 1 := by dsimp [Q]; nlinarith [sq_nonneg (S.q x-1)]

/--
Continuity of the displayed function: `Continuous S.Q`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_measurable` uses this continuity result
to establish measurability of the displayed map: `Measurable (S.density κ)`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`
with the arguments shown in the proof.
-/
theorem Q_continuous : Continuous S.Q := S.q_continuous.mul (continuous_const.sub S.q_continuous)

/--
Exact identity `S.Q x=0`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_identity` rewrites with this identity to
establish exact identity `κ*S.density κ x=S.speed x+S.Q x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_zero_left`,
`chebyshev2.PrescribedSpeed.SpeedData.q_two_right` with the arguments shown in the proof.
-/
theorem Q_zero_outside {x : ℝ} (hx : x ∉ Ioo (S.X 0) (S.X 2)) : S.Q x=0 := by
  rcases le_or_gt x (S.X 0) with h | h
  · simp only [Q,S.q_zero_left h,zero_mul]
  · have hr : S.X 2 ≤ x := not_lt.mp (fun hc => hx ⟨h,hc⟩)
    simp only [Q,S.q_two_right hr,sub_self,mul_zero]

/--
The density in Theorem 5.1, with zero endpoint values chosen as an L1 representative.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_measurable` uses this definition to
establish measurability of the displayed map: `Measurable (S.density κ)`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.
-/
def density (κ x : ℝ) : ℝ :=
  (Ioo (S.X 0) (S.X 2)).indicator (fun x => (S.D (S.q x)+S.Q x)/κ) x

/--
Measurability of the displayed map: `Measurable (S.density κ)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_integrable` uses this measurability
result to establish integrability of the displayed function: `Integrable (S.density κ)`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.Q_continuous` with the arguments shown in the proof.
-/
theorem density_measurable (κ : ℝ) : Measurable (S.density κ) :=
  (((S.measurable.comp S.q_continuous.measurable).add S.Q_continuous.measurable).div_const κ).indicator
    measurableSet_Ioo

/--
Exact identity `S.density κ x=0`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_compact_support` uses this identity to
establish the precise assertion is `HasCompactSupport (S.density κ)`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem density_zero_outside (κ : ℝ) {x : ℝ} (hx : x ∉ Ioo (S.X 0) (S.X 2)) :
    S.density κ x=0 := indicator_of_notMem hx _

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume.restrict (Icc (S.X
0) (S.X 2)), S.density κ x=(S.D (S.q x)+S.q x*(2-S.q x))/κ`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_moment` uses this identity to establish
the precise assertion is `(∫ x, S.density κ x^r)= ∫ t in Ioo (0:ℝ) 2, ((S.D t+t*(2-t))/κ)^r/S.D
t`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.density_moment_cubic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem density_formula_ae (κ : ℝ) :
    ∀ᵐ x ∂volume.restrict (Icc (S.X 0) (S.X 2)),
      S.density κ x=(S.D (S.q x)+S.q x*(2-S.q x))/κ := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hl : ∀ᵐ x ∂volume, x ≠ S.X 0 := by simp [ae_iff]
  have hr : ∀ᵐ x ∂volume, x ≠ S.X 2 := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hl,
    ae_restrict_of_ae hr] with x hx hl hr
  have hi : x ∈ Ioo (S.X 0) (S.X 2) :=
    ⟨lt_of_le_of_ne hx.1 hl.symm,lt_of_le_of_ne hx.2 hr⟩
  rw [density,indicator_of_mem hi]
  rfl

/--
The stated quantitative bound `0 ≤ S.density κ x`.

Use: `chebyshev2.Calibration.Data.comparisonDensity_properties` uses this bound to
establish the integrability result stated in that declaration.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem density_nonneg {κ : ℝ} (hκ : 0 < κ) (x : ℝ) : 0 ≤ S.density κ x := by
  by_cases hx : x ∈ Ioo (S.X 0) (S.X 2)
  · rw [density,indicator_of_mem hx]
    exact div_nonneg (add_nonneg (S.positive _ (S.q_mem_Ioo hx)).le (S.Q_nonneg x)) hκ.le
  · rw [S.density_zero_outside κ hx]

/--
The stated quantitative bound `0 < S.density κ x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_nonzero` uses this bound to establish
the precise assertion is `¬ S.density κ =ᵐ[volume] 0`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_mem_Ioo`,
`chebyshev2.PrescribedSpeed.SpeedData.Q_nonneg` with the arguments shown in the proof.
-/
theorem density_positive {κ x : ℝ} (hκ : 0 < κ) (hx : x ∈ Ioo (S.X 0) (S.X 2)) :
    0 < S.density κ x := by
  rw [density,indicator_of_mem hx]
  exact div_pos (add_pos_of_pos_of_nonneg (S.positive _ (S.q_mem_Ioo hx)) (S.Q_nonneg x)) hκ

/--
Exact identity `κ*S.density κ x=S.speed x+S.Q x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_bound` rewrites with this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume,
S.density κ x ≤ (S.B+1)/κ`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Clear the denominators using the available nonzero hypotheses,
then verify the remaining algebraic identity.
-/
theorem density_identity {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    κ*S.density κ x=S.speed x+S.Q x := by
  by_cases hx : x ∈ Ioo (S.X 0) (S.X 2)
  · rw [density,indicator_of_mem hx,speed,indicator_of_mem hx]
    field_simp
  · rw [S.density_zero_outside κ hx,speed,indicator_of_notMem hx,S.Q_zero_outside hx]
    ring

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume, S.density κ x ≤
(S.B+1)/κ`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (S.density κ)`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem density_bound {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ x ∂volume, S.density κ x ≤ (S.B+1)/κ := by
  filter_upwards [S.speed_bound] with x hx
  apply (le_div_iff₀ hκ).mpr
  rw [mul_comm,S.density_identity hκ]
  exact add_le_add hx (S.Q_le_one x)

/--
The precise assertion is `MemLp (S.density κ) ∞ volume`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 5.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem density_memLp_top {κ : ℝ} (hκ : 0 < κ) : MemLp (S.density κ) ∞ volume := by
  apply memLp_top_of_bound (S.density_measurable κ).aestronglyMeasurable ((S.B+1)/κ)
  filter_upwards [S.density_bound hκ] with x hx
  rwa [Real.norm_of_nonneg (S.density_nonneg hκ x)]

/--
The precise assertion is `HasCompactSupport (S.density κ)`.

Use: `chebyshev2.Calibration.Data.comparisonDensity_properties` uses this assertion to
establish the integrability result stated in that declaration.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem density_compact_support (κ : ℝ) : HasCompactSupport (S.density κ) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (S.X 0) (S.X 2)) isCompact_Icc
  intro x hx
  by_contra hn
  have hi : x ∉ Ioo (S.X 0) (S.X 2) := fun h => hn ⟨h.1.le,h.2.le⟩
  exact hx (S.density_zero_outside κ hi)

/--
Integrability of the displayed function: `Integrable (S.density κ)`.

Use: `chebyshev2.Calibration.Data.comparisonDensity_properties` uses this integrability
result to establish the integrability result stated in that declaration.

Article: chebyshev2, Theorem 5.1.

Proof: Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then
prove the asserted relation at an arbitrary point in that intersection. Prove equality of
functions by evaluating both sides at an arbitrary argument.
-/
theorem density_integrable {κ : ℝ} (hκ : 0 < κ) : Integrable (S.density κ) := by
  -- Establish hc as the integrability justification for the later integral estimates or
  -- changes of order.
  have hc : IntegrableOn (fun _ : ℝ => (S.B+1)/κ) (Ioo (S.X 0) (S.X 2)) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : IntegrableOn (S.density κ) (Ioo (S.X 0) (S.X 2)) := by
    apply hc.mono' (S.density_measurable κ).aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae (S.density_bound hκ)] with x hx
    rwa [Real.norm_of_nonneg (S.density_nonneg hκ x)]
  have he : (Ioo (S.X 0) (S.X 2)).indicator (S.density κ)=S.density κ := by
    funext x
    by_cases hx : x ∈ Ioo (S.X 0) (S.X 2)
    · exact indicator_of_mem hx _
    · simp only [indicator_of_notMem hx,S.density_zero_outside κ hx]
  rw [← he]
  exact hi.integrable_indicator measurableSet_Ioo

/--
The precise assertion is `¬ S.density κ =ᵐ[volume] 0`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density` uses this identity to
establish exact identity `groundParameter (S.density_integrable hκ) (S.density_nonneg hκ)=κ`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_positive`,
`chebyshev2.PrescribedSpeed.SpeedData.X_endpoint_order` with the arguments shown in the
proof.
-/
theorem density_nonzero {κ : ℝ} (hκ : 0 < κ) : ¬ S.density κ =ᵐ[volume] 0 := by
  intro hz
  have hnull : volume (Ioo (S.X 0) (S.X 2))=0 := by
    apply measure_mono_null (t := {x | S.density κ x ≠ 0}) _ ((ae_iff.mp hz))
    intro x hx
    exact ne_of_gt (S.density_positive hκ hx)
  rw [Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hnull
  linarith [S.X_endpoint_order]

/--
The Riccati data are constructed from the actual inverse, rather than postulated as a
certificate.

Use: `chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density` uses this definition to
establish exact identity `groundParameter (S.density_integrable hκ) (S.density_nonneg hκ)=κ`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.
-/
def riccati {κ : ℝ} (hκ : 0 < κ) : RiccatiData (S.density κ) κ where
  a := fun x => 1-S.q x
  bound := fun x => by rw [abs_le]; constructor <;> linarith [(S.q_mem x).1,(S.q_mem x).2]
  locally_ac := fun a b => by
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1:ℝ)) a b :=
      (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => (1:ℝ)) (uIcc a b)).absolutelyContinuousOnInterval
    exact hc.sub (S.q_locallyAC a b)
  derivative_ae := by
    filter_upwards [S.q_derivative_ae] with x hx
    have hd := (hasDerivAt_const x (1:ℝ)).sub hx
    convert hd using 1
    rw [S.density_identity hκ]
    dsimp [Q]
    ring

end SpeedData
end
end chebyshev2.PrescribedSpeed
