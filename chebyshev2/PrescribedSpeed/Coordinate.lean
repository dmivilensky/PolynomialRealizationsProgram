import chebyshev2.GroundState.Article

/-!
Article: chebyshev2, Theorem 3.2.
The quantitative expansion estimate that makes the inverse Lipschitz, proved for the full
measurable-speed hypotheses, including endpoint intervals.
Use: `chebyshev2.PrescribedSpeed.SpeedData.X_endpoint_order` feeds
`chebyshev2.Calibration.ReferenceData.calibration_global_strict_minimum` (calibration global
strict minimum).
Proof chain: `chebyshev2.Calibration.ReferenceData.contact_strictMono` — chebyshev2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.PrescribedSpeed
noncomputable section
open chebyshev2.GroundState Set MeasureTheory Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Theorem 5.1's measurable speed. The bound is an essential L-infinity bound, so no unstated
pointwise regularity or continuity is required. Values outside (0,2) are irrelevant and can
always be supplied by measurable extension.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_derivative_ae` uses this record of data and
proof obligations to prove the eventual or almost-everywhere assertion
`∀ᵐ q, HasDerivAt S.X (S.reciprocal q) q`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.
-/
structure SpeedData where
  /-- Measurable speed in the ground coordinate q on (0,2). -/
  D : ℝ → ℝ
  /-- Measurability needed to integrate its reciprocal and construct the coordinate change. -/
  measurable : Measurable D
  /-- Strict positivity in the interior, so the reciprocal coordinate speed is defined. -/
  positive : ∀ q ∈ Ioo (0:ℝ) 2, 0 < D q
  /-- Finite positive upper bound for the speed. -/
  B : ℝ
  /-- The upper bound is strictly positive. -/
  bound_positive : 0 < B
  /-- The speed is bounded above almost everywhere on its physical domain. -/
  bound : ∀ᵐ q ∂volume.restrict (Ioo (0:ℝ) 2), D q ≤ B
  /-- Finite coordinate length follows from integrability of 1/D on (0,2). -/
  reciprocal_integrable : IntegrableOn (fun q => (D q)⁻¹) (Ioo (0:ℝ) 2)

namespace SpeedData
variable (S : SpeedData)

/--
Defines `reciprocal` of type `ℝ → ℝ` by `(Ioo (0:ℝ) 2).indicator (fun q => (S.D q)⁻¹)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_expansion` rewrites with this definition to
establish the stated quantitative bound `(b-a)/S.B ≤ S.X b-S.X a`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.
-/
def reciprocal : ℝ → ℝ := (Ioo (0:ℝ) 2).indicator (fun q => (S.D q)⁻¹)
/--
Defines `X` of type `ℝ` by `∫ t in (1:ℝ)..q, S.reciprocal t`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_strictMono` uses this definition to establish
the precise assertion is `StrictMonoOn S.X (Icc (0:ℝ) 2)`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.
-/
def X (q : ℝ) : ℝ := ∫ t in (1:ℝ)..q, S.reciprocal t

/--
Integrability of the displayed function: `Integrable S.reciprocal`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_derivative_ae` uses this integrability result
to prove the eventual or almost-everywhere assertion `∀ᵐ q, HasDerivAt
S.X (S.reciprocal q) q`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem reciprocal_integrable_global : Integrable S.reciprocal :=
  S.reciprocal_integrable.integrable_indicator measurableSet_Ioo

/--
The stated quantitative bound `0 ≤ S.reciprocal q`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.coordinateMeasure_apply` uses this bound to
establish exact identity `S.coordinateMeasure A=ENNReal.ofReal (∫ t in A, S.reciprocal t)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem reciprocal_nonneg (q : ℝ) : 0 ≤ S.reciprocal q := by
  by_cases hq : q ∈ Ioo (0:ℝ) 2
  · rw [reciprocal,indicator_of_mem hq]
    exact inv_nonneg.mpr (S.positive q hq).le
  · simp [reciprocal,hq]

/--
Exact identity `S.X b-S.X a=∫ t in a..b, S.reciprocal t`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_expansion` rewrites with this identity to
establish the stated quantitative bound `(b-a)/S.B ≤ S.X b-S.X a`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.reciprocal_integrable_global` with the arguments
shown in the proof.
-/
theorem X_difference (a b : ℝ) : S.X b-S.X a=∫ t in a..b, S.reciprocal t := by
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (S.reciprocal_integrable_global.intervalIntegrable (a := 1) (b := a))
    (S.reciprocal_integrable_global.intervalIntegrable (a := a) (b := b))
  dsimp [X]
  linarith

/--
Exact identity `S.X=exponentialPrimitive 0 S.reciprocal (-∫ t in (0:ℝ)..1, S.reciprocal t)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_derivative_ae` rewrites with this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ q, HasDerivAt S.X
(S.reciprocal q) q`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem X_primitive : S.X=exponentialPrimitive 0 S.reciprocal (-∫ t in (0:ℝ)..1, S.reciprocal t) := by
  funext q
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (S.reciprocal_integrable_global.intervalIntegrable (a := 0) (b := 1))
    (S.reciprocal_integrable_global.intervalIntegrable (a := 1) (b := q))
  simp only [exponentialPrimitive,zero_mul,neg_zero,exp_zero,one_mul]
  dsimp [X]
  linarith

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval S.X a b`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_continuous` uses this assertion to establish
continuity of the displayed function: `Continuous S.X`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_primitive`,
`chebyshev2.GroundState.exponentialPrimitive_locallyAC`,
`chebyshev2.PrescribedSpeed.SpeedData.reciprocal_integrable_global` with the arguments
shown in the proof.
-/
theorem X_locallyAC (a b : ℝ) : AbsolutelyContinuousOnInterval S.X a b := by
  rw [S.X_primitive]
  exact exponentialPrimitive_locallyAC S.reciprocal_integrable_global.locallyIntegrable _ _ _ _

/--
Continuity of the displayed function: `Continuous S.X`.

Use: `chebyshev2.Calibration.Data.comparisonA0_integrable` uses this continuity result to
establish integrability of the displayed function: `Integrable (fun x => C.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
x))^2))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.locallyAC_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.X_locallyAC` with the arguments shown in the proof.
-/
theorem X_continuous : Continuous S.X := locallyAC_continuous S.X_locallyAC

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ q, HasDerivAt S.X
(S.reciprocal q) q`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_derivative_inside` uses this assertion to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume.restrict
(Ioo (S.X 0) (S.X 2)), HasDerivAt S.q (S.D (S.q x)) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_primitive`,
`chebyshev2.GroundState.exponentialPrimitive_derivative_ae`,
`chebyshev2.PrescribedSpeed.SpeedData.reciprocal_integrable_global` with the arguments
shown in the proof.
-/
theorem X_derivative_ae : ∀ᵐ q, HasDerivAt S.X (S.reciprocal q) q := by
  rw [S.X_primitive]
  simpa only [zero_mul,zero_add] using
    exponentialPrimitive_derivative_ae S.reciprocal_integrable_global.locallyIntegrable 0 _

/--
The quantitative expansion estimate that makes the inverse Lipschitz, proved for the full
measurable-speed hypotheses, including endpoint intervals.

The stated quantitative bound `(b-a)/S.B ≤ S.X b-S.X a`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_strictMono` uses this bound to establish the
precise assertion is `StrictMonoOn S.X (Icc (0:ℝ) 2)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem X_expansion {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 2) (hb : b ∈ Icc (0:ℝ) 2) (hab : a ≤ b) :
    (b-a)/S.B ≤ S.X b-S.X a := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [S.X_difference]
  have hzero : ∀ᵐ q ∂volume, q ≠ (0:ℝ) := by simp [ae_iff]
  have htwo : ∀ᵐ q ∂volume, q ≠ (2:ℝ) := by simp [ae_iff]
  have hbound : ∀ᵐ q ∂volume, q ∈ Ioo (0:ℝ) 2 → S.D q ≤ S.B := ae_imp_of_ae_restrict S.bound
  have hle : (fun _ : ℝ => S.B⁻¹) ≤ᵐ[volume.restrict (Icc a b)] S.reciprocal := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hzero,
      ae_restrict_of_ae htwo,ae_restrict_of_ae hbound] with q hq hq0 hq2 hqb
    have hqin : q ∈ Ioo (0:ℝ) 2 := ⟨lt_of_le_of_ne (ha.1.trans hq.1) hq0.symm,
      lt_of_le_of_ne (hq.2.trans hb.2) hq2⟩
    change S.B⁻¹ ≤ S.reciprocal q
    rw [reciprocal,indicator_of_mem hqin]
    exact inv_le_inv₀ S.bound_positive (S.positive q hqin) |>.mpr (hqb hqin)
  have h := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => S.B⁻¹) volume a b)
    S.reciprocal_integrable_global.intervalIntegrable hle
  rw [intervalIntegral.integral_const,smul_eq_mul] at h
  simpa only [div_eq_mul_inv] using h

/--
The precise assertion is `StrictMonoOn S.X (Icc (0:ℝ) 2)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_endpoint_order` uses this assertion to
establish the stated quantitative bound `S.X 0 < S.X 2`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_expansion` with
the arguments shown in the proof.
-/
theorem X_strictMono : StrictMonoOn S.X (Icc (0:ℝ) 2) := by
  intro a ha b hb hab
  have h := S.X_expansion ha hb hab.le
  have hp : 0 < (b-a)/S.B := div_pos (sub_pos.mpr hab) S.bound_positive
  linarith

/--
The stated quantitative bound `S.X 0 < S.X 2`.

Use: `chebyshev2.Calibration.ReferenceData.J_contact_integral` uses this bound to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_strictMono`
with the arguments shown in the proof.
-/
theorem X_endpoint_order : S.X 0 < S.X 2 :=
  S.X_strictMono (by norm_num) (by norm_num) (by norm_num)

end SpeedData
end
end chebyshev2.PrescribedSpeed
