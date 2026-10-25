import chebyshev2.Calibration.ReferenceProfile
import chebyshev2.Comparison.ProfileSymmetry
import chebyshev2.Comparison.ProfileRegularity

/-!
Article: chebyshev2, Theorem 3.2.
The actual reference density in Theorem 3.2, centered at zero.
Use: `chebyshev2.Calibration.ReferenceData.density_strictMono_left` feeds
`chebyshev2.Calibration.ReferenceData.filter_reflection_strict` (filter reflection strict).
Proof chain: `chebyshev2.Calibration.ReferenceData.calibration_Gamma` — chebyshev2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.Comparison chebyshev2.PrescribedSpeed chebyshev2.GroundState
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData)

/--
Defines `referenceSpeed` of type `SpeedData` by `R.profile.speedData R.k_positive`.

Use: `chebyshev2.Calibration.ReferenceData.coordinate_reflection` uses this definition to
establish exact identity `R.referenceSpeed.q (-x)=2-R.referenceSpeed.q x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def referenceSpeed : SpeedData := R.profile.speedData R.k_positive
/--
Defines `density` of type `ℝ → ℝ` by `R.profile.density R.k_positive`.

Use: `chebyshev2.Calibration.ReferenceData.density_bounded` uses this definition to
establish constructs witnesses with the exact properties `∃ B : ℝ, 0 ≤ B ∧ ∀ x, R.density x ≤
B`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def density : ℝ → ℝ := R.profile.density R.k_positive

/--
Continuity of the displayed function: `Continuous R.density`.

Use: `chebyshev2.Calibration.ReferenceData.contactForcing_continuous` uses this continuity
result to establish continuity of the displayed function: `Continuous (R.contactForcing hσ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.density_continuous` with
the arguments shown in the proof.
-/
theorem density_continuous : Continuous R.density := R.profile.density_continuous R.k_positive

/--
Integrability of the displayed function: `Integrable R.density ∧ (∀ x, 0 ≤ R.density x) ∧
HasCompactSupport R.density ∧ groundParameter (R.referenceSpeed.density_integrable
R.k_positive) (R.referenceSpeed.density_nonneg R.k_positive)=R.k`.

Use: `chebyshev2.Calibration.ReferenceData.contact_limit` uses this integrability result to
establish convergence along the specified source filter to the specified limit: `Tendsto
(R.contact hσ) atTop (𝓝 2)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.density_properties` with
the arguments shown in the proof.
-/
theorem density_properties : Integrable R.density ∧ (∀ x, 0 ≤ R.density x) ∧
    HasCompactSupport R.density ∧
    groundParameter (R.referenceSpeed.density_integrable R.k_positive)
      (R.referenceSpeed.density_nonneg R.k_positive)=R.k :=
  R.profile.density_properties R.k_positive

/--
Constructs witnesses with the exact properties `∃ B : ℝ, 0 ≤ B ∧ ∀ x, R.density x ≤ B`.

Use: `chebyshev2.Calibration.ReferenceData.density_energy_integrable` uses this bound to
establish integrability of the displayed function: `Integrable (fun x => (sqrt (R.density
x))^3)`.

Article: chebyshev2, Proposition 5 via
`chebyshev2.Calibration.ReferenceData.selfConsistent_attainment`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.density_bounded` with
the arguments shown in the proof.
-/
theorem density_bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, R.density x ≤ B :=
  R.profile.density_bounded R.k_positive

/--
Exact identity `R.density x=(R.amplitude (R.referenceSpeed.q x))^2`.

Use: `chebyshev2.Calibration.ReferenceData.density_strictMono_left` rewrites with this
identity to establish `StrictMonoOn R.density (Icc (R.referenceSpeed.X
0) 0)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.density_formula` with
the arguments shown in the proof.
-/
theorem density_formula (x : ℝ) : R.density x=(R.amplitude (R.referenceSpeed.q x))^2 :=
  R.profile.density_formula R.k_positive x

/--
The precise assertion is `R.referenceSpeed.X (2-q)= -R.referenceSpeed.X q`.

Use: `chebyshev2.Calibration.ReferenceData.J_contact_half_integral` uses this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.X_reflection`,
`chebyshev2.Calibration.ReferenceData.amplitude_reflection` with the arguments shown in the
proof.
-/
theorem X_reflection (q : ℝ) : R.referenceSpeed.X (2-q)= -R.referenceSpeed.X q :=
  R.profile.X_reflection R.k_positive (fun q _ => R.amplitude_reflection q) q

/--
Exact identity `R.referenceSpeed.q (-x)=2-R.referenceSpeed.q x`.

Use: `chebyshev2.Calibration.ReferenceData.J_contact_half_integral` rewrites with this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.coordinate_reflection`,
`chebyshev2.Calibration.ReferenceData.amplitude_reflection` with the arguments shown in the
proof.
-/
theorem coordinate_reflection (x : ℝ) : R.referenceSpeed.q (-x)=2-R.referenceSpeed.q x :=
  R.profile.coordinate_reflection R.k_positive (fun q _ => R.amplitude_reflection q) x

/--
Exact identity `R.density (-x)=R.density x`.

Use: `chebyshev2.Calibration.ReferenceData.contactFunctional_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt
(R.contactFunctional hσ q) (R.contactDerivative hσ q x) x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.density_reflection`,
`chebyshev2.Calibration.ReferenceData.amplitude_reflection` with the arguments shown in the
proof.
-/
theorem density_reflection (x : ℝ) : R.density (-x)=R.density x :=
  R.profile.density_reflection R.k_positive (fun q _ => R.amplitude_reflection q) x

/--
Exact identity `R.referenceSpeed.X 1=0`.

Use: `chebyshev2.Calibration.ReferenceData.coordinate_zero` uses this identity to establish
exact identity `R.referenceSpeed.q 0=1`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem X_one : R.referenceSpeed.X 1=0 := by simp [SpeedData.X]

/--
Exact identity `R.referenceSpeed.q 0=1`.

Use: `chebyshev2.Calibration.ReferenceData.density_strictMono_left` uses this identity to
establish the precise assertion is `StrictMonoOn R.density (Icc (R.referenceSpeed.X 0) 0)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.X_one`,
`chebyshev2.PrescribedSpeed.SpeedData.q_X` with the arguments shown in the proof.
-/
theorem coordinate_zero : R.referenceSpeed.q 0=1 := by simpa only [R.X_one] using R.referenceSpeed.q_X (q := 1) (by norm_num)

/--
The precise assertion is `StrictMonoOn R.referenceSpeed.q (Icc (R.referenceSpeed.X 0)
(R.referenceSpeed.X 2))`.

Use: `chebyshev2.Calibration.ReferenceData.density_strictMono_left` uses this assertion to
establish the precise assertion is `StrictMonoOn R.density (Icc (R.referenceSpeed.X 0) 0)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem coordinate_strictMono : StrictMonoOn R.referenceSpeed.q
    (Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2)) := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  intro x hx y hy hxy
  by_contra h
  have hq : R.referenceSpeed.q y ≤ R.referenceSpeed.q x := not_lt.mp h
  have hX := R.referenceSpeed.X_strictMono.monotoneOn
    (R.referenceSpeed.q_mem y) (R.referenceSpeed.q_mem x) hq
  rw [R.referenceSpeed.X_q hy,R.referenceSpeed.X_q hx] at hX
  linarith

/--
The precise assertion is `StrictMonoOn R.amplitude (Icc (0:ℝ) 1)`.

Use: `chebyshev2.Calibration.ReferenceData.density_strictMono_left` uses this assertion to
establish the precise assertion is `StrictMonoOn R.density (Icc (R.referenceSpeed.X 0) 0)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.root_strictMono`,
`chebyshev2.Calibration.ReferenceData.Q_mem` with the arguments shown in the proof.
-/
theorem amplitude_strictMono_left : StrictMonoOn R.amplitude (Icc (0:ℝ) 1) := by
  intro q hq t ht hqt
  apply R.root_strictMono (Q_mem ⟨hq.1,by linarith [hq.2]⟩)
    (Q_mem ⟨ht.1,by linarith [ht.2]⟩)
  have h1 : 0 < (t-q)*(2-q-t) := mul_pos (sub_pos.mpr hqt) (by linarith [ht.2])
  unfold Q
  nlinarith

/--
The precise assertion is `StrictMonoOn R.density (Icc (R.referenceSpeed.X 0) 0)`.

Use: `chebyshev2.Calibration.ReferenceData.density_mono_left` uses this assertion to
establish monotonicity in increasing order: `MonotoneOn R.density (Iic (0:ℝ))`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.X_one`,
`chebyshev2.PrescribedSpeed.SpeedData.X_strictMono`,
`chebyshev2.Calibration.ReferenceData.coordinate_strictMono` with the arguments shown in
the proof.
-/
theorem density_strictMono_left : StrictMonoOn R.density (Icc (R.referenceSpeed.X 0) 0) := by
  -- Use the identities/estimates `chebyshev2.Calibration.ReferenceData.X_one`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.X_strictMono`,
  -- `chebyshev2.Calibration.ReferenceData.coordinate_strictMono` with the arguments shown
  -- in the proof.
  have hr : 0 ≤ R.referenceSpeed.X 2 := by
    simpa only [R.X_one] using R.referenceSpeed.X_strictMono.monotoneOn
      (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 2) (by norm_num) (by norm_num)
  intro x hx y hy hxy
  have hx' : x ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2) := ⟨hx.1,hx.2.trans hr⟩
  have hy' : y ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2) := ⟨hy.1,hy.2.trans hr⟩
  have hq := R.coordinate_strictMono hx' hy' hxy
  have hl : R.referenceSpeed.q y ≤ 1 := by
    have h0 : (0:ℝ) ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2) := by
      refine ⟨?_,hr⟩
      simpa only [R.X_one] using R.referenceSpeed.X_strictMono.monotoneOn
        (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 2)
        (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 2) (by norm_num : (0:ℝ) ≤ 1)
    have h := R.coordinate_strictMono.monotoneOn hy' h0 hy.2
    simpa only [R.coordinate_zero] using h
  have hν := R.amplitude_strictMono_left ⟨(R.referenceSpeed.q_mem x).1,hq.le.trans hl⟩
    ⟨(R.referenceSpeed.q_mem y).1,hl⟩ hq
  rw [R.density_formula,R.density_formula]
  exact pow_lt_pow_left₀ hν (R.amplitude_nonneg (R.referenceSpeed.q_mem x)) (by norm_num : 2 ≠ 0)

end
end chebyshev2.Calibration.ReferenceData
