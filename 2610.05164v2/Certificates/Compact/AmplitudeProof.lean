import «2610.05164v2».Certificates.Compact.ContactProof
import «2610.05164v2».Certificates.Compact.AmplitudeShared
import «2610.05164v2».Numerics.AmplitudeActual
import «2610.05164v2».Calibration.AmplitudeQuadrature

/-!
Article: 2610.05164v2, Section 4.1.
Amplitude Proof.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.integral_cubic` feeds
`«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_error` (amplitude integral
error).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Certificates.Compact.AmplitudeValues
noncomputable section
open Set «2610.05164v2».Numerics «2610.05164v2».Numerics.IntegerCertificate
open «2610.05164v2».Certificates.DualInputs
set_option autoImplicit false

/--
Defines `calibration` of type `«2610.05164v2».Calibration.Data` by
`(ReferenceJetSource.referenceData reference).calibration (σ := (sigma:ℝ)) (b := (base:ℝ)) (ω
:= (omega:ℝ)) (by exact_mod_cast reference_signs.1) (by exact_mod_cast reference_signs.2.1) (by
exact_mod_cast reference_signs.2.2)`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.integral_cubic` uses this definition
to establish `(∫ q in (0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)=
∫ t in (0:ℝ)..1,integrand t`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def calibration : «2610.05164v2».Calibration.Data :=
  (ReferenceJetSource.referenceData reference).calibration
    (σ := (sigma:ℝ)) (b := (base:ℝ)) (ω := (omega:ℝ))
    (by exact_mod_cast reference_signs.1)
    (by exact_mod_cast reference_signs.2.1)
    (by exact_mod_cast reference_signs.2.2)

/--
Defines `integrand` of type `ℝ` by `6*t^2*calibration.amplitude (Real.pi^2/4) (t^3)`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.ValidPanel.actual` uses this
definition to establish `(p.valuePanel scale epsilon).Actual scale
integrand`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def integrand (t : ℝ) : ℝ := 6*t^2*calibration.amplitude (Real.pi^2/4) (t^3)

/--
Defines `ValidPanel` of type `Prop` by `AmplitudePolynomial.check scale ops epsilon p=true ∧
ContactValues.ValidPanel p.base`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.ValidPanel.actual` uses this
definition to establish `(p.valuePanel scale epsilon).Actual scale
integrand`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def ValidPanel (p : AmplitudePolynomial.Panel) : Prop :=
  AmplitudePolynomial.check scale ops epsilon p=true ∧ ContactValues.ValidPanel p.base

/--
The precise assertion is `(p.valuePanel scale epsilon).Actual scale integrand`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_error` uses this
assertion to prove the bound `|(∫ q in (0:ℝ)..2,calibration.amplitude
(Real.pi^2/4) q)- (Poly.totalCenter scale quadraturePanels:ℝ)|≤(epsilon:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem ValidPanel.actual {p : AmplitudePolynomial.Panel} (hp : ValidPanel p) :
    (p.valuePanel scale epsilon).Actual scale integrand := by
  exact p.actual_of_inputs (by decide +kernel) hp.2.1
    (ReferenceJetSource.referenceData reference) reference_signs.1
    reference_signs.2.1 reference_signs.2.2 shapeK shapeD shapeE shapeQ hp.1
    (fun _ hx => hp.2.inputs hx)

/--
Continuity on the stated domain: `ContinuousOn integrand (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_error` uses this
continuity result to prove the bound `|(∫ q in
(0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)- (Poly.totalCenter scale
quadraturePanels:ℝ)|≤(epsilon:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.amplitude_continuousOn_fixed` with the arguments shown in the
proof.
-/
theorem integrand_continuous : ContinuousOn integrand (Icc (0:ℝ) 1) := by
  have hc := calibration.amplitude_continuousOn_fixed
    (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num) : 0<Real.pi^2/4)
  exact ((continuous_const.mul (continuous_id.pow 2)).continuousOn).mul
    (hc.comp (continuous_pow 3).continuousOn (by
      intro t ht
      exact ⟨pow_nonneg ht.1 3,(pow_le_one₀ ht.1 ht.2).trans (by norm_num)⟩))

/--
The precise assertion is `(∫ q in (0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)= ∫ t in
(0:ℝ)..1,integrand t`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_error` rewrites
with this identity to prove the bound `|(∫ q in
(0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)- (Poly.totalCenter scale
quadraturePanels:ℝ)|≤(epsilon:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.amplitude_integral_cubic`,
`«2610.05164v2».Calibration.ReferenceData.calibration_Gamma_reflection` with the arguments
shown in the proof.
-/
theorem integral_cubic :
    (∫ q in (0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)=
      ∫ t in (0:ℝ)..1,integrand t := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.amplitude_integral_cubic`,
  -- `«2610.05164v2».Calibration.ReferenceData.calibration_Gamma_reflection` with the arguments
  -- shown in the proof.
  apply calibration.amplitude_integral_cubic
    (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num))
  intro q hq
  exact (ReferenceJetSource.referenceData reference).calibration_Gamma_reflection
    (by exact_mod_cast reference_signs.1) (by exact_mod_cast reference_signs.2.1)
    (by exact_mod_cast reference_signs.2.2) q hq

end
end «2610.05164v2».Certificates.Compact.AmplitudeValues
