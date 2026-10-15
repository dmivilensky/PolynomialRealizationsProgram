import «2610.05164v2».Certificates.Compact.ContactIntegral
import «2610.05164v2».Certificates.Compact.AmplitudeProof
import «2610.05164v2».Numerics.ReferenceContactQuadrature

/-!
Article: 2610.05164v2, Section 4.1.
Reference Constant.
Use: `«2610.05164v2».Certificates.Compact.ReferenceConstant.constant_enclosed` feeds
`«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` (reference base mem).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Certificates.Compact.ReferenceConstant
noncomputable section
open Set MeasureTheory «2610.05164v2».Numerics «2610.05164v2».Numerics.IntegerCertificate LeanCert.Core
open «2610.05164v2».Certificates.DualInputs
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/--
Defines `endpointBox` of type `IntervalRat` by `⟨8674975219/10^13,8674975221/10^13,by decide
+kernel⟩`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceConstant.endpoint_mem` uses this definition
to establish membership in the specified domain/enclosure: `(ReferenceJetSource.referenceData
reference).normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1)
0∈endpointBox`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def endpointBox : IntervalRat := ⟨8674975219/10^13,8674975221/10^13,by decide +kernel⟩
/--
Defines `tailBox` of type `IntervalRat` by `((ReferenceCoreSource.vacuumExpression sigma
24).enclose (fun _ => endpointBox)).getD (IntervalRat.singleton 0)`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceConstant.constant_enclosed` uses this
definition to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.J 2∈Icc (lower:ℝ) (upper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def tailBox : IntervalRat :=
  ((ReferenceCoreSource.vacuumExpression sigma 24).enclose (fun _ => endpointBox)).getD
    (IntervalRat.singleton 0)
/--
Acceptance/decoding identity for the displayed finite data:
`(ReferenceCoreSource.vacuumExpression sigma 24).enclose (fun _ => endpointBox)= some tailBox`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceConstant.tail_mem` uses this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem tail_checked :
    (ReferenceCoreSource.vacuumExpression sigma 24).enclose (fun _ => endpointBox)=
      some tailBox := by decide +kernel

/--
Membership in the specified domain/enclosure: `(ReferenceJetSource.referenceData
reference).normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1)
0∈endpointBox`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceConstant.tail_mem` uses this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem endpoint_mem :
    (ReferenceJetSource.referenceData reference).normalizedReflectedFilter
      (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) 0∈endpointBox := by
  -- Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
  -- against the proved checker; a generator's numerical report is not a premise.
  have h := abs_le.mp ReferenceTrajectory.full_trajectory.2.2
  let c := ResidualCell.lastValue ReferenceResiduals.scale
    (ResidualCell.lastValue ReferenceResiduals.scale 0 ReferenceTrajectory.leftRows)
      ReferenceTrajectory.rightRows
  have hl : endpointBox.lo≤c-ReferenceTrajectory.rightBound := by decide +kernel
  have hu : c+ReferenceTrajectory.rightBound≤endpointBox.hi := by decide +kernel
  have hl' : (endpointBox.lo:ℝ)≤(c:ℝ)-(ReferenceTrajectory.rightBound:ℝ) := by exact_mod_cast hl
  have hu' : (c:ℝ)+(ReferenceTrajectory.rightBound:ℝ)≤(endpointBox.hi:ℝ) := by exact_mod_cast hu
  have he : ReferenceJetSource.rightFilter reference reference_signs.1 2=
      (ReferenceJetSource.referenceData reference).normalizedReflectedFilter
        (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) 0 := by
    simp only [ReferenceJetSource.rightFilter,show (2:ℝ)-2=0 by norm_num]
  rw [he] at h
  constructor <;> linarith [h.1,h.2]

/--
Membership in the specified domain/enclosure:
`«2610.05164v2».Calibration.ReferenceData.vacuumSquare (sigma:ℝ)
((ReferenceJetSource.referenceData reference).normalizedReflectedFilter (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1) 0)∈tailBox`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceConstant.constant_enclosed` uses this
identity to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.J 2∈Icc (lower:ℝ) (upper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceCoreSource.vacuumExpression_enclose`,
`«2610.05164v2».Certificates.Compact.ReferenceConstant.tail_checked`,
`«2610.05164v2».Certificates.Compact.ReferenceConstant.endpoint_mem` with the arguments shown
in the proof.
-/
theorem tail_mem :
    «2610.05164v2».Calibration.ReferenceData.vacuumSquare (sigma:ℝ)
      ((ReferenceJetSource.referenceData reference).normalizedReflectedFilter
        (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) 0)∈tailBox :=
  ReferenceCoreSource.vacuumExpression_enclose tail_checked endpoint_mem

/--
Defines `lower` of type `ℚ` by `-729982411/10^12`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceConstant.constant_enclosed` uses this
definition to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.J 2∈Icc (lower:ℝ) (upper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def lower : ℚ := -729982411/10^12
/--
Defines `upper` of type `ℚ` by `-729982403/10^12`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceConstant.constant_enclosed` uses this
definition to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.J 2∈Icc (lower:ℝ) (upper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def upper : ℚ := -729982403/10^12

/--
Membership in the specified domain/enclosure: `AmplitudeValues.calibration.J 2∈Icc (lower:ℝ)
(upper:ℝ)`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` uses this assertion
to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.referenceBase∈result`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem constant_enclosed : AmplitudeValues.calibration.J 2∈Icc (lower:ℝ) (upper:ℝ) := by
  -- Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
  -- against the proved checker; a generator's numerical report is not a premise.
  have h := ContactValues.contact_integral_enclosed
  have ht := tail_mem
  have he : AmplitudeValues.calibration.J 2=
      (∫ t in (0:ℝ)..1,(ReferenceJetSource.referenceData reference).directContactCore
        (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) t)-
      «2610.05164v2».Calibration.ReferenceData.vacuumSquare (sigma:ℝ)
        ((ReferenceJetSource.referenceData reference).normalizedReflectedFilter
          (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) 0) := by
    rw [AmplitudeValues.calibration,
      «2610.05164v2».Calibration.ReferenceData.calibration_constant_direct]
    rw [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]
  have hl : lower≤ContactValues.contactLower-tailBox.hi := by decide +kernel
  have hu : ContactValues.contactUpper-tailBox.lo≤upper := by decide +kernel
  have hl' : (lower:ℝ)≤(ContactValues.contactLower:ℝ)-(tailBox.hi:ℝ) := by exact_mod_cast hl
  have hu' : (ContactValues.contactUpper:ℝ)-(tailBox.lo:ℝ)≤(upper:ℝ) := by exact_mod_cast hu
  rw [he]
  constructor <;> linarith [h.1,h.2,ht.1,ht.2]

end
end «2610.05164v2».Certificates.Compact.ReferenceConstant
