import «2610.05164v2».DualCertificate.ComparisonFilters
import «2610.05164v2».Comparison.DefectBounds
import «2610.05164v2».Calculus.QuotientContinuity

/-!
Article: 2610.05164v2, Lemma 16.
Lemma 16(ii): joint continuity of the actual normalized comparison defects, including the singular
endpoint, and of the normalized left states.
Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.leftU_range` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.U_range` (U range).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate.NormalizedCalibration
noncomputable section
open Set Filter Real «2610.05164v2».Calibration «2610.05164v2».Calculus
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable (N : «2610.05164v2».DualCertificate.NormalizedCalibration) {s : ℝ}
/--
Defines `ParameterDomain` of type `` by `Ioi (0:ℝ) × Icc (0:ℝ) 1`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_joint_continuous` uses this
definition to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.defect p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
abbrev ParameterDomain := Ioi (0:ℝ) × Icc (0:ℝ) 1

/--
Defines `cubeMap` of type `Ioi (0:ℝ) × Icc (0:ℝ) 2` by `(p.1,⟨(p.2:ℝ)^3,⟨(cube_mem
p.2.property).1,(cube_mem p.2.property).2.trans (by norm_num)⟩⟩)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_joint_bound` uses this
definition to prove the bound `0≤N.defect p.1.property s p.2 ∧ N.defect
p.1.property s p.2≤N.calibration.defectConstant p.1 s*(p.2:ℝ)^7`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def cubeMap (p : ParameterDomain) : Ioi (0:ℝ) × Icc (0:ℝ) 2 :=
  (p.1,⟨(p.2:ℝ)^3,⟨(cube_mem p.2.property).1,(cube_mem p.2.property).2.trans (by norm_num)⟩⟩)

/--
Continuity of the displayed function: `Continuous cubeMap`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_joint_continuous` uses this
continuity result to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.defect p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem cubeMap_continuous : Continuous cubeMap := by
  apply continuous_fst.prodMk
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_snd).pow 3

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.defect
p.1.property s p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defectQuotient_joint_continuous`
uses this continuity result to establish continuity of the displayed function: `Continuous (fun
p : ParameterDomain => N.defectQuotient p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.leftFilter_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.cubeMap_continuous` with the arguments
shown in the proof.
-/
theorem defect_joint_continuous (hs : 0<s) :
    Continuous (fun p : ParameterDomain => N.defect p.1.property s p.2) := by
  -- Establish continuity hκc before using the function at limits or in calculus arguments.
  have hκc : Continuous (fun p : ParameterDomain => (p.1:ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  -- Establish continuity htc before using the function at limits or in calculus arguments.
  have htc : Continuous (fun p : ParameterDomain => (p.2:ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  -- Establish continuity hf before using the function at limits or in calculus arguments.
  have hf : Continuous (fun p : ParameterDomain => N.filter p.1.property s p.2) := by
    convert! (N.calibration.leftFilter_joint_continuous hs.le).comp cubeMap_continuous using 1
  exact (htc.pow 3).sub ((hκc.div_const s).mul hf)

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.linearDefect
p.1.property p.2)`.

Use:
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefectQuotient_joint_continuous`
uses this continuity result to establish continuity of the displayed function: `Continuous (fun
p : ParameterDomain => N.linearDefectQuotient p.1.property p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.leftLinear_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.cubeMap_continuous` with the arguments
shown in the proof.
-/
theorem linearDefect_joint_continuous :
    Continuous (fun p : ParameterDomain => N.linearDefect p.1.property p.2) :=
  ((continuous_subtype_val.comp continuous_snd).pow 3).sub
    (N.calibration.leftLinear_joint_continuous.comp cubeMap_continuous)

/--
The stated quantitative bound `0≤N.defect p.1.property s p.2 ∧ N.defect p.1.property s
p.2≤N.calibration.defectConstant p.1 s*(p.2:ℝ)^7`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defectQuotient_joint_continuous`
uses this bound to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.defectQuotient p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_bounds`,
`«2610.05164v2».Calibration.Data.leftDefect_endpoint_bound`,
`«2610.05164v2».Calculus.cube_rpow_seven_thirds` with the arguments shown in the proof.
-/
theorem defect_joint_bound (hs : 0<s) (p : ParameterDomain) :
    0≤N.defect p.1.property s p.2 ∧
      N.defect p.1.property s p.2≤N.calibration.defectConstant p.1 s*(p.2:ℝ)^7 := by
  refine ⟨(N.defect_bounds p.1.property hs p.2.property).1,?_⟩
  have h := N.calibration.leftDefect_endpoint_bound p.1.property hs (cubeMap p).2.property
  dsimp only [cubeMap] at h
  rw [cube_rpow_seven_thirds p.2.property.1] at h
  exact h

/--
The stated quantitative bound `0≤N.linearDefect p.1.property p.2 ∧ N.linearDefect p.1.property
p.2≤N.calibration.defectConstant p.1 0*(p.2:ℝ)^7`.

Use:
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefectQuotient_joint_continuous`
uses this bound to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.linearDefectQuotient p.1.property p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_bounds`,
`«2610.05164v2».Calibration.Data.leftLinearDefect_endpoint_bound`,
`«2610.05164v2».Calculus.cube_rpow_seven_thirds` with the arguments shown in the proof.
-/
theorem linearDefect_joint_bound (p : ParameterDomain) :
    0≤N.linearDefect p.1.property p.2 ∧
      N.linearDefect p.1.property p.2≤N.calibration.defectConstant p.1 0*(p.2:ℝ)^7 := by
  refine ⟨(N.linearDefect_bounds p.1.property p.2.property).1,?_⟩
  have h := N.calibration.leftLinearDefect_endpoint_bound p.1.property (cubeMap p).2.property
  dsimp only [cubeMap] at h
  rw [cube_rpow_seven_thirds p.2.property.1] at h
  exact h

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.defectQuotient
p.1.property s p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.leftU_joint_continuous` uses this
continuity result to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.leftU p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.continuous_cubic_quotient`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_joint_continuous`,
`«2610.05164v2».Calibration.Data.defectConstant_continuousOn` with the arguments shown in the
proof.
-/
theorem defectQuotient_joint_continuous (hs : 0<s) :
    Continuous (fun p : ParameterDomain => N.defectQuotient p.1.property s p.2) := by
  apply continuous_cubic_quotient _ (fun κ : Ioi (0:ℝ) => N.calibration.defectConstant κ s)
    (N.defect_joint_continuous hs)
    (N.calibration.defectConstant_continuousOn s).domRestrict
  exact N.defect_joint_bound hs

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain =>
N.linearDefectQuotient p.1.property p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.leftTheta_joint_continuous` uses
this continuity result to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.leftTheta p.1.property p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.continuous_cubic_quotient`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_joint_continuous`,
`«2610.05164v2».Calibration.Data.defectConstant_continuousOn` with the arguments shown in the
proof.
-/
theorem linearDefectQuotient_joint_continuous :
    Continuous (fun p : ParameterDomain => N.linearDefectQuotient p.1.property p.2) := by
  apply continuous_cubic_quotient _ (fun κ : Ioi (0:ℝ) => N.calibration.defectConstant κ 0)
    N.linearDefect_joint_continuous
    (N.calibration.defectConstant_continuousOn 0).domRestrict
  exact N.linearDefect_joint_bound

/--
The normalized left nonlinear state U, with its actual endpoint value.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.leftU_range` uses this definition to
establish membership in the specified domain/enclosure: `N.leftU hκ s t∈Icc (0:ℝ) 1`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def leftU {κ : ℝ} (hκ : 0<κ) (s t : ℝ) : ℝ := 1-N.defectQuotient hκ s t

/--
The normalized linear defect theta, with its actual endpoint value.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.leftTheta_range` uses this
definition to establish membership in the specified domain/enclosure: `N.leftTheta hκ t∈Icc
(0:ℝ) 1`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def leftTheta {κ : ℝ} (hκ : 0<κ) (t : ℝ) : ℝ := N.linearDefectQuotient hκ t

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.leftU
p.1.property s p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.R_joint_continuous` uses this
continuity result to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.R side p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.defectQuotient_joint_continuous` with the
arguments shown in the proof.
-/
theorem leftU_joint_continuous (hs : 0<s) :
    Continuous (fun p : ParameterDomain => N.leftU p.1.property s p.2) :=
  continuous_const.sub (N.defectQuotient_joint_continuous hs)

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.leftTheta
p.1.property p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero_joint_continuous` uses this
continuity result to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.Rzero side p.1.property p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefectQuotient_joint_continuous`
with the arguments shown in the proof.
-/
theorem leftTheta_joint_continuous :
    Continuous (fun p : ParameterDomain => N.leftTheta p.1.property p.2) :=
  N.linearDefectQuotient_joint_continuous

/--
Membership in the specified domain/enclosure: `N.leftU hκ s t∈Icc (0:ℝ) 1`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.R_range` uses this assertion to
establish membership in the specified domain/enclosure: `N.R side hκ s t∈Icc (0:ℝ) (s/κ)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_bounds` with the arguments shown
in the proof.
-/
theorem leftU_range {κ t : ℝ} (hκ : 0<κ) (hs : 0<s) (ht : t∈Icc (0:ℝ) 1) :
    N.leftU hκ s t∈Icc (0:ℝ) 1 := by
  -- Use the identities/estimates
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_bounds` with the arguments
  -- shown in the proof.
  unfold leftU defectQuotient
  split_ifs with hz
  · norm_num
  · have ht3 : 0<t^3 := pow_pos (lt_of_le_of_ne ht.1 (Ne.symm hz)) _
    have h := N.defect_bounds hκ hs ht
    exact ⟨sub_nonneg.mpr ((div_le_one ht3).mpr h.2),
      sub_le_self _ (div_nonneg h.1 ht3.le)⟩

/--
Membership in the specified domain/enclosure: `N.leftTheta hκ t∈Icc (0:ℝ) 1`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero_range` uses this assertion to
establish membership in the specified domain/enclosure: `N.Rzero side hκ t∈Icc (0:ℝ) 1`.

Article: 2610.05164v2, Lemma 16.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_bounds` with the arguments
shown in the proof.
-/
theorem leftTheta_range {κ t : ℝ} (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) :
    N.leftTheta hκ t∈Icc (0:ℝ) 1 := by
  unfold leftTheta linearDefectQuotient
  split_ifs with hz
  · norm_num
  · have ht3 : 0<t^3 := pow_pos (lt_of_le_of_ne ht.1 (Ne.symm hz)) _
    have h := N.linearDefect_bounds hκ ht
    exact ⟨div_nonneg h.1 ht3.le,(div_le_one ht3).mpr h.2⟩

end
end «2610.05164v2».DualCertificate.NormalizedCalibration
