import «2610.05164v2».Certificates.DualInputs.ReferenceModel
import «2610.05164v2».Numerics.LogCosh

/-!
Article: 2610.05164v2, Section 4.1.
Kernel-checked spectral target enclosures for the one-determinant base.
Use: `«2610.05164v2».Certificates.DualInputs.TargetObservations.Hsupport_mem` feeds
`«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` (reference base mem).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Certificates.DualInputs.TargetObservations
open «2610.05164v2».Numerics LeanCert.Core
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/--
Defines `kBox` of type `IntervalRat` by `roundHigh (IntervalRat.mul (IntervalRat.singleton
(1/4)) (squareHigh piHigh))`.

Use: `«2610.05164v2».Certificates.DualInputs.TargetObservations.supportBox` uses this
definition in the displayed construction of `supportBox`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def kBox : IntervalRat := roundHigh (IntervalRat.mul (IntervalRat.singleton (1/4)) (squareHigh piHigh))
/--
Defines `supportBox` of type `IntervalRat` by `roundHigh (IntervalRat.mul
(IntervalRat.singleton sigma) kBox)`.

Use: `«2610.05164v2».Certificates.DualInputs.TargetObservations.Hsupport_mem` uses this
definition to establish membership in the specified domain/enclosure: `Real.log (Real.cosh
(Real.sqrt ((sigma:ℝ)*(Real.pi^2/4))))∈Hsupportbounds`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def supportBox : IntervalRat := roundHigh (IntervalRat.mul (IntervalRat.singleton sigma) kBox)

/--
Membership in the specified domain/enclosure: `Real.pi^2/4∈kBox`.

Use: `«2610.05164v2».Certificates.DualInputs.TargetObservations.support_mem` uses this
assertion to establish membership in the specified domain/enclosure:
`(sigma:ℝ)*(Real.pi^2/4)∈supportBox`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.mem_roundHigh`,
`«2610.05164v2».Numerics.mem_squareHigh`, `«2610.05164v2».Numerics.mem_piHigh` with the
arguments shown in the proof.
-/
theorem k_mem : Real.pi^2/4∈kBox := by
  have h := mem_roundHigh (IntervalRat.mem_mul (IntervalRat.mem_singleton (1/4))
    (mem_squareHigh mem_piHigh))
  have he : ((1/4:ℚ):ℝ)*Real.pi^2=Real.pi^2/4 := by norm_num; ring
  rw [he] at h
  exact h
/--
Membership in the specified domain/enclosure: `(sigma:ℝ)*(Real.pi^2/4)∈supportBox`.

Use: `«2610.05164v2».Certificates.DualInputs.TargetObservations.Hsupport_mem` uses this
assertion to establish membership in the specified domain/enclosure: `Real.log (Real.cosh
(Real.sqrt ((sigma:ℝ)*(Real.pi^2/4))))∈Hsupportbounds`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.mem_roundHigh`,
`«2610.05164v2».Certificates.DualInputs.TargetObservations.k_mem` with the arguments shown in
the proof.
-/
theorem support_mem : (sigma:ℝ)*(Real.pi^2/4)∈supportBox :=
  mem_roundHigh (IntervalRat.mem_mul (IntervalRat.mem_singleton sigma) k_mem)
/--
Defines `Hsupportroot` of type `IntervalRat` by `⟨(Rat.mk'
(816853631424691623436756869431012929261527) 10000000000000000000000000000000000000000 (by
decide +kernel) (by decide +kernel)),(Rat.mk' (102106703928086452929594608678876616157691)
1250000000000000000000000000000000000000 (by decide +kernel) (by decide +kernel)),by decide
+kernel⟩`.

Use: `«2610.05164v2».Certificates.DualInputs.TargetObservations.Hsupport_mem` uses this
definition to establish membership in the specified domain/enclosure: `Real.log (Real.cosh
(Real.sqrt ((sigma:ℝ)*(Real.pi^2/4))))∈Hsupportbounds`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Hsupportroot : IntervalRat := ⟨(Rat.mk' (816853631424691623436756869431012929261527) 10000000000000000000000000000000000000000 (by decide +kernel) (by decide +kernel)),(Rat.mk' (102106703928086452929594608678876616157691) 1250000000000000000000000000000000000000 (by decide +kernel) (by decide +kernel)),by decide +kernel⟩
/--
Defines `Hsupportbounds` of type `IntervalRat` by `⟨(Rat.mk' (202480539904773042585646137)
2500000000000000000000000 (by decide +kernel) (by decide +kernel)),(Rat.mk'
(809922159619092170342584549) 10000000000000000000000000 (by decide +kernel) (by decide
+kernel)),by decide +kernel⟩`.

Use: `«2610.05164v2».Certificates.DualInputs.TargetObservations.Hsupport_mem` uses this
definition to establish membership in the specified domain/enclosure: `Real.log (Real.cosh
(Real.sqrt ((sigma:ℝ)*(Real.pi^2/4))))∈Hsupportbounds`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Hsupportbounds : IntervalRat := ⟨(Rat.mk' (202480539904773042585646137) 2500000000000000000000000 (by decide +kernel) (by decide +kernel)),(Rat.mk' (809922159619092170342584549) 10000000000000000000000000 (by decide +kernel) (by decide +kernel)),by decide +kernel⟩
/--
Acceptance/decoding identity for the displayed finite data: `sqrtBracketCheck supportBox
Hsupportroot=true`.

Use: `«2610.05164v2».Certificates.DualInputs.TargetObservations.Hsupport_mem` uses this
identity to establish membership in the specified domain/enclosure: `Real.log (Real.cosh
(Real.sqrt ((sigma:ℝ)*(Real.pi^2/4))))∈Hsupportbounds`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem Hsupportroot_checked : sqrtBracketCheck supportBox Hsupportroot=true := by decide +kernel
/--
Acceptance/decoding identity for the displayed finite data: `logCoshCheck Hsupportroot
Hsupportbounds=true`.

Use: `«2610.05164v2».Certificates.DualInputs.TargetObservations.Hsupport_mem` uses this
identity to establish membership in the specified domain/enclosure: `Real.log (Real.cosh
(Real.sqrt ((sigma:ℝ)*(Real.pi^2/4))))∈Hsupportbounds`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem Hsupportlog_checked : logCoshCheck Hsupportroot Hsupportbounds=true := by decide +kernel
/--
Membership in the specified domain/enclosure: `Real.log (Real.cosh (Real.sqrt
((sigma:ℝ)*(Real.pi^2/4))))∈Hsupportbounds`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` uses this assertion
to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.referenceBase∈result`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.logCoshCheck_sound`,
`«2610.05164v2».Certificates.DualInputs.TargetObservations.Hsupportlog_checked`,
`«2610.05164v2».Numerics.sqrtBracketCheck_sound` with the arguments shown in the proof.
-/
theorem Hsupport_mem : Real.log (Real.cosh (Real.sqrt ((sigma:ℝ)*(Real.pi^2/4))))∈Hsupportbounds :=
  logCoshCheck_sound Hsupportlog_checked (sqrtBracketCheck_sound Hsupportroot_checked support_mem)

end «2610.05164v2».Certificates.DualInputs.TargetObservations
