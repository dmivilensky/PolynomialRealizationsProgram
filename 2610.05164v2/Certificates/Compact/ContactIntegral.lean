import «2610.05164v2».Certificates.Compact.ContactProof
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence000
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence001
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence002
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence003
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence004
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence005
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence006
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence007
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence008
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence009
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence010
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence011
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence012
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence013
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence014
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence015
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence016
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence017
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence018
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence019
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence020
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence021
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence022
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence023
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence024
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence025
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence026
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence027
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence028
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence029
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence030
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence031
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence032
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence033
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence034
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence035
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence036
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence037
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence038
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence039
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence040

/-!
Article: 2610.05164v2, Section 4.1.
Contact Integral.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_enclosed` feeds
`«2610.05164v2».Certificates.Compact.ReferenceConstant.constant_enclosed` (constant enclosed).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Certificates.Compact.ContactValues
noncomputable section
open Set MeasureTheory «2610.05164v2».Numerics «2610.05164v2».Numerics.IntegerCertificate
open «2610.05164v2».Certificates «2610.05164v2».Certificates.DualInputs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
/--
Defines `panels` of type `List ContactPolynomial.Panel`. The displayed construction fixes its
component data; its proof fields enforce the listed compatibility properties.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.all_valid` rewrites with this
definition to prove the quantified assertion `∀ p∈panels,ValidPanel
p`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def panels : List ContactPolynomial.Panel := block0++(block1++(block2++(block3++(block4++(block5++(block6++(block7++(block8++(block9++(block10++(block11++(block12++(block13++(block14++(block15++(block16++(block17++(block18++(block19++(block20++(block21++(block22++(block23++(block24++(block25++(block26++(block27++(block28++(block29++(block30++(block31++(block32++(block33++(block34++(block35++(block36++(block37++(block38++(block39++(block40))))))))))))))))))))))))))))))))))))))))
/--
Establishes the uniform, quantified assertion `∀ p∈panels,ValidPanel p`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_error` uses this
assertion to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem all_valid : ∀ p∈panels,ValidPanel p := by
  simp only [panels,List.forall_mem_append]
  exact ⟨validBlock0,⟨validBlock1,⟨validBlock2,⟨validBlock3,⟨validBlock4,⟨validBlock5,⟨validBlock6,⟨validBlock7,⟨validBlock8,⟨validBlock9,⟨validBlock10,⟨validBlock11,⟨validBlock12,⟨validBlock13,⟨validBlock14,⟨validBlock15,⟨validBlock16,⟨validBlock17,⟨validBlock18,⟨validBlock19,⟨validBlock20,⟨validBlock21,⟨validBlock22,⟨validBlock23,⟨validBlock24,⟨validBlock25,⟨validBlock26,⟨validBlock27,⟨validBlock28,⟨validBlock29,⟨validBlock30,⟨validBlock31,⟨validBlock32,⟨validBlock33,⟨validBlock34,⟨validBlock35,⟨validBlock36,⟨validBlock37,⟨validBlock38,⟨validBlock39,validBlock40⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
/--
Defines `quadraturePanels` of type `List Poly.ValuePanel` by `panels.map
(ContactPolynomial.Panel.valuePanel scale epsilon)`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_enclosed` uses this
definition to establish membership in the specified domain/enclosure: `(∫ t in
(0:ℝ)..1,(ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1) t)∈ Icc (contactLower:ℝ) (contactUpper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def quadraturePanels : List Poly.ValuePanel :=
  panels.map (ContactPolynomial.Panel.valuePanel scale epsilon)
/--
The precise assertion is `PartitionFrom 0 1 (quadraturePanels.map Poly.ValuePanel.domain)`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_error` uses this
assertion to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem complete_partition : PartitionFrom 0 1 (quadraturePanels.map Poly.ValuePanel.domain) := by decide +kernel
/--
Exact identity `Poly.totalRadius quadraturePanels=epsilon`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_error` rewrites with
this identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem error_sum : Poly.totalRadius quadraturePanels=epsilon := by decide +kernel

/--
The stated quantitative bound `|(∫ t in (0:ℝ)..1,(ReferenceJetSource.referenceData
reference).directContactCore (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) t)-
(Poly.totalCenter scale quadraturePanels:ℝ)|≤(epsilon:ℝ)`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_enclosed` uses this
identity to establish membership in the specified domain/enclosure: `(∫ t in
(0:ℝ)..1,(ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1) t)∈ Icc (contactLower:ℝ) (contactUpper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Certificates.Compact.ContactValues.error_sum`,
`«2610.05164v2».Calibration.ReferenceData.contactCoreIntegrand_smooth`,
`«2610.05164v2».Calibration.ReferenceData.directContactCore_eq` with the arguments shown in the
proof.
-/
theorem contact_integral_error :
    |(∫ t in (0:ℝ)..1,(ReferenceJetSource.referenceData reference).directContactCore
      (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) t)-
        (Poly.totalCenter scale quadraturePanels:ℝ)|≤(epsilon:ℝ) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Certificates.Compact.ContactValues.error_sum`,
  -- `«2610.05164v2».Calibration.ReferenceData.contactCoreIntegrand_smooth`,
  -- `«2610.05164v2».Calibration.ReferenceData.directContactCore_eq` with the arguments shown
  -- in the proof.
  rw [← error_sum]
  let f := (ReferenceJetSource.referenceData reference).directContactCore
    (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1)
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousOn f (Icc (0:ℝ) 1) := by
    have hs := ((ReferenceJetSource.referenceData reference).contactCoreIntegrand_smooth
      (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1)).continuousOn
    apply hs.congr
    intro t ht
    exact (ReferenceJetSource.referenceData reference).directContactCore_eq
      (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) ht
  have ha : ∀ q∈quadraturePanels,Poly.ValuePanel.Actual scale q f := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact (all_valid p hp).actual
  have h := Poly.integral_error_cover scale quadraturePanels complete_partition f
    (by simpa only [Rat.cast_zero,Rat.cast_one] using hc) ha
  simpa only [Rat.cast_zero,Rat.cast_one] using h

/--
Defines `contactLower` of type `ℚ` by `-729873871/10^12`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_enclosed` uses this
definition to establish membership in the specified domain/enclosure: `(∫ t in
(0:ℝ)..1,(ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1) t)∈ Icc (contactLower:ℝ) (contactUpper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def contactLower : ℚ := -729873871/10^12
/--
Defines `contactUpper` of type `ℚ` by `-729873865/10^12`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_enclosed` uses this
definition to establish membership in the specified domain/enclosure: `(∫ t in
(0:ℝ)..1,(ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1) t)∈ Icc (contactLower:ℝ) (contactUpper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def contactUpper : ℚ := -729873865/10^12

/--
Membership in the specified domain/enclosure: `(∫ t in
(0:ℝ)..1,(ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1) t)∈ Icc (contactLower:ℝ) (contactUpper:ℝ)`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceConstant.constant_enclosed` uses this
identity to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.J 2∈Icc (lower:ℝ) (upper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem contact_integral_enclosed :
    (∫ t in (0:ℝ)..1,(ReferenceJetSource.referenceData reference).directContactCore
      (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) t)∈
        Icc (contactLower:ℝ) (contactUpper:ℝ) := by
  -- Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
  -- against the proved checker; a generator's numerical report is not a premise.
  have h := abs_le.mp contact_integral_error
  have hl : contactLower≤Poly.totalCenter scale quadraturePanels-epsilon := by decide +kernel
  have hu : Poly.totalCenter scale quadraturePanels+epsilon≤contactUpper := by decide +kernel
  have hl' : (contactLower:ℝ)≤(Poly.totalCenter scale quadraturePanels:ℝ)-(epsilon:ℝ) := by exact_mod_cast hl
  have hu' : (Poly.totalCenter scale quadraturePanels:ℝ)+(epsilon:ℝ)≤(contactUpper:ℝ) := by exact_mod_cast hu
  constructor <;> linarith [h.1,h.2]

end
end «2610.05164v2».Certificates.Compact.ContactValues
