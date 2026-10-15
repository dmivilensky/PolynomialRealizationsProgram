import «2610.05164v2».Numerics.ValueQuadrature
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence000
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence001
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence002
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence003
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence004
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence005
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence006
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence007
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence008
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence009
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence010
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence011
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence012
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence013
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence014
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence015
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence016
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence017
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence018
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence019
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence020
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence021
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence022
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence023
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence024
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence025
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence026
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence027
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence028
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence029
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence030
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence031
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence032
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence033
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence034
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence035
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence036
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence037
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence038
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence039
import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Correspondence040

/-!
Article: 2610.05164v2, Section 4.1.
Amplitude Integral.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_enclosed` feeds
`«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` (reference base mem).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace «2610.05164v2».Certificates.Compact.AmplitudeValues
open «2610.05164v2».Numerics.IntegerCertificate
noncomputable section
open Set MeasureTheory «2610.05164v2».Certificates
/--
Defines `panels` of type `List AmplitudePolynomial.Panel`. The displayed construction fixes its
component data; its proof fields enforce the listed compatibility properties.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.all_valid` rewrites with this
definition to prove the quantified assertion `∀ p∈panels,ValidPanel
p`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def panels : List AmplitudePolynomial.Panel := block0++(block1++(block2++(block3++(block4++(block5++(block6++(block7++(block8++(block9++(block10++(block11++(block12++(block13++(block14++(block15++(block16++(block17++(block18++(block19++(block20++(block21++(block22++(block23++(block24++(block25++(block26++(block27++(block28++(block29++(block30++(block31++(block32++(block33++(block34++(block35++(block36++(block37++(block38++(block39++(block40))))))))))))))))))))))))))))))))))))))))
/--
Establishes the uniform, quantified assertion `∀ p∈panels,ValidPanel p`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_error` uses this
assertion to prove the bound `|(∫ q in (0:ℝ)..2,calibration.amplitude
(Real.pi^2/4) q)- (Poly.totalCenter scale quadraturePanels:ℝ)|≤(epsilon:ℝ)`.

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
(AmplitudePolynomial.Panel.valuePanel scale epsilon)`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_enclosed` uses
this definition to establish membership in the specified domain/enclosure: `(∫ q in
(0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)∈ Icc (amplitudeLower:ℝ) (amplitudeUpper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def quadraturePanels : List Poly.ValuePanel :=
  panels.map (AmplitudePolynomial.Panel.valuePanel scale epsilon)
/--
The precise assertion is `PartitionFrom 0 1 (quadraturePanels.map Poly.ValuePanel.domain)`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_error` uses this
assertion to prove the bound `|(∫ q in (0:ℝ)..2,calibration.amplitude
(Real.pi^2/4) q)- (Poly.totalCenter scale quadraturePanels:ℝ)|≤(epsilon:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem complete_partition : PartitionFrom 0 1 (quadraturePanels.map Poly.ValuePanel.domain) := by decide +kernel
/--
Exact identity `Poly.totalRadius quadraturePanels=epsilon`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_error` rewrites
with this identity to prove the bound `|(∫ q in
(0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)- (Poly.totalCenter scale
quadraturePanels:ℝ)|≤(epsilon:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem error_sum : Poly.totalRadius quadraturePanels=epsilon := by decide +kernel

/--
The stated quantitative bound `|(∫ q in (0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)-
(Poly.totalCenter scale quadraturePanels:ℝ)|≤(epsilon:ℝ)`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_enclosed` uses
this bound to establish membership in the specified domain/enclosure: `(∫ q in
(0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)∈ Icc (amplitudeLower:ℝ) (amplitudeUpper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Certificates.Compact.AmplitudeValues.integral_cubic`,
`«2610.05164v2».Certificates.Compact.AmplitudeValues.error_sum`,
`«2610.05164v2».Certificates.Compact.AmplitudeValues.ValidPanel.actual` with the arguments
shown in the proof.
-/
theorem amplitude_integral_error :
    |(∫ q in (0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)-
      (Poly.totalCenter scale quadraturePanels:ℝ)|≤(epsilon:ℝ) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Certificates.Compact.AmplitudeValues.integral_cubic`,
  -- `«2610.05164v2».Certificates.Compact.AmplitudeValues.error_sum`,
  -- `«2610.05164v2».Certificates.Compact.AmplitudeValues.ValidPanel.actual` with the arguments
  -- shown in the proof.
  rw [integral_cubic,← error_sum]
  have ha : ∀ q∈quadraturePanels,Poly.ValuePanel.Actual scale q integrand := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact (all_valid p hp).actual
  have h := Poly.integral_error_cover scale quadraturePanels complete_partition integrand
    (by simpa only [Rat.cast_zero,Rat.cast_one] using integrand_continuous) ha
  simpa only [Rat.cast_zero,Rat.cast_one] using h

/--
Defines `amplitudeLower` of type `ℚ` by `22704304581/10^10`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_enclosed` uses
this definition to establish membership in the specified domain/enclosure: `(∫ q in
(0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)∈ Icc (amplitudeLower:ℝ) (amplitudeUpper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def amplitudeLower : ℚ := 22704304581/10^10
/--
Defines `amplitudeUpper` of type `ℚ` by `22704304586/10^10`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_enclosed` uses
this definition to establish membership in the specified domain/enclosure: `(∫ q in
(0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)∈ Icc (amplitudeLower:ℝ) (amplitudeUpper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def amplitudeUpper : ℚ := 22704304586/10^10

/--
Membership in the specified domain/enclosure: `(∫ q in (0:ℝ)..2,calibration.amplitude
(Real.pi^2/4) q)∈ Icc (amplitudeLower:ℝ) (amplitudeUpper:ℝ)`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` uses this assertion
to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.referenceBase∈result`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem amplitude_integral_enclosed :
    (∫ q in (0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)∈
      Icc (amplitudeLower:ℝ) (amplitudeUpper:ℝ) := by
  -- Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
  -- against the proved checker; a generator's numerical report is not a premise.
  have h := abs_le.mp amplitude_integral_error
  have hl : amplitudeLower≤Poly.totalCenter scale quadraturePanels-epsilon := by decide +kernel
  have hu : Poly.totalCenter scale quadraturePanels+epsilon≤amplitudeUpper := by decide +kernel
  have hl' : (amplitudeLower:ℝ)≤(Poly.totalCenter scale quadraturePanels:ℝ)-(epsilon:ℝ) := by exact_mod_cast hl
  have hu' : (Poly.totalCenter scale quadraturePanels:ℝ)+(epsilon:ℝ)≤(amplitudeUpper:ℝ) := by exact_mod_cast hu
  constructor <;> linarith [h.1,h.2]

end
end «2610.05164v2».Certificates.Compact.AmplitudeValues
