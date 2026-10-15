import «2610.05164v2».Certificates.Compact.ReferenceConstant
import «2610.05164v2».Certificates.Compact.AmplitudeIntegral
import «2610.05164v2».Certificates.DualInputs.TargetObservations
import «2610.05164v2».DualCertificate.PrecisionBudget

/-!
Article: 2610.05164v2, Section 4.1.
Reference Base.
Result: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` supplies the
stated article conclusion.
-/
namespace «2610.05164v2».Certificates.Compact.ReferenceBase
noncomputable section
open Set «2610.05164v2».Numerics LeanCert.Core
open «2610.05164v2».Certificates.DualInputs
open scoped IntervalExpr
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/--
Defines `expression` of type `IntervalExpr 4` by `-(.literal base)+2*(.literal base)/(.variable
0)+ (3/((.literal 2)*(.variable 0)))*(.variable 1)- (.literal omega)*(.variable 2)- (.literal
omega)*((.variable 0)/(.literal sigma)- (2/(.literal (sigma^2)))*(.variable 3))`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` rewrites with this
definition to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.referenceBase∈result`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def expression : IntervalExpr 4 :=
  -(.literal base)+2*(.literal base)/(.variable 0)+
    (3/((.literal 2)*(.variable 0)))*(.variable 1)-
      (.literal omega)*(.variable 2)-
      (.literal omega)*((.variable 0)/(.literal sigma)-
        (2/(.literal (sigma^2)))*(.variable 3))

/--
Defines `boxes` of type `Fin 4 → IntervalRat` by `![TargetObservations.kBox,
⟨AmplitudeValues.amplitudeLower,AmplitudeValues.amplitudeUpper,by decide +kernel⟩,
⟨ReferenceConstant.lower,ReferenceConstant.upper,by decide +kernel⟩,
TargetObservations.Hsupportbounds]`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` uses this
definition to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.referenceBase∈result`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def boxes : Fin 4 → IntervalRat := ![TargetObservations.kBox,
  ⟨AmplitudeValues.amplitudeLower,AmplitudeValues.amplitudeUpper,by decide +kernel⟩,
  ⟨ReferenceConstant.lower,ReferenceConstant.upper,by decide +kernel⟩,
  TargetObservations.Hsupportbounds]

/--
Defines `result` of type `IntervalRat` by `(expression.enclose boxes).getD
(IntervalRat.singleton 0)`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_lower` uses this
definition to prove the bound
`(«2610.05164v2».DualCertificate.oneDetLower:ℝ)≤AmplitudeValues.calibration.referenceBase`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def result : IntervalRat := (expression.enclose boxes).getD (IntervalRat.singleton 0)
/--
Acceptance/decoding identity for the displayed finite data: `expression.enclose boxes=some
result`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` uses this identity
to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.referenceBase∈result`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem checked : expression.enclose boxes=some result := by decide +kernel
/--
The stated quantitative bound `«2610.05164v2».DualCertificate.oneDetLower≤result.lo`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_lower` uses this bound
to prove the bound
`(«2610.05164v2».DualCertificate.oneDetLower:ℝ)≤AmplitudeValues.calibration.referenceBase`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem lower_checked : «2610.05164v2».DualCertificate.oneDetLower≤result.lo := by decide +kernel

/--
Membership in the specified domain/enclosure:
`AmplitudeValues.calibration.referenceBase∈result`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_enclosed` uses this
assertion to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.referenceBase∈printedBox`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem reference_base_mem : AmplitudeValues.calibration.referenceBase∈result := by
  -- Check each member of the finite index type; no case is omitted.
  let values : Fin 4 → ℝ := ![Real.pi^2/4,
    (∫ q in (0:ℝ)..2,AmplitudeValues.calibration.amplitude (Real.pi^2/4) q),
    AmplitudeValues.calibration.J 2,
    Real.log (Real.cosh (Real.sqrt ((sigma:ℝ)*(Real.pi^2/4))))]
  have hm : ∀ i,values i∈boxes i := by
    intro i
    fin_cases i
    · exact TargetObservations.k_mem
    · exact AmplitudeValues.amplitude_integral_enclosed
    · exact ReferenceConstant.constant_enclosed
    · exact TargetObservations.Hsupport_mem
  have hv := IntervalExpr.enclose_sound expression boxes checked hm
  have he : expression.value values=AmplitudeValues.calibration.referenceBase := by
    simp only [expression,IntervalExpr.value_neg,IntervalExpr.value_add,
      IntervalExpr.value_sub,IntervalExpr.value_mul,IntervalExpr.value_div,
      IntervalExpr.value_literal,IntervalExpr.value_variable,IntervalExpr.value_nat,
      values,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      «2610.05164v2».Calibration.Data.referenceBase,«2610.05164v2».Calibration.Data.base]
    change -(base:ℝ)+2*(base:ℝ)/(Real.pi^2/4)+
      (3/(2*(Real.pi^2/4)))*(∫ q in (0:ℝ)..2,AmplitudeValues.calibration.amplitude (Real.pi^2/4) q)-
      (omega:ℝ)*AmplitudeValues.calibration.J 2-
      (omega:ℝ)*((Real.pi^2/4)/(sigma:ℝ)-(2/((sigma^2:ℚ):ℝ))*
        Real.log (Real.cosh (Real.sqrt ((sigma:ℝ)*(Real.pi^2/4)))))=_
    push_cast
    rfl
  rw [he] at hv
  exact hv

/--
The stated quantitative bound
`(«2610.05164v2».DualCertificate.oneDetLower:ℝ)≤AmplitudeValues.calibration.referenceBase`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` uses this
bound to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Certificates.Compact.ReferenceBase.lower_checked`,
`«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` with the arguments shown
in the proof.
-/
theorem reference_base_lower :
    («2610.05164v2».DualCertificate.oneDetLower:ℝ)≤AmplitudeValues.calibration.referenceBase :=
  (show («2610.05164v2».DualCertificate.oneDetLower:ℝ)≤(result.lo:ℝ) by
    exact_mod_cast lower_checked).trans reference_base_mem.1

/--
Defines `printedBox` of type `IntervalRat` by `⟨114266366/10^8,114266369/10^8,by decide
+kernel⟩`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.printed_box_checked` uses this
definition to establish acceptance/decoding identity for the displayed finite data:
`intervalSubsetCheck result printedBox=true`.

Article: 2610.05164v2, Section 4.1 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_enclosed`.
-/
def printedBox : IntervalRat := ⟨114266366/10^8,114266369/10^8,by decide +kernel⟩
/--
Acceptance/decoding identity for the displayed finite data: `intervalSubsetCheck result
printedBox=true`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_enclosed` uses this
identity to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.referenceBase∈printedBox`.

Article: 2610.05164v2, Section 4.1 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_enclosed`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem printed_box_checked : intervalSubsetCheck result printedBox=true := by decide +kernel
/--
Membership in the specified domain/enclosure:
`AmplitudeValues.calibration.referenceBase∈printedBox`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.intervalSubsetCheck_sound`,
`«2610.05164v2».Certificates.Compact.ReferenceBase.printed_box_checked`,
`«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_mem` with the arguments shown
in the proof.
-/
theorem reference_base_enclosed : AmplitudeValues.calibration.referenceBase∈printedBox :=
  intervalSubsetCheck_sound printed_box_checked reference_base_mem

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ n in Filter.atTop,∀ I :
«2606.16671v2».SpectralInterval,∀ J : «2610.05164v2».Fiber (n+1), 2*Real.sqrt
(«2610.05164v2».SineJacobi.chain (n+1)).normalizedEnergy<
(«2610.05164v2».DualCertificate.oneDetGainFactor:ℝ)* ((«2610.05164v2».recurrenceEquiv I (n+1)
(by omega)) J).val.normalizedGain I`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.one_det_uniform_of_value`,
`«2610.05164v2».Certificates.Compact.ReferenceBase.reference_base_lower` with the arguments
shown in the proof.
-/
theorem uniform_gain_improvement :
    ∀ᶠ n in Filter.atTop,∀ I : «2606.16671v2».SpectralInterval,∀ J : «2610.05164v2».Fiber (n+1),
      2*Real.sqrt («2610.05164v2».SineJacobi.chain (n+1)).normalizedEnergy<
        («2610.05164v2».DualCertificate.oneDetGainFactor:ℝ)*
          ((«2610.05164v2».recurrenceEquiv I (n+1) (by omega)) J).val.normalizedGain I :=
  «2610.05164v2».DualCertificate.one_det_uniform_of_value _ reference_base_lower

end
end «2610.05164v2».Certificates.Compact.ReferenceBase
