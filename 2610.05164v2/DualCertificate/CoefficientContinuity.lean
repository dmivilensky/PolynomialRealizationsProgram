import «2610.05164v2».DualCertificate.NormalizedCertificate

/-!
Article: 2610.05164v2, Theorem 3.6.
Joint continuity of the actual closed-box coefficients in Lemma 16(ii), including t=0.
Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateL_joint_continuous` feeds
`«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` (face Criterion continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate.NormalizedCalibration
noncomputable section
open Set «2610.05164v2».Residual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (N : «2610.05164v2».DualCertificate.NormalizedCalibration) (P : PolynomialPotential)

/--
Defines `CoefficientBox` of type `` by `Ioi (0:ℝ) × Icc (0:ℝ) 1 × Icc (0:ℝ) 1 × Icc (0:ℝ) 1 ×
Icc (0:ℝ) 1`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.centeredC_joint_continuous` uses
this definition to establish continuity of the displayed function: `Continuous (fun p :
CoefficientBox => P.centeredC N side p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
abbrev CoefficientBox := Ioi (0:ℝ) × Icc (0:ℝ) 1 × Icc (0:ℝ) 1 × Icc (0:ℝ) 1 × Icc (0:ℝ) 1

/--
Defines `parameterProjection` of type `ParameterDomain` by `(p.1,p.2.1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.centeredC_joint_continuous` uses
this definition to establish continuity of the displayed function: `Continuous (fun p :
CoefficientBox => P.centeredC N side p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
def parameterProjection (p : CoefficientBox) : ParameterDomain := (p.1,p.2.1)

/--
Continuity of the displayed function: `Continuous parameterProjection`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.centeredC_joint_continuous` uses
this continuity result to establish continuity of the displayed function: `Continuous (fun p :
CoefficientBox => P.centeredC N side p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem parameterProjection_continuous : Continuous parameterProjection :=
  continuous_fst.prodMk continuous_snd.fst

 /--
Continuity of the displayed function: `Continuous (fun p : CoefficientBox => P.centeredC N side
p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Use: `«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.normalizedC_smooth`,
`«2610.05164v2».DualCertificate.PolynomialPotential.comparisonC_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.parameterProjection_continuous` with the
arguments shown in the proof.
-/
theorem centeredC_joint_continuous (side : Side) : Continuous (fun p : CoefficientBox =>
    P.centeredC N side p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hm : Continuous (fun p : CoefficientBox =>
      ((p.1:ℝ),((p.2.1:ℝ),((0:ℝ),(p.2.2.1:ℝ),(p.2.2.2.1:ℝ),(p.2.2.2.2:ℝ))))) := by fun_prop
  have hc := (P.normalizedC_smooth N side).continuousOn.comp_continuous hm
    (fun p => ⟨p.1.property,p.2.1.property,mem_univ _⟩)
  exact hc.sub ((P.comparisonC_joint_continuous N side).comp parameterProjection_continuous)

 /--
Continuity of the displayed function: `Continuous (fun p : CoefficientBox => N.certificateB P
side p.1.property ξ₀ ξ₁ χ τ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Use: `«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.speed_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.R_joint_continuous` with the arguments
shown in the proof.
-/
theorem certificateB_joint_continuous (side : Side) (ξ₀ ξ₁ χ τ : ℝ) :
    Continuous (fun p : CoefficientBox =>
      N.certificateB P side p.1.property ξ₀ ξ₁ χ τ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  -- Establish continuity hk before using the function at limits or in calculus arguments.
  have hk : Continuous (fun p : CoefficientBox => (p.1:ℝ)) := by fun_prop
  -- Establish continuity ht before using the function at limits or in calculus arguments.
  have ht : Continuous (fun p : CoefficientBox => (p.2.1:ℝ)) := by fun_prop
  -- Establish continuity hu before using the function at limits or in calculus arguments.
  have hu : Continuous (fun p : CoefficientBox => (p.2.2.1:ℝ)) := by fun_prop
  -- Establish continuity hv before using the function at limits or in calculus arguments.
  have hv : Continuous (fun p : CoefficientBox => (p.2.2.2.1:ℝ)) := by fun_prop
  -- Establish continuity hθ before using the function at limits or in calculus arguments.
  have hθ : Continuous (fun p : CoefficientBox => (p.2.2.2.2:ℝ)) := by fun_prop
  have hm := hk.prodMk ht
  have hr := N.root_smooth.continuousOn.comp_continuous hm (fun p => ⟨p.1.property,p.2.1.property⟩)
  have hd := N.speed_smooth.continuousOn.comp_continuous hm (fun p => ⟨p.1.property,p.2.1.property⟩)
  -- Establish continuity hq before using the function at limits or in calculus arguments.
  have hq : Continuous (fun p : CoefficientBox => side.q p.2.1) := by cases side <;> unfold Side.q <;> fun_prop
  have hR₀ := (N.R_joint_continuous side (by norm_num : (0:ℝ)<32)).comp parameterProjection_continuous
  have hR₁ := (N.R_joint_continuous side (by norm_num : (0:ℝ)<64)).comp parameterProjection_continuous
  have hRz := (N.Rzero_joint_continuous side).comp parameterProjection_continuous
  have hbar := (P.comparisonC_joint_continuous N side).comp parameterProjection_continuous
  -- Establish continuity hstate before using the function at limits or in calculus arguments.
  have hstate : Continuous (fun p : CoefficientBox =>
      ((p.1:ℝ),((p.2.1:ℝ),((0:ℝ),(p.2.2.1:ℝ),(p.2.2.2.1:ℝ),(p.2.2.2.2:ℝ))))) := by fun_prop
  have hb := (P.normalizedB_smooth N side).continuousOn.comp_continuous hstate
    (fun p => ⟨p.1.property,p.2.1.property,mem_univ _⟩)
  have hkn : ∀ p : CoefficientBox,(p.1:ℝ)≠0 := fun p => p.1.property.ne'
  have hrn : ∀ p : CoefficientBox,N.root p.1 p.2.1≠0 := fun p => (N.root_spec p.1.property p.2.1.property).1.ne'
  have hdn : ∀ p : CoefficientBox,N.speed p.1 p.2.1≠0 := fun p => (N.speed_positive p.1.property p.2.1.property).ne'
  have hD₀ : ∀ p : CoefficientBox,
      2+side.q p.2.1*(32/(p.1:ℝ))*(p.2.2.1:ℝ)+(2-side.q p.2.1)*N.R side p.1.property 32 p.2.1≠0 :=
    fun p => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<2)
      (N.determinantTerm_denominator side p.1.property (by norm_num) p.2.1.property p.2.2.1.property))
  have hD₁ : ∀ p : CoefficientBox,
      2+side.q p.2.1*(64/(p.1:ℝ))*(p.2.2.2.1:ℝ)+(2-side.q p.2.1)*N.R side p.1.property 64 p.2.1≠0 :=
    fun p => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<2)
      (N.determinantTerm_denominator side p.1.property (by norm_num) p.2.1.property p.2.2.2.1.property))
  -- Establish continuity hcap before using the function at limits or in calculus arguments.
  have hcap : Continuous (fun p : CoefficientBox => 2-(p.2.1:ℝ)^3) := continuous_const.sub (ht.pow 3)
  -- Establish continuity hden₀ before using the function at limits or in calculus arguments.
  have hden₀ : Continuous (fun p : CoefficientBox =>
      2+side.q p.2.1*(32/(p.1:ℝ))*(p.2.2.1:ℝ)+(2-side.q p.2.1)*N.R side p.1.property 32 p.2.1) := (continuous_const.add ((hq.mul (continuous_const.div hk hkn)).mul hu)).add
    ((continuous_const.sub hq).mul hR₀)
  -- Establish continuity hden₁ before using the function at limits or in calculus arguments.
  have hden₁ : Continuous (fun p : CoefficientBox =>
      2+side.q p.2.1*(64/(p.1:ℝ))*(p.2.2.2.1:ℝ)+(2-side.q p.2.1)*N.R side p.1.property 64 p.2.1) := (continuous_const.add ((hq.mul (continuous_const.div hk hkn)).mul hv)).add
    ((continuous_const.sub hq).mul hR₁)
  -- Establish continuity hterm₀ before using the function at limits or in calculus arguments.
  have hterm₀ : Continuous (fun p : CoefficientBox => N.determinantTerm side p.1.property 32 p.2.1 p.2.2.1) :=
    (((continuous_const.mul hcap).mul (continuous_const.add (hu.mul hR₀))).div
      ((hd.mul hr).mul hden₀) (fun p => mul_ne_zero (mul_ne_zero (hdn p) (hrn p)) (hD₀ p)))
  -- Establish continuity hterm₁ before using the function at limits or in calculus arguments.
  have hterm₁ : Continuous (fun p : CoefficientBox => N.determinantTerm side p.1.property 64 p.2.1 p.2.2.2.1) :=
    (((continuous_const.mul hcap).mul (continuous_const.add (hv.mul hR₁))).div
      ((hd.mul hr).mul hden₁) (fun p => mul_ne_zero (mul_ne_zero (hdn p) (hrn p)) (hD₁ p)))
  -- Establish continuity htrace before using the function at limits or in calculus arguments.
  have htrace : Continuous (fun p : CoefficientBox => N.traceTerm side p.1.property p.2.1 p.2.2.2.2) :=
    ((hk.mul hcap).div ((continuous_const.mul hd).mul hr)
      (fun p => mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) (hdn p)) (hrn p))).mul
        (((continuous_const.mul (continuous_const.sub hθ)).mul hRz |>.sub
          (hq.mul (continuous_const.sub hθ))).sub ((continuous_const.sub hq).mul hRz))
  -- Establish continuity hcenter before using the function at limits or in calculus arguments.
  have hcenter : Continuous (fun p : CoefficientBox => P.centeredB N side p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
    hb.add (((hk.mul (hr.pow 2)).div hd hdn).mul hbar)
  exact (((((continuous_const.mul hcap).div (hd.mul hr) (fun p => mul_ne_zero (hdn p) (hrn p))).add
    (continuous_const.mul hterm₀)).add (continuous_const.mul hterm₁)).add (continuous_const.mul htrace)).add hcenter

 /--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.certificateL
p.1 p.2)`.

Use: `«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_spec` with the arguments shown in
the proof.
-/
theorem certificateL_joint_continuous : Continuous (fun p : ParameterDomain => N.certificateL p.1 p.2) := by
  have hk : Continuous (fun p : ParameterDomain => (p.1:ℝ)) := by fun_prop
  have ht : Continuous (fun p : ParameterDomain => (p.2:ℝ)) := by fun_prop
  have hr := N.root_smooth.continuousOn.comp_continuous (hk.prodMk ht)
    (fun p => ⟨p.1.property,p.2.property⟩)
  unfold certificateL
  exact (ht.mul (continuous_const.sub (ht.pow 3))).div (hk.mul (hr.pow 2))
    (fun p => mul_ne_zero p.1.property.ne' (pow_ne_zero _ (N.root_spec p.1.property p.2.property).1.ne'))

end
end «2610.05164v2».DualCertificate.NormalizedCalibration
