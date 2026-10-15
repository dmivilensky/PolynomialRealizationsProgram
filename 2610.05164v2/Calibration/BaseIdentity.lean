import «2610.05164v2».Calibration.Filter

/-!
Article: 2610.05164v2, Proposition 4.
Proposition 4's exact nonnegative-defect decomposition (18).
Use: `«2610.05164v2».Calibration.Data.energy_ge_base` feeds
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_minimum_finite` (self Consistent minimum
finite).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Calibration
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».GroundState «2610.05164v2».Filters «2610.05164v2».Sobolev
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace Data
variable (C : Data)

/--
Defines `Vprime` of type `ℝ` by `-(C.b+3/2*C.extendedAmplitude κ q)/κ`.

Use: `«2610.05164v2».Calibration.Data.V` uses this definition in the displayed construction of
`V`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def Vprime (κ q : ℝ) : ℝ := -(C.b+3/2*C.extendedAmplitude κ q)/κ
/--
Defines `V` of type `ℝ → ℝ` by `primitive (C.Vprime κ)`.

Use: `«2610.05164v2».Calibration.Data.V_two` uses this definition to establish the precise
assertion is `C.V κ 2= -(2*C.b+3/2*(∫ q in (0:ℝ)..2, C.amplitude κ q))/κ`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def V (κ : ℝ) : ℝ → ℝ := primitive (C.Vprime κ)
/--
Defines `T` of type `ℝ` by `C.F q h-C.Gamma q`.

Use: `«2610.05164v2».Calibration.Data.T_integrable` uses this definition to establish
integrability of the displayed function: `Integrable (fun x => C.T (G.q x) (C.calibrationState
G x))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def T (q h : ℝ) : ℝ := C.F q h-C.Gamma q
/--
Defines `base` of type `ℝ` by `-C.b+2*C.b/κ+ 3/(2*κ)*(∫ q in (0:ℝ)..2, C.amplitude κ
q)-C.omega*C.J 2- C.omega*(κ/C.sigma-2/C.sigma^2*H)`.

Use: `«2610.05164v2».Calibration.Data.base_identity` uses this definition to establish the
identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def base (κ H : ℝ) : ℝ := -C.b+2*C.b/κ+
  3/(2*κ)*(∫ q in (0:ℝ)..2, C.amplitude κ q)-C.omega*C.J 2-
  C.omega*(κ/C.sigma-2/C.sigma^2*H)

/--
Continuity of the displayed function: `Continuous (C.Vprime κ)`.

Use: `«2610.05164v2».Calibration.Data.V_c1` uses this continuity result to establish smoothness
to the stated order: `ContDiff ℝ 1 (C.V κ)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.extendedAmplitude_continuous` with the arguments shown in the
proof.
-/
theorem Vprime_continuous {κ : ℝ} (hκ : 0 < κ) : Continuous (C.Vprime κ) :=
  (continuous_const.add (continuous_const.mul (C.extendedAmplitude_continuous hκ))).neg.div_const _

/--
Smoothness to the stated order: `ContDiff ℝ 1 (C.V κ)`.

Use: `«2610.05164v2».Calibration.Data.V_composition_mass` uses this assertion to establish
exact identity `(∫ x, C.Vprime (groundParameter hm hn) (G.q x)* (groundParameter hm hn*m x-Q
(G.q x)))=C.V (groundParameter hm hn) 2`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.primitive_c1`,
`«2610.05164v2».Calibration.Data.Vprime_continuous` with the arguments shown in the proof.
-/
theorem V_c1 {κ : ℝ} (hκ : 0 < κ) : ContDiff ℝ 1 (C.V κ) := primitive_c1 (C.Vprime_continuous hκ)

/--
The actual derivative at the stated point: `HasDerivAt (C.V κ) (C.Vprime κ q) q`.

Use: `«2610.05164v2».Calibration.Data.V_composition_derivative` uses this derivative formula to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun
x => C.V (groundParameter hm hn) (G.q x)) (C.Vprime (groundParameter hm hn) (G.q
x)*(groundParameter hm hn*m x-Q (G.q x))) x`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.primitive_derivative`,
`«2610.05164v2».Calibration.Data.Vprime_continuous` with the arguments shown in the proof.
-/
theorem V_derivative {κ : ℝ} (hκ : 0 < κ) (q : ℝ) :
    HasDerivAt (C.V κ) (C.Vprime κ q) q := primitive_derivative (C.Vprime_continuous hκ) q

/--
Exact identity `C.V κ 0=0`.

Use: `«2610.05164v2».Calibration.Data.V_composition_mass` uses this identity to establish exact
identity `(∫ x, C.Vprime (groundParameter hm hn) (G.q x)* (groundParameter hm hn*m x-Q (G.q
x)))=C.V (groundParameter hm hn) 2`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem V_zero (κ : ℝ) : C.V κ 0=0 := by simp [V,primitive]

/--
The precise assertion is `C.V κ 2= -(2*C.b+3/2*(∫ q in (0:ℝ)..2, C.amplitude κ q))/κ`.

Use: `«2610.05164v2».Calibration.Data.base_identity` rewrites with this identity to establish
the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem V_two (κ : ℝ) : C.V κ 2=
    -(2*C.b+3/2*(∫ q in (0:ℝ)..2, C.amplitude κ q))/κ := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  unfold V primitive Vprime
  have hκ : 0 < κ ∨ κ ≤ 0 := lt_or_ge 0 κ
  have he : (∫ q in (0:ℝ)..2, C.extendedAmplitude κ q)=
      ∫ q in (0:ℝ)..2, C.amplitude κ q := by
    apply intervalIntegral.integral_congr
    intro q hq
    exact C.extendedAmplitude_eq (by simpa using hq)
  rcases hκ with hk | hk
  · rw [intervalIntegral.integral_div,intervalIntegral.integral_neg,
      intervalIntegral.integral_add intervalIntegrable_const
        ((C.extendedAmplitude_continuous hk).intervalIntegrable _ _ |>.const_mul (3/2:ℝ)),
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul,he,smul_eq_mul]
    ring
  · have he0 : C.amplitude κ=0 := by
      funext q
      simp [amplitude,positiveRoot,not_lt.mpr hk]
    have he1 : C.extendedAmplitude κ=0 := by funext q; simp [extendedAmplitude,he0]
    simp [he0,he1,intervalIntegral.integral_const,smul_eq_mul]

/--
The precise assertion is `n^3+C.b*n^2+C.omega*f^2+ C.Vprime κ q*(κ*n^2-Q q)+C.omega*C.Jprime
h*(q^2+C.sigma*f^2-2*h)= rho n (C.amplitude κ q)+C.omega*C.T q h`.

Use: `«2610.05164v2».Calibration.Data.base_identity` uses this identity to establish the
identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem base_pointwise {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Icc (0:ℝ) 2) (n f h : ℝ)
    (hh : h=q-f) :
    n^3+C.b*n^2+C.omega*f^2+
      C.Vprime κ q*(κ*n^2-Q q)+C.omega*C.Jprime h*(q^2+C.sigma*f^2-2*h)=
        rho n (C.amplitude κ q)+C.omega*C.T q h := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hcal := C.calibration_identity q h
  have hcubic := C.amplitude_equation hκ hq
  rw [Vprime,C.extendedAmplitude_eq hq]
  unfold T constant at *
  have hf : q-h=f := by rw [hh]; ring
  rw [hf] at hcal
  have ht := tangent_identity n (C.amplitude κ q)
  field_simp [hκ.ne']
  linear_combination 2*κ*ht+2*κ*C.omega*hcal-hcubic

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)
include G

/--
The stated quantitative bound `0 ≤ C.T (G.q x) (C.calibrationState G x)`.

Use: `«2610.05164v2».Calibration.Data.energy_ge_base` uses this bound to establish the stated
quantitative bound `C.base (groundParameter hm hn) («2610.05164v2».Continuum.logDeterminant
(«2610.05164v2».Continuum.kernelEigenvalue hm hn) (C.sigma*groundParameter hm hn)) ≤ (∫ x,
(sqrt (m x))^3)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.Gamma_le_state`,
`«2610.05164v2».GroundState.GroundWitness.coordinate_mem`,
`«2610.05164v2».Calibration.Data.calibrationState_bounds` with the arguments shown in the
proof.
-/
theorem T_nonneg (x : ℝ) : 0 ≤ C.T (G.q x) (C.calibrationState G x) :=
  sub_nonneg.mpr (C.Gamma_le_state (G.coordinate_mem x).1 (C.calibrationState_bounds G x))

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => C.V
(groundParameter hm hn) (G.q x)) (C.Vprime (groundParameter hm hn) (G.q x)*(groundParameter hm
hn*m x-Q (G.q x))) x`.

Use: `«2610.05164v2».Calibration.Data.V_composition_mass` uses this identity to establish exact
identity `(∫ x, C.Vprime (groundParameter hm hn) (G.q x)* (groundParameter hm hn*m x-Q (G.q
x)))=C.V (groundParameter hm hn) 2`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem V_composition_derivative : ∀ᵐ x, HasDerivAt (fun x => C.V (groundParameter hm hn) (G.q x))
    (C.Vprime (groundParameter hm hn) (G.q x)*(groundParameter hm hn*m x-Q (G.q x))) x := by
  filter_upwards [G.coordinate_derivative] with x hx
  exact (C.V_derivative G.coupling_positive (G.q x)).comp x hx

/--
Integrability of the displayed function: `Integrable (fun x => C.Vprime (groundParameter hm hn)
(G.q x)*(groundParameter hm hn*m x-Q (G.q x)))`.

Use: `«2610.05164v2».Calibration.Data.V_composition_mass` uses this integrability result to
establish exact identity `(∫ x, C.Vprime (groundParameter hm hn) (G.q x)* (groundParameter hm
hn*m x-Q (G.q x)))=C.V (groundParameter hm hn) 2`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.amplitude_bounded`,
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».Calibration.continuous_mul_derivative_integrable` with the arguments shown in
the proof.
-/
theorem V_composition_integrable : Integrable (fun x =>
    C.Vprime (groundParameter hm hn) (G.q x)*(groundParameter hm hn*m x-Q (G.q x))) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.amplitude_bounded`,
  -- `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».Calibration.continuous_mul_derivative_integrable` with the arguments shown
  -- in the proof.
  obtain ⟨M,_,hM⟩ := C.amplitude_bounded G.coupling_positive
  apply continuous_mul_derivative_integrable (B := (C.b+3/2*M)/groundParameter hm hn) G.R.q_continuous
    (C.Vprime_continuous G.coupling_positive) G.coordinate_integrability.2
  intro x
  change ‖C.Vprime (groundParameter hm hn) (G.q x)‖ ≤ (C.b+3/2*M)/groundParameter hm hn
  have hb := C.b_positive
  have hν := C.amplitude_nonneg G.coupling_positive (G.q x)
  rw [Vprime,C.extendedAmplitude_eq (G.coordinate_mem x),norm_div,norm_neg,
    Real.norm_of_nonneg (by positivity : 0 ≤ C.b+3/2*C.amplitude (groundParameter hm hn) (G.q x)),
    Real.norm_of_nonneg G.coupling_positive.le]
  exact div_le_div_of_nonneg_right (by linarith [hM _ (G.coordinate_mem x)]) G.coupling_positive.le

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => C.J
(C.calibrationState G x)) (C.Jprime (C.calibrationState G x)* ((G.q
x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x)) x`.

Use: `«2610.05164v2».Calibration.Data.J_composition_mass` uses this identity to establish exact
identity `(∫ x, C.Jprime (C.calibrationState G x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm
hn x)^2-2*C.calibrationState G x))=C.J 2`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem J_composition_derivative : ∀ᵐ x, HasDerivAt (fun x => C.J (C.calibrationState G x))
    (C.Jprime (C.calibrationState G x)*
      ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x)) x := by
  filter_upwards [C.calibrationState_derivative G] with x hx
  exact (C.J_derivative (C.calibrationState G x)).comp x hx

/--
Integrability of the displayed function: `Integrable (fun x => C.Jprime (C.calibrationState G
x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x))`.

Use: `«2610.05164v2».Calibration.Data.J_composition_mass` uses this integrability result to
establish exact identity `(∫ x, C.Jprime (C.calibrationState G x)* ((G.q
x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x))=C.J 2`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.continuous_mul_derivative_integrable`,
`«2610.05164v2».GroundState.locallyAC_continuous`,
`«2610.05164v2».Calibration.Data.calibrationState_locallyAC` with the arguments shown in the
proof.
-/
theorem J_composition_integrable : Integrable (fun x => C.Jprime (C.calibrationState G x)*
    ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x)) :=
  continuous_mul_derivative_integrable (locallyAC_continuous (C.calibrationState_locallyAC G))
    C.Jprime_continuous (C.calibrationState_derivative_integrable G) (fun _ => C.Jprime_bound _)

/--
Exact identity `(∫ x, C.Vprime (groundParameter hm hn) (G.q x)* (groundParameter hm hn*m x-Q
(G.q x)))=C.V (groundParameter hm hn) 2`.

Use: `«2610.05164v2».Calibration.Data.base_identity` rewrites with this identity to establish
the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem V_composition_mass : (∫ x, C.Vprime (groundParameter hm hn) (G.q x)*
    (groundParameter hm hn*m x-Q (G.q x)))=C.V (groundParameter hm hn) 2 := by
  have hc := (C.V_c1 G.coupling_positive).continuous
  have h := integral_derivative_eq_limits
    (locallyAC_comp_c1_interval G.coordinate_mem G.coordinate_locallyAC (C.V_c1 G.coupling_positive))
    (C.V_composition_derivative G) (C.V_composition_integrable G)
    (hc.continuousAt.tendsto.comp G.coordinate_limits.1) (hc.continuousAt.tendsto.comp G.coordinate_limits.2)
  simpa only [C.V_zero,sub_zero] using h

/--
Exact identity `(∫ x, C.Jprime (C.calibrationState G x)* ((G.q
x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x))=C.J 2`.

Use: `«2610.05164v2».Calibration.Data.base_identity` rewrites with this identity to establish
the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem J_composition_mass : (∫ x, C.Jprime (C.calibrationState G x)*
    ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x))=C.J 2 := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have hb (x : ℝ) : C.calibrationState G x ∈ Icc (0:ℝ) 2 :=
    ⟨(C.calibrationState_bounds G x).1,(C.calibrationState_bounds G x).2.trans (G.coordinate_mem x).2⟩
  have hc := C.J_c1.continuous
  have h := integral_derivative_eq_limits
    (locallyAC_comp_c1_interval hb (C.calibrationState_locallyAC G) C.J_c1)
    (C.J_composition_derivative G) (C.J_composition_integrable G)
    (hc.continuousAt.tendsto.comp (C.calibrationState_limits G).1)
    (hc.continuousAt.tendsto.comp (C.calibrationState_limits G).2)
  simpa only [C.J_zero,sub_zero] using h

/--
Integrability of the displayed function: `Integrable (fun x => C.Gamma (G.q x))`.

Use: `«2610.05164v2».Calibration.Data.T_integrable` uses this integrability result to establish
integrability of the displayed function: `Integrable (fun x => C.T (G.q x) (C.calibrationState
G x))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coordinate_integrability`,
`«2610.05164v2».Calibration.Data.Gamma_continuous`,
`«2610.05164v2».GroundState.RiccatiData.q_continuous` with the arguments shown in the proof.
-/
theorem Gamma_integrable : Integrable (fun x => C.Gamma (G.q x)) := by
  apply G.coordinate_integrability.1.mono' (C.Gamma_continuous.comp G.R.q_continuous).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖C.Gamma (G.q x)‖ ≤ Q (G.q x)
    rw [Real.norm_of_nonneg (C.Gamma_nonneg (G.coordinate_mem x))]
    exact C.Gamma_le_Q (G.coordinate_mem x))

/--
Integrability of the displayed function: `Integrable (fun x => C.T (G.q x) (C.calibrationState
G x))`.

Use: `«2610.05164v2».Calibration.Data.energy_eq_base_iff` uses this integrability result to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.calibrationFilter_square_integrable`,
`«2610.05164v2».Calibration.Data.J_composition_integrable`,
`«2610.05164v2».Calibration.Data.Gamma_integrable` with the arguments shown in the proof.
-/
theorem T_integrable : Integrable (fun x => C.T (G.q x) (C.calibrationState G x)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.Data.calibrationFilter_square_integrable`,
  -- `«2610.05164v2».Calibration.Data.J_composition_integrable`,
  -- `«2610.05164v2».Calibration.Data.Gamma_integrable` with the arguments shown in the proof.
  apply (((C.calibrationFilter_square_integrable G).add
    (C.J_composition_integrable G)).sub (C.Gamma_integrable G)).congr
  exact Eventually.of_forall (fun x => by
    have he := C.calibration_identity (G.q x) (C.calibrationState G x)
    change (C.calibrationFilter hm hn x)^2+C.Jprime (C.calibrationState G x)*
      ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x)-
        C.Gamma (G.q x)=C.T (G.q x) (C.calibrationState G x)
    unfold T
    convert congrArg (fun z => z-C.Gamma (G.q x)) he using 1
    dsimp [calibrationState]
    ring)

/--
Integrability of the displayed function: `Integrable (fun x => C.amplitude (groundParameter hm
hn) (G.q x)*m x)`.

Use: `«2610.05164v2».Calibration.Data.rho_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun x => rho (sqrt (m x))
(C.amplitude (groundParameter hm hn) (G.q x)))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.amplitude_bounded`,
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».Calibration.Data.amplitude_continuousOn_fixed` with the arguments shown in the
proof.
-/
theorem amplitude_mul_density_integrable : Integrable (fun x =>
    C.amplitude (groundParameter hm hn) (G.q x)*m x) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.amplitude_bounded`,
  -- `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».Calibration.Data.amplitude_continuousOn_fixed` with the arguments shown in
  -- the proof.
  obtain ⟨M,_,hM⟩ := C.amplitude_bounded G.coupling_positive
  apply hm.bdd_mul (c := M)
    ((C.amplitude_continuousOn_fixed G.coupling_positive).comp_continuous G.R.q_continuous
      G.coordinate_mem).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖C.amplitude (groundParameter hm hn) (G.q x)‖ ≤ M
    rw [Real.norm_of_nonneg (C.amplitude_nonneg G.coupling_positive _)]
    exact hM _ (G.coordinate_mem x))

/--
Integrability of the displayed function: `Integrable (fun x => rho (sqrt (m x)) (C.amplitude
(groundParameter hm hn) (G.q x)))`.

Use: `«2610.05164v2».Calibration.Data.energy_eq_base_iff` uses this integrability result to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.amplitude_mul_density_integrable`,
`«2610.05164v2».Calibration.Data.amplitude_cube_integrable`,
`«2610.05164v2».Calibration.tangent_identity` with the arguments shown in the proof.
-/
theorem rho_integrable (hE : Integrable (fun x => (sqrt (m x))^3)) :
    Integrable (fun x => rho (sqrt (m x)) (C.amplitude (groundParameter hm hn) (G.q x))) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.Data.amplitude_mul_density_integrable`,
  -- `«2610.05164v2».Calibration.Data.amplitude_cube_integrable`,
  -- `«2610.05164v2».Calibration.tangent_identity` with the arguments shown in the proof.
  apply ((hE.sub ((C.amplitude_mul_density_integrable G).const_mul (3/2:ℝ))).add
    ((C.amplitude_cube_integrable G).div_const 2)).congr
  exact Eventually.of_forall (fun x => by
    change (sqrt (m x))^3-3/2*(C.amplitude (groundParameter hm hn) (G.q x)*m x)+
      (C.amplitude (groundParameter hm hn) (G.q x))^3/2=_
    have ht := tangent_identity (sqrt (m x)) (C.amplitude (groundParameter hm hn) (G.q x))
    rw [sq_sqrt (hn x)] at ht
    linarith)

/--
Equation (18) for the article's full finite-energy L1 class. The parameter and logarithmic
observation on the right are the actual spectrum.

Use: `«2610.05164v2».Calibration.Data.energy_ge_base` rewrites with this identity to establish
the stated quantitative bound `C.base (groundParameter hm hn)
(«2610.05164v2».Continuum.logDeterminant («2610.05164v2».Continuum.kernelEigenvalue hm hn)
(C.sigma*groundParameter hm hn)) ≤ (∫ x, (sqrt (m x))^3)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem base_identity (hM : (∫ x, m x)=1) (hE : Integrable (fun x => (sqrt (m x))^3)) :
    (∫ x, (sqrt (m x))^3)=
      C.base (groundParameter hm hn)
        («2610.05164v2».Continuum.logDeterminant («2610.05164v2».Continuum.kernelEigenvalue hm hn)
          (C.sigma*groundParameter hm hn))+
        ∫ x, rho (sqrt (m x)) (C.amplitude (groundParameter hm hn) (G.q x))+
          C.omega*C.T (G.q x) (C.calibrationState G x) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hpoint (x : ℝ) := C.base_pointwise G.coupling_positive (G.coordinate_mem x)
    (sqrt (m x)) (C.calibrationFilter hm hn x) (C.calibrationState G x) rfl
  have he := congrArg (fun f : ℝ → ℝ => ∫ x, f x)
    (funext (fun x => hpoint x))
  simp only [sq_sqrt (hn _)] at he
  simp only [mul_assoc] at he
  rw [integral_add (f := fun x => (sqrt (m x))^3+C.b*m x+
      C.omega*(C.calibrationFilter hm hn x)^2+
      C.Vprime (groundParameter hm hn) (G.q x)*(groundParameter hm hn*m x-Q (G.q x)))
      (g := fun x => C.omega*(C.Jprime (C.calibrationState G x)*
        ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x)))
      (hE.add (hm.const_mul C.b) |>.add
      ((C.calibrationFilter_square_integrable G).const_mul C.omega) |>.add
      (C.V_composition_integrable G)) ((C.J_composition_integrable G).const_mul C.omega),
    integral_add (f := fun x => (sqrt (m x))^3+C.b*m x+C.omega*(C.calibrationFilter hm hn x)^2)
      (g := fun x => C.Vprime (groundParameter hm hn) (G.q x)*(groundParameter hm hn*m x-Q (G.q x)))
      (hE.add (hm.const_mul C.b) |>.add
      ((C.calibrationFilter_square_integrable G).const_mul C.omega)) (C.V_composition_integrable G),
    integral_add (f := fun x => (sqrt (m x))^3+C.b*m x) (g := fun x => C.omega*(C.calibrationFilter hm hn x)^2)
      (hE.add (hm.const_mul C.b)) ((C.calibrationFilter_square_integrable G).const_mul C.omega),
    integral_add (f := fun x => (sqrt (m x))^3) (g := fun x => C.b*m x)
      hE (hm.const_mul C.b),integral_const_mul,integral_const_mul,
    C.V_composition_mass G,integral_const_mul,C.J_composition_mass G,
    C.calibrationFilter_square_mass G,hM,C.V_two] at he
  unfold base
  field_simp [G.coupling_positive.ne',C.sigma_positive.ne'] at he ⊢
  nlinarith

/--
Proposition 6's continuum bound for finite energy.

The stated quantitative bound `C.base (groundParameter hm hn)
(«2610.05164v2».Continuum.logDeterminant («2610.05164v2».Continuum.kernelEigenvalue hm hn)
(C.sigma*groundParameter hm hn)) ≤ (∫ x, (sqrt (m x))^3)`.

Use: `«2610.05164v2».Calibration.Data.one_determinant_lower_bound` uses this bound to establish
the stated quantitative bound `ENNReal.ofReal (C.base (groundParameter hm hn) (logDeterminant
(kernelEigenvalue hm hn) (C.sigma*groundParameter hm hn))) ≤ ∫⁻ x, ENNReal.ofReal (m
x^(3/2:ℝ))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.base_identity`,
`«2610.05164v2».Calibration.rho_nonneg`, `«2610.05164v2».Calibration.Data.amplitude_nonneg`
with the arguments shown in the proof.
-/
theorem energy_ge_base (hM : (∫ x, m x)=1) (hE : Integrable (fun x => (sqrt (m x))^3)) :
    C.base (groundParameter hm hn)
      («2610.05164v2».Continuum.logDeterminant («2610.05164v2».Continuum.kernelEigenvalue hm hn)
        (C.sigma*groundParameter hm hn)) ≤ (∫ x, (sqrt (m x))^3) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.base_identity`,
  -- `«2610.05164v2».Calibration.rho_nonneg`,
  -- `«2610.05164v2».Calibration.Data.amplitude_nonneg` with the arguments shown in the proof.
  rw [C.base_identity G hM hE]
  apply le_add_of_nonneg_right
  apply integral_nonneg
  intro x
  exact add_nonneg (rho_nonneg (sqrt_nonneg _) (C.amplitude_nonneg G.coupling_positive _))
    (mul_nonneg C.omega_nonneg (C.T_nonneg G x))

end Data
end
end «2610.05164v2».Calibration
