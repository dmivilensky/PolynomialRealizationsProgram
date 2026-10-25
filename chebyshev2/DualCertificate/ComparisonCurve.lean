import chebyshev2.DualCertificate.RegularPotential
import chebyshev2.Residual.Gauge
import chebyshev2.Calculus.ZeroExtension

/-!
Article: chebyshev2, Lemma 16.
The actual comparison state and the derivative of the raw potential along it.
Use: `chebyshev2.DualCertificate.PolynomialPotential.curveValue_normalized_derivative` feeds
`chebyshev2.DualCertificate.PolynomialPotential.curveValue_derivative_extended` (curve Value
derivative extended).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_analytic` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.DualCertificate.NormalizedCalibration
noncomputable section
open Set chebyshev2.Calibration chebyshev2.Residual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (N : chebyshev2.DualCertificate.NormalizedCalibration)

/--
Defines `curve` of type `State` by `(q,N.calibration.leftFilter hκ 32
q/32,N.calibration.leftFilter hκ 64 q/64, q-N.calibration.leftLinear hκ q)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.curve_continuous` uses this
definition to establish continuity on the stated domain: `ContinuousOn (N.curve hκ) (Icc 0 2)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def curve {κ : ℝ} (hκ : 0<κ) (q : ℝ) : State :=
  (q,N.calibration.leftFilter hκ 32 q/32,N.calibration.leftFilter hκ 64 q/64,
    q-N.calibration.leftLinear hκ q)

/--
Continuity on the stated domain: `ContinuousOn (N.curve hκ) (Icc 0 2)`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.curveValue_continuous` uses this
continuity result to establish continuity on the stated domain: `ContinuousOn (P.curveValue N
hκ) (Icc 0 2)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.leftFilter_ac`,
`chebyshev2.Calibration.Data.leftLinear_ac` with the arguments shown in the proof.
-/
theorem curve_continuous {κ : ℝ} (hκ : 0<κ) : ContinuousOn (N.curve hκ) (Icc 0 2) := by
  unfold curve
  convert! continuousOn_id.prodMk (((N.calibration.leftFilter_ac hκ (by norm_num : (0:ℝ)≤32)).continuousOn.div_const 32).prodMk
    (((N.calibration.leftFilter_ac hκ (by norm_num : (0:ℝ)≤64)).continuousOn.div_const 64).prodMk
      (continuousOn_id.sub (N.calibration.leftLinear_ac hκ).continuousOn))) using 1
  simp only [uIcc_of_le (by norm_num : (0:ℝ)≤2)]

/--
Exact identity `N.curve hκ 0=(0,0,0,0)`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.curveValue_zero` rewrites with this
identity to establish the identity `P.curveValue N hκ 0=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.leftFilter_zero`,
`chebyshev2.Calibration.Data.leftLinear_zero` with the arguments shown in the proof.
-/
theorem curve_zero {κ : ℝ} (hκ : 0<κ) : N.curve hκ 0=(0,0,0,0) := by
  simp [curve,N.calibration.leftFilter_zero hκ (by norm_num : (0:ℝ)≤32),
    N.calibration.leftFilter_zero hκ (by norm_num : (0:ℝ)≤64),N.calibration.leftLinear_zero hκ]

/--
The actual derivative at the stated point: `HasDerivAt (N.curve hκ) ((N.calibration.speed κ
q)⁻¹ • ((N.calibration.amplitude κ q)^2 • inputVector κ-driftVector (N.curve hκ q))) q`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.curveValue_derivative` uses this
derivative formula to establish the actual derivative at the stated point: `HasDerivAt
(P.curveValue N hκ) ((bPotential κ P.raw (N.curve hκ q)*(N.calibration.amplitude κ q)^2-
dPotential P.raw (N.curve hκ q))/N.calibration.speed κ q) q`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem curve_derivative {κ q : ℝ} (hκ : 0<κ) (hq : q∈Ioo (0:ℝ) 2) :
    HasDerivAt (N.curve hκ)
      ((N.calibration.speed κ q)⁻¹ •
        ((N.calibration.amplitude κ q)^2 • inputVector κ-driftVector (N.curve hκ q))) q := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs := N.calibration.speed_positive hκ hq
  have h := (hasDerivAt_id q).prodMk
    (((N.calibration.leftFilter_derivative hκ (by norm_num : (0:ℝ)≤32) hq).div_const 32).prodMk
      (((N.calibration.leftFilter_derivative hκ (by norm_num : (0:ℝ)≤64) hq).div_const 64).prodMk
        ((hasDerivAt_id q).sub (N.calibration.leftLinear_derivative hκ hq))))
  convert! h using 1
  ext <;> dsimp [curve,inputVector,driftVector,chebyshev2.Calibration.Q]
  all_goals field_simp [hs.ne']
  all_goals try simp only [chebyshev2.Calibration.Data.speed,chebyshev2.Calibration.Q]
  all_goals ring

/--
Exact identity `side.q t*N.U side hκ s t=κ/s*N.calibration.leftFilter hκ s (side.q t)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.curve_normalized` uses this identity
to establish the identity `N.curve hκ (side.q t)=PolynomialPotential.unnormalize κ (side.q
t,N.U side hκ 32 t,N.U side hκ 64 t,N.theta side hκ t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem U_factor (side : Side) {κ s t : ℝ} (hκ : 0<κ) (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) :
    side.q t*N.U side hκ s t=κ/s*N.calibration.leftFilter hκ s (side.q t) := by
  cases side with
  | left => exact N.leftU_factor hκ hs ht
  | right => dsimp [U,farFilter,Side.q]
             field_simp [show 2-t^3≠0 by linarith [(cube_mem ⟨ht.1.le,ht.2⟩).2]]

/--
Exact identity `side.q t*N.theta side hκ t=side.q t-N.calibration.leftLinear hκ (side.q t)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.curve_normalized` uses this identity
to establish the identity `N.curve hκ (side.q t)=PolynomialPotential.unnormalize κ (side.q
t,N.U side hκ 32 t,N.U side hκ 64 t,N.theta side hκ t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem theta_factor (side : Side) {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Ioc (0:ℝ) 1) :
    side.q t*N.theta side hκ t=side.q t-N.calibration.leftLinear hκ (side.q t) := by
  cases side with
  | left => exact N.leftTheta_factor hκ ht
  | right => dsimp [theta,farLinear,Side.q]
             field_simp [show 2-t^3≠0 by linarith [(cube_mem ⟨ht.1.le,ht.2⟩).2]]

/--
Exact identity `N.curve hκ (side.q t)=PolynomialPotential.unnormalize κ (side.q t,N.U side hκ
32 t,N.U side hκ 64 t,N.theta side hκ t)`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.curveValue_normalized_derivative`
rewrites with this identity to establish the actual derivative at the stated point: `HasDerivAt
(P.curveValue N hκ) (t*(N.root κ t)^3/N.speed κ t*P.comparisonC N side hκ t) (side.q t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.U_factor`,
`chebyshev2.DualCertificate.NormalizedCalibration.theta_factor` with the arguments shown in
the proof.
-/
theorem curve_normalized (side : Side) {κ t : ℝ} (hκ : 0<κ) (ht : t∈Ioc (0:ℝ) 1) :
    N.curve hκ (side.q t)=PolynomialPotential.unnormalize κ
      (side.q t,N.U side hκ 32 t,N.U side hκ 64 t,N.theta side hκ t) := by
  -- Use the identities/estimates
  -- `chebyshev2.DualCertificate.NormalizedCalibration.U_factor`,
  -- `chebyshev2.DualCertificate.NormalizedCalibration.theta_factor` with the arguments
  -- shown in the proof.
  have h₀ := N.U_factor side hκ (by norm_num : (0:ℝ)<32) ht
  have h₁ := N.U_factor side hκ (by norm_num : (0:ℝ)<64) ht
  have hh := N.theta_factor side hκ ht
  dsimp [curve,PolynomialPotential.unnormalize]
  ext
  · rfl
  · apply (eq_div_iff hκ.ne').mpr
    nlinarith [h₀]
  · apply (eq_div_iff hκ.ne').mpr
    nlinarith [h₁]
  · exact hh.symm

variable (hΓ : ∀ q∈Icc (0:ℝ) 2,N.calibration.Gamma (2-q)=N.calibration.Gamma q)

include hΓ in
/--
Exact identity `N.calibration.amplitude κ (side.q t)=t*N.root κ t`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.curveValue_normalized_derivative`
rewrites with this identity to establish the actual derivative at the stated point: `HasDerivAt
(P.curveValue N hκ) (t*(N.root κ t)^3/N.speed κ t*P.comparisonC N side hκ t) (side.q t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.root_amplitude`,
`chebyshev2.Calibration.Data.amplitude_reflection` with the arguments shown in the proof.
-/
theorem side_amplitude (side : Side) {κ t : ℝ} (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) :
    N.calibration.amplitude κ (side.q t)=t*N.root κ t := by
  cases side with
  | left => exact N.root_amplitude hκ ht
  | right => rw [Side.q,N.calibration.amplitude_reflection hκ hΓ,N.root_amplitude hκ ht]

include hΓ in
/--
Exact identity `N.calibration.speed κ (side.q t)=t^2*N.speed κ t`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.curveValue_normalized_derivative`
rewrites with this identity to establish the actual derivative at the stated point: `HasDerivAt
(P.curveValue N hκ) (t*(N.root κ t)^3/N.speed κ t*P.comparisonC N side hκ t) (side.q t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.speed_factor`,
`chebyshev2.Calibration.Data.speed_reflection` with the arguments shown in the proof.
-/
theorem side_speed (side : Side) {κ t : ℝ} (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) :
    N.calibration.speed κ (side.q t)=t^2*N.speed κ t := by
  cases side with
  | left => exact N.speed_factor hκ ht
  | right => rw [Side.q,N.calibration.speed_reflection hκ hΓ,N.speed_factor hκ ht]

end
end chebyshev2.DualCertificate.NormalizedCalibration

namespace chebyshev2.DualCertificate.PolynomialPotential
noncomputable section
open Set chebyshev2.Residual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable (P : chebyshev2.DualCertificate.PolynomialPotential) (N : NormalizedCalibration)

/--
Defines `curveValue` of type `ℝ` by `P.raw (N.curve hκ q)`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.curveValue_derivative` uses this
definition to establish the actual derivative at the stated point: `HasDerivAt (P.curveValue N
hκ) ((bPotential κ P.raw (N.curve hκ q)*(N.calibration.amplitude κ q)^2- dPotential P.raw
(N.curve hκ q))/N.calibration.speed κ q) q`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def curveValue {κ : ℝ} (hκ : 0<κ) (q : ℝ) : ℝ := P.raw (N.curve hκ q)

/--
The actual derivative at the stated point: `HasDerivAt (P.curveValue N hκ) ((bPotential κ P.raw
(N.curve hκ q)*(N.calibration.amplitude κ q)^2- dPotential P.raw (N.curve hκ
q))/N.calibration.speed κ q) q`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.curveValue_normalized_derivative` uses
this derivative formula to establish the actual derivative at the stated point: `HasDerivAt
(P.curveValue N hκ) (t*(N.root κ t)^3/N.speed κ t*P.comparisonC N side hκ t) (side.q t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.PolynomialPotential.raw_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.curve_derivative` with the arguments
shown in the proof.
-/
theorem curveValue_derivative {κ q : ℝ} (hκ : 0<κ) (hq : q∈Ioo (0:ℝ) 2) :
    HasDerivAt (P.curveValue N hκ)
      ((bPotential κ P.raw (N.curve hκ q)*(N.calibration.amplitude κ q)^2-
        dPotential P.raw (N.curve hκ q))/N.calibration.speed κ q) q := by
  -- Use the identities/estimates
  -- `chebyshev2.DualCertificate.PolynomialPotential.raw_smooth`,
  -- `chebyshev2.DualCertificate.NormalizedCalibration.curve_derivative` with the arguments
  -- shown in the proof.
  have h := (P.raw_smooth.differentiable (by norm_num) (N.curve hκ q)).hasFDerivAt.comp_hasDerivAt q
    (N.curve_derivative hκ hq)
  convert! h using 1
  simp only [map_smul,map_sub,smul_eq_mul,bPotential,dPotential,div_eq_mul_inv]
  ring

 /--
The actual derivative at the stated point: `HasDerivAt (P.curveValue N hκ) (t*(N.root κ
t)^3/N.speed κ t*P.comparisonC N side hκ t) (side.q t)`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.centering_normalized_derivative` uses
this derivative formula to establish the actual derivative at the stated point: `HasDerivAt
(P.centering N hκ) (P.sideSlope N side hκ t) (side.q t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem curveValue_normalized_derivative
    (hΓ : ∀ q∈Icc (0:ℝ) 2,N.calibration.Gamma (2-q)=N.calibration.Gamma q)
    (side : Side) {κ t : ℝ} (hκ : 0<κ) (ht : t∈Ioc (0:ℝ) 1) :
    HasDerivAt (P.curveValue N hκ)
      (t*(N.root κ t)^3/N.speed κ t*P.comparisonC N side hκ t) (side.q t) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := P.curveValue_derivative N hκ (side.q_interior ht)
  rw [N.curve_normalized side hκ ht,N.side_amplitude hΓ side hκ ⟨ht.1.le,ht.2⟩,
    N.side_speed hΓ side hκ ⟨ht.1.le,ht.2⟩] at h
  convert! h using 1
  unfold comparisonC
  rw [P.normalizedC_identity N side hκ ht]
  field_simp [ht.1.ne',(N.root_spec hκ ⟨ht.1.le,ht.2⟩).1.ne']

end
end chebyshev2.DualCertificate.PolynomialPotential
