import «2610.05164v2».DualCertificate.CenteredPotential

/-!
Article: 2610.05164v2, Theorem 3.6.
Actual normalized coefficients of the centered potential.
Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centered_d_endpoints` feeds
`«2610.05164v2».DualCertificate.Data.boundary_residual` (boundary residual).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate.PolynomialPotential
noncomputable section
open Set «2610.05164v2».Residual «2610.05164v2».Calculus «2610.05164v2».Calibration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (P : «2610.05164v2».DualCertificate.PolynomialPotential) (N : NormalizedCalibration)

/--
Defines `centeredB` of type `ℝ` by `P.normalizedB N side κ t U₀ U₁ θ+ κ*(N.root κ t)^2/N.speed
κ t*P.comparisonC N side hκ t`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centeredB_identity` uses this
definition to establish `P.centeredB N side hκ t U₀ U₁ θ= -bPotential
κ (P.centered N hκ) (unnormalize κ (side.q t,U₀,U₁,θ))/(t*N.root κ t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def centeredB (side : Side) {κ : ℝ} (hκ : 0<κ) (t U₀ U₁ θ : ℝ) : ℝ :=
  P.normalizedB N side κ t U₀ U₁ θ+
    κ*(N.root κ t)^2/N.speed κ t*P.comparisonC N side hκ t

/--
Defines `centeredC` of type `ℝ` by `P.normalizedC N side κ t U₀ U₁ θ-P.comparisonC N side hκ
t`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centeredC_identity` uses this
definition to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def centeredC (side : Side) {κ : ℝ} (hκ : 0<κ) (t U₀ U₁ θ : ℝ) : ℝ :=
  P.normalizedC N side κ t U₀ U₁ θ-P.comparisonC N side hκ t

variable (hΓ : ∀ q∈Icc (0:ℝ) 2,N.calibration.Gamma (2-q)=N.calibration.Gamma q)

include hΓ in
/--
The actual derivative at the stated point: `HasDerivAt (P.centering N hκ) (P.sideSlope N side
hκ t) (side.q t)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centeredB_identity` rewrites with this
derivative formula to establish `P.centeredB N side hκ t U₀ U₁ θ=
-bPotential κ (P.centered N hκ) (unnormalize κ (side.q t,U₀,U₁,θ))/(t*N.root κ t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem centering_normalized_derivative (side : Side) {κ t : ℝ}
    (hκ : 0<κ) (ht : t∈Ioc (0:ℝ) 1) :
    HasDerivAt (P.centering N hκ) (P.sideSlope N side hκ t) (side.q t) := by
  apply (P.curveValue_normalized_derivative N hΓ side hκ ht).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (side.q_interior ht).1 (side.q_interior ht).2] with q hq
  exact indicator_of_mem hq _

include hΓ in
/--
The precise assertion is `P.centeredB N side hκ t U₀ U₁ θ= -bPotential κ (P.centered N hκ)
(unnormalize κ (side.q t,U₀,U₁,θ))/(t*N.root κ t)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_identity` rewrites with
this identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem centeredB_identity (side : Side) {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Ioc (0:ℝ) 1) (U₀ U₁ θ : ℝ) :
    P.centeredB N side hκ t U₀ U₁ θ=
      -bPotential κ (P.centered N hκ)
        (unnormalize κ (side.q t,U₀,U₁,θ))/(t*N.root κ t) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [centered,gaugePotential_b (P.raw_smooth.of_le (by simp)) (P.centering_c1 N hΓ hκ)]
  rw [show (unnormalize κ (side.q t,U₀,U₁,θ)).1=side.q t from rfl,
    (P.centering_normalized_derivative N hΓ side hκ ht).deriv]
  unfold centeredB sideSlope
  rw [P.normalizedB_identity N side hκ ht]
  field_simp [ht.1.ne',(N.root_spec hκ ⟨ht.1.le,ht.2⟩).1.ne']
  ring

include hΓ in
/--
The precise assertion is `P.centeredC N side hκ t U₀ U₁ θ= (bPotential κ (P.centered N hκ)
(unnormalize κ (side.q t,U₀,U₁,θ))*(t*N.root κ t)^2- dPotential (P.centered N hκ) (unnormalize
κ (side.q t,U₀,U₁,θ)))/(t*N.root κ t)^3`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.actual_normalized_criterion`
rewrites with this identity to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem centeredC_identity (side : Side) {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Ioc (0:ℝ) 1) (U₀ U₁ θ : ℝ) :
    P.centeredC N side hκ t U₀ U₁ θ=
      (bPotential κ (P.centered N hκ) (unnormalize κ (side.q t,U₀,U₁,θ))*(t*N.root κ t)^2-
        dPotential (P.centered N hκ) (unnormalize κ (side.q t,U₀,U₁,θ)))/(t*N.root κ t)^3 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [centered,gaugePotential_b (P.raw_smooth.of_le (by simp)) (P.centering_c1 N hΓ hκ),
    gaugePotential_d (P.raw_smooth.of_le (by simp)) (P.centering_c1 N hΓ hκ)]
  rw [show (unnormalize κ (side.q t,U₀,U₁,θ)).1=side.q t from rfl,
    (P.centering_normalized_derivative N hΓ side hκ ht).deriv,side.Q]
  unfold centeredC sideSlope
  rw [P.normalizedC_identity N side hκ ht]
  have he := N.speed_root hκ ⟨ht.1.le,ht.2⟩
  field_simp [ht.1.ne',(N.root_spec hκ ⟨ht.1.le,ht.2⟩).1.ne',
    (N.speed_positive hκ ⟨ht.1.le,ht.2⟩).ne']
  linear_combination (t^3*(N.root κ t)^3*P.comparisonC N side hκ t)*he

include hΓ in
/--
Exact identity `dPotential (P.centered N hκ) Y=0`.

Use: `«2610.05164v2».DualCertificate.Data.boundary_residual` uses this identity to establish
exact identity `D.calibration.stateResidual hκ D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ) (D.statePotential
κ) Y 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Residual.gaugePotential_d`,
`«2610.05164v2».DualCertificate.PolynomialPotential.raw_smooth`,
`«2610.05164v2».DualCertificate.PolynomialPotential.centering_c1` with the arguments shown in
the proof.
-/
theorem centered_d_endpoints {κ : ℝ} (hκ : 0<κ) {Y : State}
    (hq : Y.1=0 ∧ Y.2.1=0 ∧ Y.2.2.1=0 ∧ Y.2.2.2=0 ∨ Y.1=2) :
    dPotential (P.centered N hκ) Y=0 := by
  rw [centered,gaugePotential_d (P.raw_smooth.of_le (by simp)) (P.centering_c1 N hΓ hκ),
    P.raw_dPotential_endpoints hq]
  have hQ : Q Y.1=0 := by rcases hq with hq | hq <;> simp [Q,hq]
  rw [hQ,zero_mul,sub_zero]

end
end «2610.05164v2».DualCertificate.PolynomialPotential
