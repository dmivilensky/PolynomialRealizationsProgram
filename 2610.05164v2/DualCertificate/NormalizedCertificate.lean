import «2610.05164v2».DualCertificate.NormalizedMultipliers
import «2610.05164v2».DualCertificate.NormalizedCriterion
import «2610.05164v2».Residual.SpectralBound

/-!
Article: 2610.05164v2, Lemma 16.
The complete normalized state criterion (50) for the actual centered potential and comparison
multipliers, together with its affine face reduction.
Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.actual_face_reduction` feeds
`«2610.05164v2».DualCertificate.Data.normalized_criterion_of_admissible` (normalized criterion of
admissible).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate.NormalizedCalibration
noncomputable section
open Set «2610.05164v2».Calibration «2610.05164v2».Residual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (N : «2610.05164v2».DualCertificate.NormalizedCalibration) (P : PolynomialPotential)

/--
Defines `certificateB` of type `ℝ` by `τ*(2-t^3)/(N.speed κ t*N.root κ t)+ ξ₀*N.determinantTerm
side hκ 32 t U₀+ξ₁*N.determinantTerm side hκ 64 t U₁+ χ*N.traceTerm side hκ t θ+P.centeredB N
side hκ t U₀ U₁ θ`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_affine` uses this
definition to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def certificateB (side : Side) {κ : ℝ} (hκ : 0<κ) (ξ₀ ξ₁ χ τ t U₀ U₁ θ : ℝ) : ℝ :=
  τ*(2-t^3)/(N.speed κ t*N.root κ t)+
    ξ₀*N.determinantTerm side hκ 32 t U₀+ξ₁*N.determinantTerm side hκ 64 t U₁+
    χ*N.traceTerm side hκ t θ+P.centeredB N side hκ t U₀ U₁ θ

/--
Defines `certificateL` of type `ℝ` by `t*(2-t^3)/(κ*(N.root κ t)^2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateL_identity` uses this
definition to establish the identity `N.certificateL κ t=Q (side.q t)/(κ*(t*N.root κ t)^2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def certificateL (κ t : ℝ) : ℝ := t*(2-t^3)/(κ*(N.root κ t)^2)

variable (hΓ : ∀ q∈Icc (0:ℝ) 2,N.calibration.Gamma (2-q)=N.calibration.Gamma q)

include hΓ in
/--
The precise assertion is `N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ θ=
(N.calibration.stateComparisonMultiplier hκ ξ₀ ξ₁ χ (PolynomialPotential.unnormalize κ (side.q
t,U₀,U₁,θ))+ τ*Q (side.q t)/N.calibration.speed κ (side.q t)- bPotential κ (P.centered N hκ)
(PolynomialPotential.unnormalize κ (side.q t,U₀,U₁,θ)))/ (t*N.root κ t)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.actual_normalized_criterion`
rewrites with this identity to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem certificateB_identity (side : Side) {κ t U₀ U₁ : ℝ} (hκ : 0<κ)
    (ht : t∈Ioc (0:ℝ) 1) (h₀ : U₀∈Icc (0:ℝ) 1) (h₁ : U₁∈Icc (0:ℝ) 1)
    (ξ₀ ξ₁ χ τ θ : ℝ) :
    N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ θ=
      (N.calibration.stateComparisonMultiplier hκ ξ₀ ξ₁ χ
          (PolynomialPotential.unnormalize κ (side.q t,U₀,U₁,θ))+
        τ*Q (side.q t)/N.calibration.speed κ (side.q t)-
        bPotential κ (P.centered N hκ) (PolynomialPotential.unnormalize κ (side.q t,U₀,U₁,θ)))/
          (t*N.root κ t) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  unfold certificateB
  rw [N.determinantTerm_identity hΓ side hκ (by norm_num : (0:ℝ)<32) ht h₀,
    N.determinantTerm_identity hΓ side hκ (by norm_num : (0:ℝ)<64) ht h₁,
    N.traceTerm_identity hΓ side hκ ht,P.centeredB_identity N hΓ side hκ ht]
  have hτ : τ*(2-t^3)/(N.speed κ t*N.root κ t)=
      (τ*Q (side.q t)/N.calibration.speed κ (side.q t))/(t*N.root κ t) := by
    rw [N.side_speed hΓ side hκ ⟨ht.1.le,ht.2⟩,side.Q]
    field_simp [ht.1.ne',(N.root_spec hκ ⟨ht.1.le,ht.2⟩).1.ne',
      (N.speed_positive hκ ⟨ht.1.le,ht.2⟩).ne']
  rw [hτ]
  unfold «2610.05164v2».Calibration.Data.stateComparisonMultiplier PolynomialPotential.unnormalize
  dsimp only
  have h32 : (32:ℝ)*(side.q t*U₀/κ)=side.q t*(32/κ)*U₀ := by ring
  have h64 : (64:ℝ)*(side.q t*U₁/κ)=side.q t*(64/κ)*U₁ := by ring
  have hh : side.q t-side.q t*θ=side.q t*(1-θ) := by ring
  rw [h32,h64,hh]
  ring

 /--
Exact identity `N.certificateL κ t=Q (side.q t)/(κ*(t*N.root κ t)^2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.actual_normalized_criterion`
rewrites with this identity to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem certificateL_identity (side : Side) {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Ioc (0:ℝ) 1) :
    N.certificateL κ t=Q (side.q t)/(κ*(t*N.root κ t)^2) := by
  rw [side.Q]
  unfold certificateL
  field_simp [hκ.ne',ht.1.ne',(N.root_spec hκ ⟨ht.1.le,ht.2⟩).1.ne']

include hΓ in
/--
Equivalence of the displayed criteria: `(∀ n : ℝ,0≤n → 0≤residual κ (N.calibration.amplitude κ
(side.q t)) (Q (side.q t)) (N.calibration.stateComparisonMultiplier hκ ξ₀ ξ₁ χ
(PolynomialPotential.unnormalize κ (side.q t,U₀,U₁,θ))) (-τ*Q (side.q t)/N.calibration.speed κ
(side.q t)+N.calibration.amplitude κ (side.q t)*e) τ (bPotential κ (P.centered N hκ)
(PolynomialPotential.unnormalize κ (side.q t,U₀,U₁,θ))) (dPotential (P.centered N hκ)
(PolynomialPotential.unnormalize κ (side.q t,U₀,U₁,θ))) n) ↔ criterion (N.certificateB P side
hκ ξ₀ ξ₁ χ τ t U₀ U₁ θ) (P.centeredC N side hκ t U₀ U₁ θ) e (N.certificateL κ t)≤0`.

Use: `«2610.05164v2».DualCertificate.Data.normalized_residual_of_admissible` uses this bound to
establish establishes the uniform, quantified assertion `∀ n : ℝ,0≤n →
0≤D.calibration.stateResidual hκ D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ) (D.statePotential κ)
(PolynomialPotential.unnormalize κ (side.q t,U,V,θ)) n`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.side_amplitude`,
`«2610.05164v2».DualCertificate.normalized_residual_criterion`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_spec` with the arguments shown in
the proof.
-/
theorem actual_normalized_criterion (side : Side) {κ t U₀ U₁ : ℝ} (hκ : 0<κ)
    (ht : t∈Ioc (0:ℝ) 1) (h₀ : U₀∈Icc (0:ℝ) 1) (h₁ : U₁∈Icc (0:ℝ) 1)
    (ξ₀ ξ₁ χ τ θ e : ℝ) :
    (∀ n : ℝ,0≤n → 0≤residual κ (N.calibration.amplitude κ (side.q t)) (Q (side.q t))
      (N.calibration.stateComparisonMultiplier hκ ξ₀ ξ₁ χ
        (PolynomialPotential.unnormalize κ (side.q t,U₀,U₁,θ)))
      (-τ*Q (side.q t)/N.calibration.speed κ (side.q t)+N.calibration.amplitude κ (side.q t)*e) τ
      (bPotential κ (P.centered N hκ) (PolynomialPotential.unnormalize κ (side.q t,U₀,U₁,θ)))
      (dPotential (P.centered N hκ) (PolynomialPotential.unnormalize κ (side.q t,U₀,U₁,θ))) n) ↔
    criterion (N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ θ)
      (P.centeredC N side hκ t U₀ U₁ θ) e (N.certificateL κ t)≤0 := by
  -- Use the identities/estimates
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.side_amplitude`,
  -- `«2610.05164v2».DualCertificate.normalized_residual_criterion`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.root_spec` with the arguments shown
  -- in the proof.
  rw [N.side_amplitude hΓ side hκ ⟨ht.1.le,ht.2⟩]
  rw [normalized_residual_criterion hκ.ne' (mul_pos ht.1 (N.root_spec hκ ⟨ht.1.le,ht.2⟩).1)
    (N.calibration.speed_positive hκ (side.q_interior ht)).ne'
    (by rw [← N.side_amplitude hΓ side hκ ⟨ht.1.le,ht.2⟩];rfl)]
  rw [← N.certificateB_identity P hΓ side hκ ht h₀ h₁,
    ← P.centeredC_identity N hΓ side hκ ht,← N.certificateL_identity side hκ ht]

 /--
The precise assertion is `N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ θ= N.certificateB P side
hκ ξ₀ ξ₁ χ τ t U₀ U₁ 0+ (N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ 1- N.certificateB P side hκ
ξ₀ ξ₁ χ τ t U₀ U₁ 0)*θ`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.actual_face_reduction` rewrites with
this identity to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem certificateB_affine (side : Side) {κ : ℝ} (hκ : 0<κ)
    (ξ₀ ξ₁ χ τ t U₀ U₁ θ : ℝ) :
    N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ θ=
      N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ 0+
        (N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ 1-
          N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ 0)*θ := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  unfold certificateB traceTerm PolynomialPotential.centeredB PolynomialPotential.normalizedB
    PolynomialPotential.flatB PolynomialPotential.flatQ PolynomialPotential.flatInner
    PolynomialPotential.flatU0 PolynomialPotential.flatU1
  simp only [div_eq_mul_inv]
  ring

 /--
Exact identity `P.centeredC N side hκ t U₀ U₁ θ=P.centeredC N side hκ t U₀ U₁ 0+ (P.centeredC N
side hκ t U₀ U₁ 1-P.centeredC N side hκ t U₀ U₁ 0)*θ`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.actual_face_reduction` rewrites with
this identity to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem centeredC_affine (side : Side) {κ : ℝ} (hκ : 0<κ) (t U₀ U₁ θ : ℝ) :
    P.centeredC N side hκ t U₀ U₁ θ=P.centeredC N side hκ t U₀ U₁ 0+
      (P.centeredC N side hκ t U₀ U₁ 1-P.centeredC N side hκ t U₀ U₁ 0)*θ := by
  unfold PolynomialPotential.centeredC PolynomialPotential.normalizedC PolynomialPotential.flatB
    PolynomialPotential.flatD PolynomialPotential.flatQ PolynomialPotential.flatInner
    PolynomialPotential.flatU0 PolynomialPotential.flatU1
  simp only [div_eq_mul_inv]
  ring

 /--
The stated quantitative bound `criterion (N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ θ)
(P.centeredC N side hκ t U₀ U₁ θ) e (N.certificateL κ t) ≤ max (criterion (N.certificateB P
side hκ ξ₀ ξ₁ χ τ t U₀ U₁ lo) (P.centeredC N side hκ t U₀ U₁ lo) e (N.certificateL κ t))
(criterion (N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ hi) (P.centeredC N side hκ t U₀ U₁ hi) e
(N.certificateL κ t))`.

Use: `«2610.05164v2».DualCertificate.Data.normalized_criterion_of_admissible` uses this bound
to prove the bound `criterion (D.B side hκ t U V θ) (D.C side hκ t U V
θ) ((D.cells side).value t) (D.normalization.certificateL κ t)<0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_affine`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.centeredC_affine`,
`«2610.05164v2».DualCertificate.criterion_le_faces` with the arguments shown in the proof.
-/
theorem actual_face_reduction (side : Side) {κ : ℝ} (hκ : 0<κ)
    (ξ₀ ξ₁ χ τ t U₀ U₁ e lo hi θ : ℝ) (hθ : θ∈Icc lo hi) :
    criterion (N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ θ)
      (P.centeredC N side hκ t U₀ U₁ θ) e (N.certificateL κ t) ≤
    max (criterion (N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ lo)
      (P.centeredC N side hκ t U₀ U₁ lo) e (N.certificateL κ t))
      (criterion (N.certificateB P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ hi)
        (P.centeredC N side hκ t U₀ U₁ hi) e (N.certificateL κ t)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_affine`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.centeredC_affine`,
  -- `«2610.05164v2».DualCertificate.criterion_le_faces` with the arguments shown in the proof.
  rw [N.certificateB_affine P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ θ,
    N.centeredC_affine P side hκ t U₀ U₁ θ,
    N.certificateB_affine P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ lo,
    N.centeredC_affine P side hκ t U₀ U₁ lo,
    N.certificateB_affine P side hκ ξ₀ ξ₁ χ τ t U₀ U₁ hi,
    N.centeredC_affine P side hκ t U₀ U₁ hi]
  exact criterion_le_faces _ _ _ _ _ _ hθ

end
end «2610.05164v2».DualCertificate.NormalizedCalibration
