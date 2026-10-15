import «2610.05164v2».DualCertificate.FlatPotential
import «2610.05164v2».DualCertificate.ReflectedFilters

/-!
Article: 2610.05164v2, Theorem 3.6.
The normalized raw polynomial-potential coefficients on both closed sides.
Use: `«2610.05164v2».DualCertificate.PolynomialPotential.comparisonC_joint_continuous` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_joint_continuous` (certificate B
joint continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate.PolynomialPotential
noncomputable section
open Set «2610.05164v2».Residual
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (P : «2610.05164v2».DualCertificate.PolynomialPotential)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × State => P.flatB p.1 p.2) (Ioi
(0:ℝ) ×ˢ univ)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.normalizedB_smooth` uses this identity
to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State =>
P.normalizedB N side p.1 p.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) CoefficientDomain`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem flatB_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × State => P.flatB p.1 p.2)
    (Ioi (0:ℝ) ×ˢ univ) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hp (A : Polynomial ℚ) : ContDiffOn ℝ ∞ (fun p : ℝ × State => A.aeval p.2.1)
      (Ioi (0:ℝ) ×ˢ univ) :=
    (A.contDiff_aeval ∞).contDiffOn.comp (contDiffOn_fst.comp contDiffOn_snd
      (fun _ _ => mem_univ _)) (fun _ _ => mem_univ _)
  have hi : ∀ p∈Ioi (0:ℝ) ×ˢ (univ : Set State), p.1≠0 := fun _ hp => hp.1.ne'
  unfold flatB flatQ flatInner flatU0 flatU1
  fun_prop (disch := aesop)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × State => P.flatD p.1 p.2) (Ioi
(0:ℝ) ×ˢ univ)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.normalizedC_smooth` uses this identity
to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State =>
P.normalizedC N side p.1 p.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) CoefficientDomain`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem flatD_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × State => P.flatD p.1 p.2)
    (Ioi (0:ℝ) ×ˢ univ) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hp (A : Polynomial ℚ) : ContDiffOn ℝ ∞ (fun p : ℝ × State => A.aeval p.2.1)
      (Ioi (0:ℝ) ×ˢ univ) :=
    (A.contDiff_aeval ∞).contDiffOn.comp (contDiffOn_fst.comp contDiffOn_snd
      (fun _ _ => mem_univ _)) (fun _ _ => mem_univ _)
  have hi : ∀ p∈Ioi (0:ℝ) ×ˢ (univ : Set State), p.1≠0 := fun _ hp => hp.1.ne'
  unfold flatD flatQ flatInner flatU0 flatU1 «2610.05164v2».Calibration.Q
  fun_prop (disch := aesop)

/--
Defines `normalizedB` of type `ℝ` by `-t^2*(2-t^3)*P.flatB κ (side.q t,U₀,U₁,θ)/N.root κ t`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.normalizedB_identity` uses this
definition to establish `P.normalizedB N side κ t U₀ U₁ θ= -bPotential
κ P.raw (unnormalize κ (side.q t,U₀,U₁,θ))/(t*N.root κ t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def normalizedB (N : NormalizedCalibration) (side : Side) (κ t U₀ U₁ θ : ℝ) : ℝ :=
  -t^2*(2-t^3)*P.flatB κ (side.q t,U₀,U₁,θ)/N.root κ t

/--
Defines `normalizedC` of type `ℝ` by `(2-t^3)/(N.root κ t)^3* (t^2*(N.root κ t)^2*P.flatB κ
(side.q t,U₀,U₁,θ)-P.flatD κ (side.q t,U₀,U₁,θ))`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.comparisonC` uses this definition in
the displayed construction of `comparisonC`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def normalizedC (N : NormalizedCalibration) (side : Side) (κ t U₀ U₁ θ : ℝ) : ℝ :=
  (2-t^3)/(N.root κ t)^3*
    (t^2*(N.root κ t)^2*P.flatB κ (side.q t,U₀,U₁,θ)-P.flatD κ (side.q t,U₀,U₁,θ))

/--
The precise assertion is `P.normalizedB N side κ t U₀ U₁ θ= -bPotential κ P.raw (unnormalize κ
(side.q t,U₀,U₁,θ))/(t*N.root κ t)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centeredB_identity` rewrites with this
identity to establish `P.centeredB N side hκ t U₀ U₁ θ= -bPotential κ
(P.centered N hκ) (unnormalize κ (side.q t,U₀,U₁,θ))/(t*N.root κ t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalizedB_identity (N : NormalizedCalibration) (side : Side)
    {κ t : ℝ} (hκ : 0<κ) (ht : t∈Ioc (0:ℝ) 1) (U₀ U₁ θ : ℝ) :
    P.normalizedB N side κ t U₀ U₁ θ=
      -bPotential κ P.raw (unnormalize κ (side.q t,U₀,U₁,θ))/(t*N.root κ t) := by
  rw [P.raw_b_factor,side.Q]
  unfold normalizedB
  field_simp [ht.1.ne',(N.root_spec hκ ⟨ht.1.le,ht.2⟩).1.ne']

/--
The precise assertion is `P.normalizedC N side κ t U₀ U₁ θ= (bPotential κ P.raw (unnormalize κ
(side.q t,U₀,U₁,θ))*(t*N.root κ t)^2- dPotential P.raw (unnormalize κ (side.q
t,U₀,U₁,θ)))/(t*N.root κ t)^3`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centeredC_identity` rewrites with this
identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalizedC_identity (N : NormalizedCalibration) (side : Side)
    {κ t : ℝ} (hκ : 0<κ) (ht : t∈Ioc (0:ℝ) 1) (U₀ U₁ θ : ℝ) :
    P.normalizedC N side κ t U₀ U₁ θ=
      (bPotential κ P.raw (unnormalize κ (side.q t,U₀,U₁,θ))*(t*N.root κ t)^2-
        dPotential P.raw (unnormalize κ (side.q t,U₀,U₁,θ)))/(t*N.root κ t)^3 := by
  rw [P.raw_b_factor,P.raw_d_factor,side.Q]
  unfold normalizedC
  field_simp [ht.1.ne',(N.root_spec hκ ⟨ht.1.le,ht.2⟩).1.ne']

/--
Defines `CoefficientDomain` of type `Set (ℝ × ℝ × State)` by `Ioi (0:ℝ) ×ˢ (Icc (0:ℝ) 1 ×ˢ
univ)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.normalizedB_smooth` uses this
definition to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State
=> P.normalizedB N side p.1 p.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) CoefficientDomain`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
abbrev CoefficientDomain : Set (ℝ × ℝ × State) :=
  Ioi (0:ℝ) ×ˢ (Icc (0:ℝ) 1 ×ˢ univ)

 /--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State => P.normalizedB N side
p.1 p.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) CoefficientDomain`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_joint_continuous` uses
this identity to establish continuity of the displayed function: `Continuous (fun p :
CoefficientBox => N.certificateB P side p.1.property ξ₀ ξ₁ χ τ p.2.1 p.2.2.1 p.2.2.2.1
p.2.2.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth`,
`«2610.05164v2».DualCertificate.PolynomialPotential.flatB_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_spec` with the arguments shown in
the proof.
-/
theorem normalizedB_smooth (N : NormalizedCalibration) (side : Side) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State =>
      P.normalizedB N side p.1 p.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) CoefficientDomain := by
  -- Use the identities/estimates
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth`,
  -- `«2610.05164v2».DualCertificate.PolynomialPotential.flatB_smooth`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.root_spec` with the arguments shown
  -- in the proof.
  have hr : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State => N.root p.1 p.2.1) CoefficientDomain :=
    N.root_smooth.comp (contDiffOn_fst.prodMk (contDiffOn_fst.comp contDiffOn_snd
      (fun _ hp => hp.2))) (fun _ hp => ⟨hp.1,hp.2.1⟩)
  have hq : ContDiff ℝ ∞ side.q := by cases side <;> unfold Side.q <;> fun_prop
  have hb : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State =>
      P.flatB p.1 (side.q p.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2)) CoefficientDomain := by
    exact P.flatB_smooth.comp (f := fun p : ℝ × ℝ × State =>
      (p.1,(side.q p.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2)))
      (by fun_prop) (fun _ hp => ⟨hp.1,mem_univ _⟩)
  unfold normalizedB
  apply ContDiffOn.div _ hr (fun _ hp => (N.root_spec hp.1 hp.2.1).1.ne')
  fun_prop

 /--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State => P.normalizedC N side
p.1 p.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) CoefficientDomain`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.comparisonC_joint_continuous` uses
this identity to establish continuity of the displayed function: `Continuous (fun p :
NormalizedCalibration.ParameterDomain => P.comparisonC N side p.1.property p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth`,
`«2610.05164v2».DualCertificate.PolynomialPotential.flatB_smooth`,
`«2610.05164v2».DualCertificate.PolynomialPotential.flatD_smooth` with the arguments shown in
the proof.
-/
theorem normalizedC_smooth (N : NormalizedCalibration) (side : Side) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State =>
      P.normalizedC N side p.1 p.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) CoefficientDomain := by
  -- Use the identities/estimates
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth`,
  -- `«2610.05164v2».DualCertificate.PolynomialPotential.flatB_smooth`,
  -- `«2610.05164v2».DualCertificate.PolynomialPotential.flatD_smooth` with the arguments shown
  -- in the proof.
  have hr : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State => N.root p.1 p.2.1) CoefficientDomain :=
    N.root_smooth.comp (contDiffOn_fst.prodMk (contDiffOn_fst.comp contDiffOn_snd
      (fun _ hp => hp.2))) (fun _ hp => ⟨hp.1,hp.2.1⟩)
  have hq : ContDiff ℝ ∞ side.q := by cases side <;> unfold Side.q <;> fun_prop
  have hb : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State =>
      P.flatB p.1 (side.q p.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2)) CoefficientDomain := by
    exact P.flatB_smooth.comp (f := fun p : ℝ × ℝ × State =>
      (p.1,(side.q p.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2)))
      (by fun_prop) (fun _ hp => ⟨hp.1,mem_univ _⟩)
  have hd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × State =>
      P.flatD p.1 (side.q p.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2)) CoefficientDomain := by
    exact P.flatD_smooth.comp (f := fun p : ℝ × ℝ × State =>
      (p.1,(side.q p.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2)))
      (by fun_prop) (fun _ hp => ⟨hp.1,mem_univ _⟩)
  unfold normalizedC
  exact (contDiffOn_const.sub ((contDiffOn_fst.comp contDiffOn_snd
    (fun _ hp => hp.2)).pow 3) |>.div (hr.pow 3)
      (fun _ hp => pow_ne_zero _ (N.root_spec hp.1 hp.2.1).1.ne')).mul
    (((contDiffOn_fst.comp contDiffOn_snd (fun _ hp => hp.2)).pow 2 |>.mul (hr.pow 2)).mul hb |>.sub hd)

 /--
Defines `comparisonC` of type `ℝ` by `P.normalizedC N side κ t (N.U side hκ 32 t) (N.U side hκ
64 t) (N.theta side hκ t)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.comparisonC_joint_continuous` uses
this definition to establish continuity of the displayed function: `Continuous (fun p :
NormalizedCalibration.ParameterDomain => P.comparisonC N side p.1.property p.2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def comparisonC (N : NormalizedCalibration) (side : Side) {κ : ℝ} (hκ : 0<κ) (t : ℝ) : ℝ :=
  P.normalizedC N side κ t (N.U side hκ 32 t) (N.U side hκ 64 t) (N.theta side hκ t)

 /--
Continuity of the displayed function: `Continuous (fun p :
NormalizedCalibration.ParameterDomain => P.comparisonC N side p.1.property p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.centeredC_joint_continuous` uses
this continuity result to establish continuity of the displayed function: `Continuous (fun p :
CoefficientBox => P.centeredC N side p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.normalizedC_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.U_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.theta_joint_continuous` with the
arguments shown in the proof.
-/
theorem comparisonC_joint_continuous (N : NormalizedCalibration) (side : Side) :
    Continuous (fun p : NormalizedCalibration.ParameterDomain => P.comparisonC N side p.1.property p.2) := by
  -- Establish continuity hk before using the function at limits or in calculus arguments.
  have hk : Continuous (fun p : NormalizedCalibration.ParameterDomain => (p.1:ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  -- Establish continuity ht before using the function at limits or in calculus arguments.
  have ht : Continuous (fun p : NormalizedCalibration.ParameterDomain => (p.2:ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  apply (P.normalizedC_smooth N side).continuousOn.comp_continuous
    (hk.prodMk (ht.prodMk ((continuous_const (y := (0:ℝ))).prodMk
      ((N.U_joint_continuous side (by norm_num : (0:ℝ)<32)).prodMk
        ((N.U_joint_continuous side (by norm_num : (0:ℝ)<64)).prodMk
          (N.theta_joint_continuous side))))))
  exact fun p => ⟨p.1.property,p.2.property,mem_univ _⟩

end
end «2610.05164v2».DualCertificate.PolynomialPotential
