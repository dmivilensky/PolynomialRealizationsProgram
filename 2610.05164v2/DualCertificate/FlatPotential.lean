import «2610.05164v2».DualCertificate.TermDerivatives

/-!
Article: 2610.05164v2, Lemma 16.
A factorization of the actual polynomial-potential gradient by Q(q).
Use: `«2610.05164v2».DualCertificate.PolynomialPotential.raw_d_factor` feeds
`«2610.05164v2».DualCertificate.PolynomialPotential.normalizedC_identity` (normalized C identity).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate.PolynomialPotential
noncomputable section
open «2610.05164v2».Residual «2610.05164v2».Calibration Polynomial
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (P : «2610.05164v2».DualCertificate.PolynomialPotential)

/--
Z contains (q,U0,U1,theta), and this is its original article state.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.raw_b_factor` uses this definition to
establish exact identity `bPotential κ P.raw (unnormalize κ Z)=«2610.05164v2».Calibration.Q
Z.1*P.flatB κ Z`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def unnormalize (κ : ℝ) (Z : State) : State :=
  (Z.1,Z.1*Z.2.1/κ,Z.1*Z.2.2.1/κ,Z.1*Z.2.2.2)

/--
Defines `flatInner` of type `ℝ` by `P.Ph.aeval Z.1*Z.2.2.2+Z.1*(P.P₀.aeval Z.1*(Z.2.1/κ)+
P.P₁.aeval Z.1*(Z.2.2.1/κ)+P.P₀₀.aeval Z.1*(Z.2.1/κ)^2+ P.P₀₁.aeval
Z.1*(Z.2.1/κ)*(Z.2.2.1/κ)+P.P₁₁.aeval Z.1*(Z.2.2.1/κ)^2)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.flatQ` uses this definition in the
displayed construction of `flatQ`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def flatInner (κ : ℝ) (Z : State) : ℝ :=
  P.Ph.aeval Z.1*Z.2.2.2+Z.1*(P.P₀.aeval Z.1*(Z.2.1/κ)+
    P.P₁.aeval Z.1*(Z.2.2.1/κ)+P.P₀₀.aeval Z.1*(Z.2.1/κ)^2+
    P.P₀₁.aeval Z.1*(Z.2.1/κ)*(Z.2.2.1/κ)+P.P₁₁.aeval Z.1*(Z.2.2.1/κ)^2)

/--
Defines `flatQ` of type `ℝ`. The displayed construction fixes its component data; its proof
fields enforce the listed compatibility properties.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.flatB` uses this definition in the
displayed construction of `flatB`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def flatQ (κ : ℝ) (Z : State) : ℝ := -2*P.flatInner κ Z+(2-Z.1)*
  (P.Ph.derivative.aeval Z.1*Z.2.2.2+
    (P.P₀.aeval Z.1+Z.1*P.P₀.derivative.aeval Z.1)*(Z.2.1/κ)+
    (P.P₁.aeval Z.1+Z.1*P.P₁.derivative.aeval Z.1)*(Z.2.2.1/κ)+
    Z.1*P.P₀₀.derivative.aeval Z.1*(Z.2.1/κ)^2+
    Z.1*P.P₀₁.derivative.aeval Z.1*(Z.2.1/κ)*(Z.2.2.1/κ)+
    Z.1*P.P₁₁.derivative.aeval Z.1*(Z.2.2.1/κ)^2)

/--
Defines `flatU0` of type `ℝ` by `P.P₀.aeval Z.1+2*P.P₀₀.aeval Z.1*(Z.2.1/κ)+P.P₀₁.aeval
Z.1*(Z.2.2.1/κ)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.flatB` uses this definition in the
displayed construction of `flatB`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def flatU0 (κ : ℝ) (Z : State) : ℝ :=
  P.P₀.aeval Z.1+2*P.P₀₀.aeval Z.1*(Z.2.1/κ)+P.P₀₁.aeval Z.1*(Z.2.2.1/κ)

/--
Defines `flatU1` of type `ℝ` by `P.P₁.aeval Z.1+P.P₀₁.aeval Z.1*(Z.2.1/κ)+2*P.P₁₁.aeval
Z.1*(Z.2.2.1/κ)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.flatB` uses this definition in the
displayed construction of `flatB`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def flatU1 (κ : ℝ) (Z : State) : ℝ :=
  P.P₁.aeval Z.1+P.P₀₁.aeval Z.1*(Z.2.1/κ)+2*P.P₁₁.aeval Z.1*(Z.2.2.1/κ)

/--
Defines `flatB` of type `ℝ` by `κ*P.flatQ κ Z+(2-Z.1)*(P.flatU0 κ Z+P.flatU1 κ Z)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.raw_b_factor` uses this definition to
establish exact identity `bPotential κ P.raw (unnormalize κ Z)=«2610.05164v2».Calibration.Q
Z.1*P.flatB κ Z`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def flatB (κ : ℝ) (Z : State) : ℝ :=
  κ*P.flatQ κ Z+(2-Z.1)*(P.flatU0 κ Z+P.flatU1 κ Z)

/--
Defines `flatD` of type `ℝ` by `«2610.05164v2».Calibration.Q Z.1*P.flatQ κ Z+
«2610.05164v2».Calibration.Q Z.1*P.flatU0 κ Z*(2*(Z.2.1/κ)+32*Z.1*(Z.2.1/κ)^2)+
«2610.05164v2».Calibration.Q Z.1*P.flatU1 κ Z*(2*(Z.2.2.1/κ)+64*Z.1*(Z.2.2.1/κ)^2)+
(2-Z.1)*P.Ph.aeval Z.1*(2*Z.2.2.2-Z.1)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.raw_d_factor` uses this definition to
establish exact identity `dPotential P.raw (unnormalize κ Z)=«2610.05164v2».Calibration.Q
Z.1*P.flatD κ Z`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def flatD (κ : ℝ) (Z : State) : ℝ :=
  «2610.05164v2».Calibration.Q Z.1*P.flatQ κ Z+
    «2610.05164v2».Calibration.Q Z.1*P.flatU0 κ Z*(2*(Z.2.1/κ)+32*Z.1*(Z.2.1/κ)^2)+
    «2610.05164v2».Calibration.Q Z.1*P.flatU1 κ Z*(2*(Z.2.2.1/κ)+64*Z.1*(Z.2.2.1/κ)^2)+
    (2-Z.1)*P.Ph.aeval Z.1*(2*Z.2.2.2-Z.1)

/--
Exact identity `bPotential κ P.raw (unnormalize κ Z)=«2610.05164v2».Calibration.Q Z.1*P.flatB κ
Z`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.normalizedB_identity` rewrites with
this identity to establish `P.normalizedB N side κ t U₀ U₁ θ=
-bPotential κ P.raw (unnormalize κ (side.q t,U₀,U₁,θ))/(t*N.root κ t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.raw_fderiv` with the arguments shown in the
proof.
-/
theorem raw_b_factor (κ : ℝ) (Z : State) :
    bPotential κ P.raw (unnormalize κ Z)=«2610.05164v2».Calibration.Q Z.1*P.flatB κ Z := by
  rw [bPotential,P.raw_fderiv]
  norm_num [Fin.sum_univ_succ,coefficient,derivative_mul,derivative_pow,
    atom,atomDifferential,unnormalize,inputVector]
  unfold flatB flatQ flatInner flatU0 flatU1 «2610.05164v2».Calibration.Q
  simp only [div_eq_mul_inv]
  ring

/--
Exact identity `dPotential P.raw (unnormalize κ Z)=«2610.05164v2».Calibration.Q Z.1*P.flatD κ
Z`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.normalizedC_identity` rewrites with
this identity to establish `P.normalizedC N side κ t U₀ U₁ θ=
(bPotential κ P.raw (unnormalize κ (side.q t,U₀,U₁,θ))*(t*N.root κ t)^2- dPotential P.raw
(unnormalize κ (side.q t,U₀,U₁,θ)))/(t*N.root κ t)^3`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.raw_fderiv` with the arguments shown in the
proof.
-/
theorem raw_d_factor (κ : ℝ) (Z : State) :
    dPotential P.raw (unnormalize κ Z)=«2610.05164v2».Calibration.Q Z.1*P.flatD κ Z := by
  rw [dPotential,P.raw_fderiv]
  norm_num [Fin.sum_univ_succ,coefficient,derivative_mul,derivative_pow,
    atom,atomDifferential,unnormalize,driftVector]
  unfold flatD flatQ flatInner flatU0 flatU1 «2610.05164v2».Calibration.Q
  simp only [div_eq_mul_inv]
  ring

end
end «2610.05164v2».DualCertificate.PolynomialPotential
