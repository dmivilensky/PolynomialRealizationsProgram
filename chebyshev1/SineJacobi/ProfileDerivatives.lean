import chebyshev1.SineJacobi.EllipticODE

/-!
Article: chebyshev1, Theorem E.3.
Profile Derivatives.
Use: `chebyshev1.SineJacobi.sineProfile₁_deriv` feeds
`chebyshev1.SineJacobi.sineProfile₃_deriv` (sine Profile₃ deriv).
Proof chain: `chebyshev1.SineJacobi.sineProfile_ode` — chebyshev1, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set

/--
Defines `profileWeight` of type `(t : ℝ)` by `Real.sqrt (sin (Real.pi*t))`.

Use: `chebyshev1.SineJacobi.profileWeight_deriv` rewrites with this definition to establish
the actual derivative at the stated point: `HasDerivAt profileWeight (profileWeight₁ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def profileWeight (t : ℝ) := Real.sqrt (sin (Real.pi*t))
/--
Defines `profileWeight₁` of type `(t : ℝ)` by `Real.pi*cos (Real.pi*t)/(2*profileWeight t)`.

Use: `chebyshev1.SineJacobi.profileWeight_deriv` rewrites with this definition to establish
the actual derivative at the stated point: `HasDerivAt profileWeight (profileWeight₁ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def profileWeight₁ (t : ℝ) := Real.pi*cos (Real.pi*t)/(2*profileWeight t)
/--
Defines `profileWeight₂` of type `(t : ℝ)` by `-Real.pi^2*sin (Real.pi*t)/(2*profileWeight t) -
Real.pi^2*cos (Real.pi*t)^2/(4*profileWeight t^3)`.

Use: `chebyshev1.SineJacobi.profileWeight₁_deriv` rewrites with this definition to
establish the actual derivative at the stated point: `HasDerivAt profileWeight₁ (profileWeight₂
t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def profileWeight₂ (t : ℝ) :=
  -Real.pi^2*sin (Real.pi*t)/(2*profileWeight t) -
    Real.pi^2*cos (Real.pi*t)^2/(4*profileWeight t^3)
/--
Defines `profileModulus` of type `(t : ℝ)` by `sin (Real.pi*t/2)`.

Use: `chebyshev1.SineJacobi.profileElliptic` uses this definition in the displayed
construction of `profileElliptic`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def profileModulus (t : ℝ) := sin (Real.pi*t/2)
/--
Defines `profileModulus₁` of type `(t : ℝ)` by `(Real.pi/2)*cos (Real.pi*t/2)`.

Use: `chebyshev1.SineJacobi.profileElliptic₁` uses this definition in the displayed
construction of `profileElliptic₁`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def profileModulus₁ (t : ℝ) := (Real.pi/2)*cos (Real.pi*t/2)
/--
Defines `profileModulus₂` of type `(t : ℝ)` by `-(Real.pi^2/4)*sin (Real.pi*t/2)`.

Use: `chebyshev1.SineJacobi.profileElliptic₂` uses this definition in the displayed
construction of `profileElliptic₂`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def profileModulus₂ (t : ℝ) := -(Real.pi^2/4)*sin (Real.pi*t/2)
/--
Defines `profileElliptic` of type `(t : ℝ)` by `ellipticK (profileModulus t)`.

Use: `chebyshev1.SineJacobi.sineProfile_deriv` rewrites with this definition to establish
the actual derivative at the stated point: `HasDerivAt sineProfile (sineProfile₁ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def profileElliptic (t : ℝ) := ellipticK (profileModulus t)
/--
Defines `profileElliptic₁` of type `(t : ℝ)` by `ellipticK₁ (profileModulus t)*profileModulus₁
t`.

Use: `chebyshev1.SineJacobi.sineProfile₁` uses this definition in the displayed
construction of `sineProfile₁`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def profileElliptic₁ (t : ℝ) := ellipticK₁ (profileModulus t)*profileModulus₁ t
/--
Defines `profileElliptic₂` of type `(t : ℝ)` by `ellipticK₂ (profileModulus t)*profileModulus₁
t^2 + ellipticK₁ (profileModulus t)*profileModulus₂ t`.

Use: `chebyshev1.SineJacobi.profileElliptic₁_deriv` rewrites with this definition to
establish the actual derivative at the stated point: `HasDerivAt profileElliptic₁
(profileElliptic₂ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def profileElliptic₂ (t : ℝ) :=
  ellipticK₂ (profileModulus t)*profileModulus₁ t^2 +
    ellipticK₁ (profileModulus t)*profileModulus₂ t
/--
Defines `sineProfile₁` of type `(t : ℝ)` by `(2/(Real.pi*Real.sqrt Real.pi))* (profileWeight₁
t*profileElliptic t+profileWeight t*profileElliptic₁ t)`.

Use: `chebyshev1.SineJacobi.sineProfile_deriv` uses this definition to establish the actual
derivative at the stated point: `HasDerivAt sineProfile (sineProfile₁ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def sineProfile₁ (t : ℝ) := (2/(Real.pi*Real.sqrt Real.pi))*
  (profileWeight₁ t*profileElliptic t+profileWeight t*profileElliptic₁ t)
/--
Defines `sineProfile₂` of type `(t : ℝ)` by `(2/(Real.pi*Real.sqrt Real.pi))* (profileWeight₂
t*profileElliptic t+2*profileWeight₁ t*profileElliptic₁ t+ profileWeight t*profileElliptic₂
t)`.

Use: `chebyshev1.SineJacobi.sineProfile₁_deriv` rewrites with this definition to establish
the actual derivative at the stated point: `HasDerivAt sineProfile₁ (sineProfile₂ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.
-/
def sineProfile₂ (t : ℝ) := (2/(Real.pi*Real.sqrt Real.pi))*
  (profileWeight₂ t*profileElliptic t+2*profileWeight₁ t*profileElliptic₁ t+
    profileWeight t*profileElliptic₂ t)

/--
The stated quantitative bound `0 < profileWeight t`.

Use: `chebyshev1.SineJacobi.profileWeight_deriv` uses this bound to establish the actual
derivative at the stated point: `HasDerivAt profileWeight (profileWeight₁ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem profileWeight_pos {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : 0 < profileWeight t := by
  apply Real.sqrt_pos.mpr
  exact sin_pos_of_mem_Ioo ⟨mul_pos pi_pos ht.1, by nlinarith [pi_pos, ht.2]⟩

/--
The stated quantitative bound `|profileModulus t| < 1`.

Use: `chebyshev1.SineJacobi.profileElliptic_deriv` uses this bound to establish the actual
derivative at the stated point: `HasDerivAt profileElliptic (profileElliptic₁ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem profileModulus_lt_one {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : |profileModulus t| < 1 := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hh : Real.pi*t/2 ∈ Ioo (0:ℝ) (Real.pi/2) :=
    ⟨half_pos (mul_pos pi_pos ht.1), by nlinarith [pi_pos, ht.2]⟩
  unfold profileModulus
  rw [abs_of_pos (sin_pos_of_mem_Ioo
    ⟨hh.1, hh.2.trans (by linarith [pi_pos] : Real.pi/2 < Real.pi)⟩)]
  have hb := strictMonoOn_sin
    (show Real.pi*t/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [pi_pos, hh.1, hh.2])
    (show Real.pi/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [pi_pos]) hh.2
  simpa using hb

/--
The actual derivative at the stated point: `HasDerivAt profileModulus (profileModulus₁ t) t`.

Use: `chebyshev1.SineJacobi.profileElliptic_deriv` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt profileElliptic
(profileElliptic₁ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem profileModulus_deriv (t : ℝ) :
    HasDerivAt profileModulus (profileModulus₁ t) t := by
  convert (((hasDerivAt_id t).const_mul Real.pi).div_const 2).sin using 1
  · funext u; simp [profileModulus]
  · simp [profileModulus₁]; ring

/--
The actual derivative at the stated point: `HasDerivAt profileModulus₁ (profileModulus₂ t) t`.

Use: `chebyshev1.SineJacobi.profileElliptic₁_deriv` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt profileElliptic₁
(profileElliptic₂ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem profileModulus₁_deriv (t : ℝ) :
    HasDerivAt profileModulus₁ (profileModulus₂ t) t := by
  convert ((((hasDerivAt_id t).const_mul Real.pi).div_const 2).cos.const_mul (Real.pi/2)) using 1
  · funext u; simp [profileModulus₁]
  · simp [profileModulus₂]; ring

/--
The actual derivative at the stated point: `HasDerivAt profileWeight (profileWeight₁ t) t`.

Use: `chebyshev1.SineJacobi.profileWeight₁_deriv` uses this derivative formula to establish
the actual derivative at the stated point: `HasDerivAt profileWeight₁ (profileWeight₂ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem profileWeight_deriv {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt profileWeight (profileWeight₁ t) t := by
  have hp : sin (Real.pi*t) ≠ 0 := (Real.sqrt_pos.mp (profileWeight_pos ht)).ne'
  convert (((hasDerivAt_id t).const_mul Real.pi).sin.sqrt hp) using 1
  · funext u; simp [profileWeight]
  · simp [profileWeight₁, profileWeight]; ring

/--
The actual derivative at the stated point: `HasDerivAt profileWeight₁ (profileWeight₂ t) t`.

Use: `chebyshev1.SineJacobi.sineProfile₁_deriv` uses this derivative formula to establish
the actual derivative at the stated point: `HasDerivAt sineProfile₁ (sineProfile₂ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem profileWeight₁_deriv {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt profileWeight₁ (profileWeight₂ t) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hw := profileWeight_deriv ht
  have hs := (profileWeight_pos ht).ne'
  have hd := ((((hasDerivAt_id t).const_mul Real.pi).cos.const_mul Real.pi)).div
    (hw.const_mul 2) (mul_ne_zero (by norm_num) hs)
  convert hd using 1
  · funext u; simp [profileWeight₁]
  · simp only [profileWeight₂, profileWeight₁, id_eq]
    generalize profileWeight t = w at hs ⊢
    field_simp [hs]
    ring

/--
The actual derivative at the stated point: `HasDerivAt profileElliptic (profileElliptic₁ t) t`.

Use: `chebyshev1.SineJacobi.sineProfile_deriv` uses this derivative formula to establish
the actual derivative at the stated point: `HasDerivAt sineProfile (sineProfile₁ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.ellipticK_deriv`,
`chebyshev1.SineJacobi.profileModulus_lt_one`,
`chebyshev1.SineJacobi.profileModulus_deriv` with the arguments shown in the proof.
-/
theorem profileElliptic_deriv {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt profileElliptic (profileElliptic₁ t) t :=
  (ellipticK_deriv (profileModulus_lt_one ht)).comp t (profileModulus_deriv t)

/--
The actual derivative at the stated point: `HasDerivAt profileElliptic₁ (profileElliptic₂ t)
t`.

Use: `chebyshev1.SineJacobi.sineProfile₁_deriv` uses this derivative formula to establish
the actual derivative at the stated point: `HasDerivAt sineProfile₁ (sineProfile₂ t) t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.ellipticK₁_deriv`,
`chebyshev1.SineJacobi.profileModulus_lt_one`,
`chebyshev1.SineJacobi.profileModulus_deriv` with the arguments shown in the proof.
-/
theorem profileElliptic₁_deriv {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt profileElliptic₁ (profileElliptic₂ t) t := by
  have hd := ((ellipticK₁_deriv (profileModulus_lt_one ht)).comp t
    (profileModulus_deriv t)).mul (profileModulus₁_deriv t)
  convert hd using 1
  · rfl
  · simp only [profileElliptic₂, Function.comp_def]; ring

/--
The actual derivative at the stated point: `HasDerivAt sineProfile (sineProfile₁ t) t`.

Use: `chebyshev1.SineJacobi.endpointProfile_locallyUniform` uses this derivative formula to
establish the precise assertion is `TendstoLocallyUniformlyOn endpointProfile sineProfile atTop
(Ioo (0:ℝ) 1)`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sineProfile_deriv {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt sineProfile (sineProfile₁ t) t := by
  have hd := ((profileWeight_deriv ht).mul (profileElliptic_deriv ht)).const_mul
    (2/(Real.pi*Real.sqrt Real.pi))
  convert hd using 1
  · funext u; simp only [sineProfile, profileWeight, profileElliptic, profileModulus, Pi.mul_apply]; ring
  · rfl

/--
The actual derivative at the stated point: `HasDerivAt sineProfile₁ (sineProfile₂ t) t`.

Use: `chebyshev1.SineJacobi.profileDerivative_eq` uses this derivative formula to establish
exact identity `iteratedDeriv n sineProfile t = profileDerivative n t`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.profileWeight₁_deriv`,
`chebyshev1.SineJacobi.profileElliptic_deriv`,
`chebyshev1.SineJacobi.profileWeight_deriv` with the arguments shown in the proof.
-/
theorem sineProfile₁_deriv {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt sineProfile₁ (sineProfile₂ t) t := by
  have hd := (((profileWeight₁_deriv ht).mul (profileElliptic_deriv ht)).add
    ((profileWeight_deriv ht).mul (profileElliptic₁_deriv ht))).const_mul
      (2/(Real.pi*Real.sqrt Real.pi))
  convert hd using 1
  · rfl
  · simp only [sineProfile₂]; ring

end
end chebyshev1.SineJacobi
