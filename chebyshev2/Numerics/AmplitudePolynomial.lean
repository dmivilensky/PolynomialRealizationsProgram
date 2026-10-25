import chebyshev2.Numerics.ContactActual
import chebyshev2.Numerics.WeightedCubicResidual

/-!
Article: chebyshev2, Section 4.1.
Amplitude Polynomial.
Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.cleared_error` feeds
`chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.check_sound` (check sound).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate
noncomputable section
open Set Polynomial chebyshev2.Calibration chebyshev2.DualCertificate
set_option autoImplicit false

namespace AmplitudeExpr
/--
Defines `H` of type `Expr` by `.input 0`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.amplitude` uses this definition
in the displayed construction of `amplitude`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def H : Expr := .input 0
/--
Defines `approx` of type `Expr` by `.input 1`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.quadratureResidual` uses this
definition in the displayed construction of `quadratureResidual`. Its inputs and component
formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def approx : Expr := .input 1
/--
Defines `t` of type `Expr` by `.input 2`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def t : Expr := .input 2
/--
Defines `pi` of type `Expr` by `.input 3`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.k` uses this definition in the
displayed construction of `k`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def pi : Expr := .input 3
/--
Defines `left` of type `Expr` by `.input 5`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.den` uses this definition in the
displayed construction of `den`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def left : Expr := .input 5
/--
Defines `right` of type `Expr` by `.input 6`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.den` uses this definition in the
displayed construction of `den`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def right : Expr := .input 6
/--
Defines `lit` of type `` by `ContactExpr.lit`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
abbrev lit := ContactExpr.lit
/--
Defines `sq` of type `` by `ContactExpr.sq`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.k` uses this definition in the
displayed construction of `k`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
abbrev sq := ContactExpr.sq
/--
Defines `cube` of type `` by `ContactExpr.cube`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
abbrev cube := ContactExpr.cube
/--
Defines `sub` of type `` by `ContactExpr.sub`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
abbrev sub := ContactExpr.sub
/--
Defines `Q` of type `Expr` by `.mul (cube t) (sub (lit 2) (cube t))`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.gammaNum` uses this definition
in the displayed construction of `gammaNum`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Q : Expr := .mul (cube t) (sub (lit 2) (cube t))
/--
Defines `k` of type `Expr` by `.mul (lit (1/4)) (sq pi)`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.k_value` rewrites with this
definition to establish the identity `k.value (values t π r l u c h g)=π^2/4`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def k : Expr := .mul (lit (1/4)) (sq pi)
/--
Defines `den` of type `Expr` by `.add (lit 2) (.mul (lit σ) (.add left right))`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.den_value` rewrites with this
definition to establish the identity `(den σ).value (values t π r l u c h g)=2+(σ:ℝ)*(l+u)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def den (σ : ℚ) : Expr := .add (lit 2) (.mul (lit σ) (.add left right))
/--
Defines `gammaNum` of type `Expr` by `sub (.mul Q (.add left right)) (.mul (lit 2) (.mul left
right))`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.rootResidual` uses this
definition in the displayed construction of `rootResidual`. Its inputs and component formulas
are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def gammaNum : Expr := sub (.mul Q (.add left right)) (.mul (lit 2) (.mul left right))
/--
Defines `amplitude` of type `Expr` by `.mul t H`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.rootResidual` uses this
definition in the displayed construction of `rootResidual`. Its inputs and component formulas
are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def amplitude : Expr := .mul t H
/--
Defines `rootResidual` of type `Expr` by `sub (.mul (den σ) (sub (sub (.mul k (cube amplitude))
(.mul (lit 3) (.mul Q amplitude))) (.mul (lit (2*b)) Q))) (.mul (.mul (lit (2*ω)) k)
gammaNum)`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.rootResidual_value` rewrites
with this definition to establish `(rootResidual σ b ω).value (values
t π r l u c h g)=
(2+(σ:ℝ)*(l+u))*((π^2/4)*(t*h)^3-3*(t^3*(2-t^3))*(t*h)-2*(b:ℝ)*(t^3*(2-t^3)))-
2*(ω:ℝ)*(π^2/4)*((t^3*(2-t^3))*(l+u)-2*l*u)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def rootResidual (σ b ω : ℚ) : Expr := sub
  (.mul (den σ) (sub (sub (.mul k (cube amplitude)) (.mul (lit 3) (.mul Q amplitude)))
    (.mul (lit (2*b)) Q))) (.mul (.mul (lit (2*ω)) k) gammaNum)
/--
Defines `quadratureResidual` of type `Expr` by `sub approx (.mul (lit 6) (.mul (cube t) H))`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.quadratureResidual_value`
rewrites with this definition to establish the identity `quadratureResidual.value (values t π
r l u c h g)=g-6*t^3*h`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def quadratureResidual : Expr := sub approx (.mul (lit 6) (.mul (cube t) H))
/--
Defines `values` by pattern matching with result type `Nat → ℝ`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudeExpr.den_value` rewrites with this
definition to establish the identity `(den σ).value (values t π r l u c h g)=2+(σ:ℝ)*(l+u)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def values (t π r l u c h g : ℝ) : Nat → ℝ
  | 0 => h
  | 1 => g
  | 2 => t
  | 3 => π
  | 4 => r
  | 5 => l
  | 6 => u
  | 7 => c
  | _ => 0

/--
Exact identity `(den σ).value (values t π r l u c h g)=2+(σ:ℝ)*(l+u)`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.check_sound` rewrites with
this identity to prove the bound `|6*t^2*(R.calibration (σ :=
(sigma:ℝ)) (b := (b:ℝ)) (ω := (omega:ℝ)) (by exact_mod_cast hσ) (by exact_mod_cast hb) (by
exact_mod_cast hω)).amplitude (Real.pi^2/4) (t^3)-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem den_value (σ : ℚ) (t π r l u c h g : ℝ) :
    (den σ).value (values t π r l u c h g)=2+(σ:ℝ)*(l+u) := by
  simp only [den,ContactExpr.lit,Expr.value,Expr.rational_value,values,left,right]
  norm_num
/--
Exact identity `k.value (values t π r l u c h g)=π^2/4`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.check_sound` rewrites with
this identity to prove the bound `|6*t^2*(R.calibration (σ :=
(sigma:ℝ)) (b := (b:ℝ)) (ω := (omega:ℝ)) (by exact_mod_cast hσ) (by exact_mod_cast hb) (by
exact_mod_cast hω)).amplitude (Real.pi^2/4) (t^3)-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem k_value (t π r l u c h g : ℝ) :
    k.value (values t π r l u c h g)=π^2/4 := by
  simp only [k,ContactExpr.lit,ContactExpr.sq,Expr.value,Expr.rational_value,values,pi]
  norm_num
  ring
/--
The precise assertion is `(rootResidual σ b ω).value (values t π r l u c h g)=
(2+(σ:ℝ)*(l+u))*((π^2/4)*(t*h)^3-3*(t^3*(2-t^3))*(t*h)-2*(b:ℝ)*(t^3*(2-t^3)))-
2*(ω:ℝ)*(π^2/4)*((t^3*(2-t^3))*(l+u)-2*l*u)`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.check_sound` rewrites with
this identity to prove the bound `|6*t^2*(R.calibration (σ :=
(sigma:ℝ)) (b := (b:ℝ)) (ω := (omega:ℝ)) (by exact_mod_cast hσ) (by exact_mod_cast hb) (by
exact_mod_cast hω)).amplitude (Real.pi^2/4) (t^3)-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem rootResidual_value (σ b ω : ℚ) (t π r l u c h g : ℝ) :
    (rootResidual σ b ω).value (values t π r l u c h g)=
      (2+(σ:ℝ)*(l+u))*((π^2/4)*(t*h)^3-3*(t^3*(2-t^3))*(t*h)-2*(b:ℝ)*(t^3*(2-t^3)))-
        2*(ω:ℝ)*(π^2/4)*((t^3*(2-t^3))*(l+u)-2*l*u) := by
  simp only [rootResidual,den,amplitude,gammaNum,Q,k,ContactExpr.lit,ContactExpr.sub,
    ContactExpr.sq,ContactExpr.cube,Expr.value,Expr.rational_value,values,H,AmplitudeExpr.t,pi,left,right]
  push_cast
  ring
/--
Exact identity `quadratureResidual.value (values t π r l u c h g)=g-6*t^3*h`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.check_sound` rewrites with
this identity to prove the bound `|6*t^2*(R.calibration (σ :=
(sigma:ℝ)) (b := (b:ℝ)) (ω := (omega:ℝ)) (by exact_mod_cast hσ) (by exact_mod_cast hb) (by
exact_mod_cast hω)).amplitude (Real.pi^2/4) (t^3)-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem quadratureResidual_value (t π r l u c h g : ℝ) :
    quadratureResidual.value (values t π r l u c h g)=g-6*t^3*h := by
  simp only [quadratureResidual,ContactExpr.sub,ContactExpr.cube,ContactExpr.sq,
    ContactExpr.lit,Expr.value,Expr.rational_value,values,H,AmplitudeExpr.t,approx]
  norm_num
  ring
end AmplitudeExpr

namespace AmplitudePolynomial
variable (R : ReferenceData) {σ b ω : ℝ} (hσ : 0<σ) (hb : 0<b) (hω : 0≤ω)

/--
The stated quantitative bound `|6*t^2*(R.calibration hσ hb hω).amplitude κ
(t^3)-6*t^3*h|≤24*er/κ`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.cleared_error` uses this
bound to prove the bound `|6*t^2*(R.calibration hσ hb hω).amplitude κ
(t^3)-g|≤24*er/(dl*kl)+eq`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem weighted_error {κ t h er : ℝ} (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1)
    (hH : (1/2:ℝ)≤h) (her : 0≤er)
    (he : |κ*(t*h)^3-3*Q (t^3)*(t*h)-(R.calibration hσ hb hω).constant κ (t^3)|≤er) :
    |6*t^2*(R.calibration hσ hb hω).amplitude κ (t^3)-6*t^3*h|≤24*er/κ := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hq : t^3∈Icc (0:ℝ) 2 := by
    have hc := cube_mem ht
    exact ⟨hc.1,hc.2.trans (by norm_num)⟩
  have hp : 0<t → 0<(R.calibration hσ hb hω).constant κ (t^3) ∧
      0<(R.calibration hσ hb hω).amplitude κ (t^3) := by
    intro htpos
    have hqi := Side.q_interior Side.left ⟨htpos,ht.2⟩
    exact ⟨(R.calibration hσ hb hω).constant_positive hκ hqi,
      ((R.calibration hσ hb hω).amplitude_spec hκ hqi).1⟩
  have herror := weighted_positive_cubic_residual_error (z := t*h) hκ (by norm_num : (0:ℝ)<1/2)
    ht.1 her hp ((R.calibration hσ hb hω).amplitude_equation hκ hq)
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hH ht.1) he
  have hid : 6*t^2*(R.calibration hσ hb hω).amplitude κ (t^3)-6*t^3*h=
      6*(t^2*((R.calibration hσ hb hω).amplitude κ (t^3)-t*h)) := by ring
  rw [hid,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<6)]
  calc
    6*|t^2*((R.calibration hσ hb hω).amplitude κ (t^3)-t*h)|≤6*(er/(κ*(1/2)^2)) :=
      mul_le_mul_of_nonneg_left herror (by norm_num)
    _=24*er/κ := by field_simp; ring

/--
The stated quantitative bound `|6*t^2*(R.calibration hσ hb hω).amplitude κ
(t^3)-g|≤24*er/(dl*kl)+eq`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.check_sound` uses this
bound to prove the bound `|6*t^2*(R.calibration (σ := (sigma:ℝ)) (b :=
(b:ℝ)) (ω := (omega:ℝ)) (by exact_mod_cast hσ) (by exact_mod_cast hb) (by exact_mod_cast
hω)).amplitude (Real.pi^2/4) (t^3)-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem cleared_error {κ kl t h g dl er eq : ℝ} (hκ : 0<κ) (hkl : 0<kl) (hk : kl≤κ)
    (ht : t∈Icc (0:ℝ) 1) (hH : (1/2:ℝ)≤h) (hdl : 0<dl)
    (hden : dl≤2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t))
    (her : 0≤er)
    (he : |(2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t))*
        (κ*(t*h)^3-3*Q (t^3)*(t*h)-2*b*Q (t^3))-
      2*ω*κ*(Q (t^3)*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)-
        2*R.normalizedFilter hσ t*R.normalizedReflectedFilter hσ t)|≤er)
    (hq : |g-6*t^3*h|≤eq) :
    |6*t^2*(R.calibration hσ hb hω).amplitude κ (t^3)-g|≤24*er/(dl*kl)+eq := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let d := 2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)
  let C := R.calibration hσ hb hω
  have hd : 0<d := hdl.trans_le hden
  have hGamma : C.Gamma (t^3)=
      (Q (t^3)*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)-
        2*R.normalizedFilter hσ t*R.normalizedReflectedFilter hσ t)/d := by
    rw [ReferenceData.calibration_Gamma_direct R hσ hb hω ht]
    rfl
  have hid : d*(κ*(t*h)^3-3*Q (t^3)*(t*h)-C.constant κ (t^3))=
      d*(κ*(t*h)^3-3*Q (t^3)*(t*h)-2*b*Q (t^3))-
      2*ω*κ*(Q (t^3)*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)-
        2*R.normalizedFilter hσ t*R.normalizedReflectedFilter hσ t) := by
    rw [Data.constant,hGamma]
    change d*(κ*(t*h)^3-3*Q (t^3)*(t*h)-
      (2*b*Q (t^3)+2*κ*ω*((Q (t^3)*(R.normalizedFilter hσ t+
        R.normalizedReflectedFilter hσ t)-2*R.normalizedFilter hσ t*
          R.normalizedReflectedFilter hσ t)/d)))=_
    field_simp [hd.ne']
    ring
  have hroot : |κ*(t*h)^3-3*Q (t^3)*(t*h)-C.constant κ (t^3)|≤er/dl := by
    have hh : d*|κ*(t*h)^3-3*Q (t^3)*(t*h)-C.constant κ (t^3)|≤er := by
      rw [← abs_of_pos hd,← abs_mul,hid]
      exact he
    rw [le_div_iff₀ hdl]
    nlinarith [mul_le_mul_of_nonneg_right hden
      (abs_nonneg (κ*(t*h)^3-3*Q (t^3)*(t*h)-C.constant κ (t^3)))]
  have hw := weighted_error R hσ hb hω hκ ht hH (div_nonneg her hdl.le) hroot
  have hbudget : 24*(er/dl)/κ≤24*er/(dl*kl) := by
    have hh := div_le_div_of_nonneg_left (show 0≤24*(er/dl) by positivity) hkl hk
    calc
      24*(er/dl)/κ≤24*(er/dl)/kl := hh
      _=24*er/(dl*kl) := by ring
  have hid' : 6*t^2*C.amplitude κ (t^3)-g=
      (6*t^2*C.amplitude κ (t^3)-6*t^3*h)-(g-6*t^3*h) := by ring
  rw [hid']
  exact (abs_sub _ _).trans (add_le_add (hw.trans hbudget) hq)

end AmplitudePolynomial
end
end chebyshev2.Numerics.IntegerCertificate
