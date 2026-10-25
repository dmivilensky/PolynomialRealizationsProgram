import chebyshev2.Numerics.PolynomialAffine
import chebyshev2.Numerics.DirectReferenceCore

/-!
Article: chebyshev2, Section 4.1.
Cleared-denominator quadrature for the actual contact integrand.
Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.error_bound` feeds
`chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.check_sound` (check sound).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate
open Set Polynomial chebyshev2.Calibration
set_option autoImplicit false

namespace ContactExpr
/--
Defines `t` of type `Expr` by `.input 0`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def t : Expr := .input 0
/--
Defines `pi` of type `Expr` by `.input 1`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.speed` uses this definition in the
displayed construction of `speed`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def pi : Expr := .input 1
/--
Defines `root` of type `Expr` by `.input 2`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.speed` uses this definition in the
displayed construction of `speed`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def root : Expr := .input 2
/--
Defines `left` of type `Expr` by `.input 3`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.gammaDen` uses this definition in
the displayed construction of `gammaDen`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def left : Expr := .input 3
/--
Defines `right` of type `Expr` by `.input 4`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.gammaDen` uses this definition in
the displayed construction of `gammaDen`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def right : Expr := .input 4
/--
Defines `approx` of type `Expr` by `.input 5`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.residual` uses this definition in
the displayed construction of `residual`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def approx : Expr := .input 5
/--
Defines `lit` of type `Expr` by `.rational q`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def lit (q : ℚ) : Expr := .rational q
/--
Defines `sq` of type `Expr` by `.mul e e`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.cube` uses this definition in the
displayed construction of `cube`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def sq (e : Expr) : Expr := .mul e e
/--
Defines `cube` of type `Expr` by `.mul (sq e) e`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def cube (e : Expr) : Expr := .mul (sq e) e
/--
Defines `sub` of type `Expr` by `.add a (.neg b)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def sub (a b : Expr) : Expr := .add a (.neg b)
/--
Defines `Q` of type `Expr` by `.mul (cube t) (sub (lit 2) (cube t))`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.gammaNum` uses this definition in
the displayed construction of `gammaNum`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Q : Expr := .mul (cube t) (sub (lit 2) (cube t))
/--
Defines `gammaDen` of type `Expr` by `.add (lit 2) (.mul (lit σ) (.add left right))`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.gammaDen_value` rewrites with this
definition to establish the identity `(gammaDen σ).value (values t r l u g)=2+(σ:ℝ)*(l+u)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def gammaDen (σ : ℚ) : Expr := .add (lit 2) (.mul (lit σ) (.add left right))
/--
Defines `speed` of type `Expr` by `sub (.mul (.mul (lit (1/4)) (sq pi)) (sq root)) (.mul t (sub
(lit 2) (cube t)))`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.residual` uses this definition in
the displayed construction of `residual`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def speed : Expr := sub (.mul (.mul (lit (1/4)) (sq pi)) (sq root))
  (.mul t (sub (lit 2) (cube t)))
/--
Defines `gammaNum` of type `Expr` by `sub (.mul Q (.add left right)) (.mul (lit 2) (.mul left
right))`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.numerator` uses this definition in
the displayed construction of `numerator`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def gammaNum : Expr := sub (.mul Q (.add left right)) (.mul (lit 2) (.mul left right))
/--
Defines `numerator` of type `Expr` by `.mul (lit 3) (sub (.mul (lit 2) gammaNum) (.mul (.add
(sq left) (sq right)) (gammaDen σ)))`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.residual` uses this definition in
the displayed construction of `residual`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def numerator (σ : ℚ) : Expr := .mul (lit 3)
  (sub (.mul (lit 2) gammaNum) (.mul (.add (sq left) (sq right)) (gammaDen σ)))
/--
Defines `residual` of type `Expr` by `sub (numerator σ) (.mul approx (.mul (gammaDen σ)
speed))`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.residual_value` rewrites with this
definition to establish `(residual σ).value (values t r l u g)=
3*(2*((t^3*(2-t^3))*(l+u)-2*l*u)-(l^2+u^2)*(2+(σ:ℝ)*(l+u)))-
g*((2+(σ:ℝ)*(l+u))*((Real.pi^2/4)*r^2-t*(2-t^3)))`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def residual (σ : ℚ) : Expr := sub (numerator σ) (.mul approx (.mul (gammaDen σ) speed))
/--
Defines `values` by pattern matching with result type `Nat → ℝ`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactExpr.gammaDen_value` rewrites with this
definition to establish the identity `(gammaDen σ).value (values t r l u g)=2+(σ:ℝ)*(l+u)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def values (t r l u g : ℝ) : Nat → ℝ
  | 0 => t
  | 1 => Real.pi
  | 2 => r
  | 3 => l
  | 4 => u
  | 5 => g
  | _ => 0

/--
Exact identity `(gammaDen σ).value (values t r l u g)=2+(σ:ℝ)*(l+u)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.error_bound` rewrites with
this identity to prove the bound `|R.directContactCore (σ := (sigma:ℝ))
(by exact_mod_cast hsigma) t-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem gammaDen_value (σ : ℚ) (t r l u g : ℝ) :
    (gammaDen σ).value (values t r l u g)=2+(σ:ℝ)*(l+u) := by
  simp only [gammaDen,lit,Expr.value,Expr.rational_value,values,left,right]
  norm_num

/--
Exact identity `speed.value (values t r l u g)=(Real.pi^2/4)*r^2-t*(2-t^3)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.error_bound` rewrites with
this identity to prove the bound `|R.directContactCore (σ := (sigma:ℝ))
(by exact_mod_cast hsigma) t-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem speed_value (t r l u g : ℝ) :
    speed.value (values t r l u g)=(Real.pi^2/4)*r^2-t*(2-t^3) := by
  simp only [speed,sub,sq,cube,lit,Expr.value,Expr.rational_value,values,ContactExpr.t,pi,root]
  norm_num
  ring

/--
The precise assertion is `(residual σ).value (values t r l u g)=
3*(2*((t^3*(2-t^3))*(l+u)-2*l*u)-(l^2+u^2)*(2+(σ:ℝ)*(l+u)))-
g*((2+(σ:ℝ)*(l+u))*((Real.pi^2/4)*r^2-t*(2-t^3)))`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.error_bound` rewrites with
this identity to prove the bound `|R.directContactCore (σ := (sigma:ℝ))
(by exact_mod_cast hsigma) t-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem residual_value (σ : ℚ) (t r l u g : ℝ) :
    (residual σ).value (values t r l u g)=
      3*(2*((t^3*(2-t^3))*(l+u)-2*l*u)-(l^2+u^2)*(2+(σ:ℝ)*(l+u)))-
        g*((2+(σ:ℝ)*(l+u))*((Real.pi^2/4)*r^2-t*(2-t^3))) := by
  simp only [residual,numerator,gammaNum,Q,gammaDen,speed,sub,sq,cube,lit,
    Expr.value,Expr.rational_value,values,ContactExpr.t,pi,root,left,right,approx]
  norm_num
  ring
end ContactExpr

namespace ContactPolynomial
noncomputable section
variable (R : ReferenceData) {σ : ℝ} (hσ : 0<σ)

/--
The precise assertion is `(R.directContactCore hσ t-g)* ((2+σ*(R.normalizedFilter hσ
t+R.normalizedReflectedFilter hσ t))* ReferenceResidual.denominator R t)=
3*(2*((t^3*(2-t^3))*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)-
2*R.normalizedFilter hσ t*R.normalizedReflectedFilter hσ t)- ((R.normalizedFilter hσ
t)^2+(R.normalizedReflectedFilter hσ t)^2)* (2+σ*(R.normalizedFilter hσ
t+R.normalizedReflectedFilter hσ t)))- g*((2+σ*(R.normalizedFilter hσ
t+R.normalizedReflectedFilter hσ t))* ReferenceResidual.denominator R t)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.error_bound` uses this
identity to prove the bound `|R.directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast hsigma) t-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem cleared_identity {t g : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hD : 0<2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)) :
    (R.directContactCore hσ t-g)*
      ((2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t))*
        ReferenceResidual.denominator R t)=
    3*(2*((t^3*(2-t^3))*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)-
      2*R.normalizedFilter hσ t*R.normalizedReflectedFilter hσ t)-
      ((R.normalizedFilter hσ t)^2+(R.normalizedReflectedFilter hσ t)^2)*
        (2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)))-
      g*((2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t))*
        ReferenceResidual.denominator R t) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  dsimp only [ReferenceData.directContactCore,ReferenceData.directGamma,ReferenceData.normalizedVelocity]
  rw [← ReferenceResidual.denominator_eq_speed R ht]
  have hV := ReferenceResidual.denominator_positive R ht
  generalize R.normalizedFilter hσ t=l at *
  generalize R.normalizedReflectedFilter hσ t=u at *
  generalize 2+σ*(l+u)=D at *
  generalize ReferenceResidual.denominator R t=V at *
  field_simp [hD.ne',hV.ne']
  ring

/--
The stated quantitative bound `|R.directContactCore (σ := (sigma:ℝ)) (by exact_mod_cast hsigma)
t-g|≤(ε:ℝ)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.check_sound` uses this
identity to prove the bound `|R.directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast hsigma) t-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Bounds.real_mem`,
`chebyshev2.Numerics.IntegerCertificate.ContactExpr.gammaDen_value`,
`chebyshev2.Numerics.IntegerCertificate.ContactExpr.speed_value` with the arguments shown
in the proof.
-/
theorem error_bound (hk : R.k=Real.pi^2/4) {sigma : ℚ} (hsigma : 0<sigma) {t g : ℝ}
    (ht : t∈Icc (0:ℝ) 1) {s : Nat} (hs : 0<s) {D V E : Bounds} {ε : ℚ}
    (hD : D.Mem s ((ContactExpr.gammaDen sigma).value
      (ContactExpr.values t (R.normalizedRoot t)
        (R.normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t)
        (R.normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t) g)))
    (hV : V.Mem s (ContactExpr.speed.value
      (ContactExpr.values t (R.normalizedRoot t)
        (R.normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t)
        (R.normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t) g)))
    (hE : E.Mem s ((ContactExpr.residual sigma).value
      (ContactExpr.values t (R.normalizedRoot t)
        (R.normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t)
        (R.normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t) g)))
    (hc : 0<D.lower s ∧ 0<V.lower s ∧ 0≤ε ∧
      E.magnitude s≤ε*(D.lower s*V.lower s)) :
    |R.directContactCore (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t-g|≤(ε:ℝ) := by
  -- Use the identities/estimates `chebyshev2.Numerics.IntegerCertificate.Bounds.real_mem`,
  -- `chebyshev2.Numerics.IntegerCertificate.ContactExpr.gammaDen_value`,
  -- `chebyshev2.Numerics.IntegerCertificate.ContactExpr.speed_value` with the arguments
  -- shown in the proof.
  rw [ContactExpr.gammaDen_value] at hD
  rw [ContactExpr.speed_value] at hV
  rw [ContactExpr.residual_value] at hE
  have hDr := (Bounds.real_mem hs hD).1
  have hVr := (Bounds.real_mem hs hV).1
  have hDl : (0:ℝ)<(D.lower s:ℝ) := by exact_mod_cast hc.1
  have hVl : (0:ℝ)<(V.lower s:ℝ) := by exact_mod_cast hc.2.1
  have hε : (0:ℝ)≤(ε:ℝ) := by exact_mod_cast hc.2.2.1
  have he : (E.magnitude s:ℝ)≤(ε:ℝ)*((D.lower s:ℝ)*(V.lower s:ℝ)) := by
    exact_mod_cast hc.2.2.2
  rw [← hk] at hVr hE
  change (V.lower s:ℝ)≤ReferenceResidual.denominator R t at hVr
  have hdpos := hDl.trans_le hDr
  have hvpos := hVl.trans_le hVr
  have he' := Bounds.real_abs hs hE
  have hid := cleared_identity R (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) (g := g) ht hdpos
  dsimp only [ReferenceResidual.denominator] at hid
  rw [← hid,abs_mul] at he'
  change |R.directContactCore (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t-g| *
    |(2+(sigma:ℝ)*(R.normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t+
      R.normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t))*
      ReferenceResidual.denominator R t|≤(E.magnitude s:ℝ) at he'
  rw [abs_of_pos (mul_pos hdpos hvpos)] at he'
  have hbudget : (E.magnitude s:ℝ)≤(ε:ℝ)*
      ((2+(sigma:ℝ)*(R.normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t+
        R.normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t))*
        ReferenceResidual.denominator R t) := he.trans (by gcongr)
  exact (mul_le_mul_iff_left₀ (mul_pos hdpos hvpos)).mp (he'.trans hbudget)

end
end ContactPolynomial
end chebyshev2.Numerics.IntegerCertificate
