import «2610.05164v2».Numerics.IntegerPolynomial
import «2610.05164v2».Numerics.IntegerReferenceSource
import «2610.05164v2».Numerics.ReferenceResidualIdentity

/-!
Article: 2610.05164v2, Section 4.1.
Polynomial residuals for the actual rational reference profile.
Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.factor_value` feeds
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` (The complete local acceptance
theorem: all numerical premises are discharged by the executable certificate predicate).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate
open Set «2610.05164v2».DualCertificate «2610.05164v2».Calibration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ResidualExpr
/--
Defines `t` of type `Expr` by `.input 0`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def t : Expr := .input 0
/--
Defines `pi` of type `Expr` by `.input 1`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.k` uses this definition in the
displayed construction of `k`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def pi : Expr := .input 1
/--
Defines `z` of type `Expr` by `.input 2`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.odeResidual` uses this definition
in the displayed construction of `odeResidual`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def z : Expr := .input 2
/--
Defines `p` of type `Expr` by `.input 3`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.odeResidual` uses this definition
in the displayed construction of `odeResidual`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def p : Expr := .input 3
/--
Defines `pd` of type `Expr` by `.input 4`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.factor` uses this definition in
the displayed construction of `factor`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def pd : Expr := .input 4
/--
Defines `sq` of type `Expr` by `.mul e e`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.cube` uses this definition in the
displayed construction of `cube`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def sq (e : Expr) : Expr := .mul e e
/--
Defines `cube` of type `Expr` by `.mul (sq e) e`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def cube (e : Expr) : Expr := .mul (sq e) e
/--
Defines `sub` of type `Expr` by `.add a (.neg b)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.factor` uses this definition in
the displayed construction of `factor`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def sub (a b : Expr) : Expr := .add a (.neg b)
/--
Defines `times` of type `Expr` by `.mul (.rational q) e`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.factor` uses this definition in
the displayed construction of `factor`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def times (q : ℚ) (e : Expr) : Expr := .mul (.rational q) e
/--
Defines `h` of type `Expr` by `sub (.rational 2) (cube t)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def h : Expr := sub (.rational 2) (cube t)
/--
Defines `Q` of type `Expr` by `.mul (cube t) h`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.profileParts_value` uses this
definition to establish the identity `0<(profileParts R).1.value v ∧ (profileParts R).2.value
v = (profileParts R).1.value v * R.coefficient (Q.value v)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Q : Expr := .mul (cube t) h
/--
Defines `k` of type `Expr` by `times (1/4) (sq pi)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.factor` uses this definition in
the displayed construction of `factor`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def k : Expr := times (1/4) (sq pi)

/--
Defines `profileStep` of type `Expr × Expr` by `let di := .add Q (.rational v.2) (.mul dn.1 di,
.add (.mul dn.2 di) (times v.1 (.mul Q dn.1)))`.

Use:
`_private.«2610.05164v2».Numerics.IntegerReferenceResidual.0.«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.profileFold`
rewrites with this definition to establish the identity `0<((vs.foldl profileStep
dn).1).value v ∧ ((vs.foldl profileStep dn).2).value v = ((vs.foldl profileStep dn).1).value v
* (c+(vs.map (fun a => (a.1:ℝ)*q/(q+(a.2:ℝ)))).sum)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def profileStep (dn : Expr × Expr) (v : ℚ × ℚ) : Expr × Expr :=
  let di := .add Q (.rational v.2)
  (.mul dn.1 di, .add (.mul dn.2 di) (times v.1 (.mul Q dn.1)))
/--
Defines `terms` of type `List (ℚ × ℚ)` by `List.ofFn (fun i => (R.p i,R.ζ i))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.profileParts` uses this
definition in the displayed construction of `profileParts`. Its inputs and component formulas
are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def terms (R : RationalReference) : List (ℚ × ℚ) := List.ofFn (fun i => (R.p i,R.ζ i))
/--
Defines `profileParts` of type `Expr × Expr` by `(terms R).foldl profileStep (.rational
1,.rational R.p₀)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.profileParts_value` uses this
definition to establish the identity `0<(profileParts R).1.value v ∧ (profileParts R).2.value
v = (profileParts R).1.value v * R.coefficient (Q.value v)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def profileParts (R : RationalReference) : Expr × Expr :=
  (terms R).foldl profileStep (.rational 1,.rational R.p₀)
/--
Defines `rootResidual` of type `Expr` by `sub (.mul (sub (.mul k (cube z)) (times 3 (.mul (.mul
t h) z))) (profileParts R).1) (times 2 (.mul h (profileParts R).2))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.rootResidual_value` rewrites with
this definition to establish the identity `(rootResidual R).value (values t₀ z₀ p₀ pd₀) =
(profileParts R).1.value (values t₀ z₀ p₀ pd₀) * ((Real.pi^2/4)*z₀^3-3*t₀*(2-t₀^3)*z₀-
2*R.coefficient (t₀^3*(2-t₀^3))*(2-t₀^3))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def rootResidual (R : RationalReference) : Expr :=
  sub (.mul (sub (.mul k (cube z)) (times 3 (.mul (.mul t h) z)))
    (profileParts R).1) (times 2 (.mul h (profileParts R).2))
/--
Defines `factor` of type `Expr` by `.mul k (sub (times 3 (sq t)) pd)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.factor_value` rewrites with this
definition to establish the identity `factor.value (values t₀ z₀ p₀ pd₀) =
(Real.pi^2/4)*(3*t₀^2-pd₀)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def factor : Expr := .mul k (sub (times 3 (sq t)) pd)
/--
Defines `odeResidual` of type `Expr` by `sub (sub (.add (.mul factor (sq z)) (.mul pd (.mul t
h))) (times 6 p)) (times (3*σ) (sq p))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.odeResidual_value` rewrites with
this definition to establish the identity `(odeResidual σ).value (values t₀ z₀ p₀ pd₀) =
(Real.pi^2/4)*(3*t₀^2-pd₀)*z₀^2+pd₀*t₀*(2-t₀^3)-6*p₀-3*(σ:ℝ)*p₀^2`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def odeResidual (σ : ℚ) : Expr :=
  sub (sub (.add (.mul factor (sq z)) (.mul pd (.mul t h))) (times 6 p))
    (times (3*σ) (sq p))

/--
Exact identity `0<((vs.foldl profileStep dn).1).value v ∧ ((vs.foldl profileStep dn).2).value v
= ((vs.foldl profileStep dn).1).value v * (c+(vs.map (fun a => (a.1:ℝ)*q/(q+(a.2:ℝ)))).sum)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.profileParts_value` uses this
identity to establish the identity `0<(profileParts R).1.value v ∧ (profileParts R).2.value v
= (profileParts R).1.value v * R.coefficient (Q.value v)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `vs` while keeping `dn c` arbitrary; the recursive step uses the
previous-stage assertion. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
private theorem profileFold (vs : List (ℚ × ℚ)) (dn : Expr × Expr)
    (v : Nat → ℝ) (q c : ℝ) (hQ : Q.value v=q) (hq : 0≤q)
    (hz : ∀ a ∈ vs, (0:ℚ)<a.2)
    (hd : 0<dn.1.value v) (hn : dn.2.value v=dn.1.value v*c) :
    0<((vs.foldl profileStep dn).1).value v ∧
    ((vs.foldl profileStep dn).2).value v =
      ((vs.foldl profileStep dn).1).value v *
        (c+(vs.map (fun a => (a.1:ℝ)*q/(q+(a.2:ℝ)))).sum) := by
  -- Induct on `vs` while keeping `dn c` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction vs generalizing dn c with
  | nil => simpa using And.intro hd hn
  | cons a vs ih =>
    have hza : (0:ℝ)<a.2 := by exact_mod_cast hz a (by simp)
    have hdi : 0<q+(a.2:ℝ) := by linarith
    have hdn : 0<(profileStep dn a).1.value v := by
      simpa [profileStep, Expr.value, Expr.rational_value, hQ] using mul_pos hd hdi
    have hnn : (profileStep dn a).2.value v =
        (profileStep dn a).1.value v*(c+(a.1:ℝ)*q/(q+(a.2:ℝ))) := by
      simp only [profileStep, Expr.value, times, Expr.rational_value, hQ, hn]
      field_simp [hdi.ne']
    have hh := ih (profileStep dn a) (c+(a.1:ℝ)*q/(q+(a.2:ℝ)))
      (fun b hb => hz b (by simp [hb])) hdn hnn
    simpa [add_assoc] using hh

/--
Exact identity `0<(profileParts R).1.value v ∧ (profileParts R).2.value v = (profileParts
R).1.value v * R.coefficient (Q.value v)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.rootResidual_value` uses this
identity to establish the identity `(rootResidual R).value (values t₀ z₀ p₀ pd₀) =
(profileParts R).1.value (values t₀ z₀ p₀ pd₀) * ((Real.pi^2/4)*z₀^3-3*t₀*(2-t₀^3)*z₀-
2*R.coefficient (t₀^3*(2-t₀^3))*(2-t₀^3))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`_private.«2610.05164v2».Numerics.IntegerReferenceResidual.0.«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.profileFold`,
`«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem profileParts_value (R : RationalReference) (v : Nat → ℝ)
    (hq : 0≤Q.value v) :
    0<(profileParts R).1.value v ∧ (profileParts R).2.value v =
      (profileParts R).1.value v * R.coefficient (Q.value v) := by
  -- Use the identities/estimates
  -- `_private.«2610.05164v2».Numerics.IntegerReferenceResidual.0.«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.profileFold`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown
  -- in the proof.
  have hh := profileFold (terms R) (.rational 1,.rational R.p₀) v (Q.value v)
    (R.p₀:ℝ) rfl hq ?_ (by simp [Expr.rational_value]) (by simp [Expr.rational_value])
  · simpa [profileParts, terms, RationalReference.coefficient, List.map_ofFn,
      List.sum_ofFn, Function.comp_apply] using hh
  · intro a ha
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp ha
    subst a
    exact R.ζ_pos i

/--
Defines `values` by pattern matching with result type `Nat → ℝ`. The displayed branches
determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.factor_value` rewrites with this
definition to establish the identity `factor.value (values t₀ z₀ p₀ pd₀) =
(Real.pi^2/4)*(3*t₀^2-pd₀)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def values (t z p pd : ℝ) : Nat → ℝ
  | 0 => t | 1 => Real.pi | 2 => z | 3 => p | 4 => pd | _ => 0

/--
The precise assertion is `let v`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.rootResidual_value` uses this
assertion to establish the identity `(rootResidual R).value (values t₀ z₀ p₀ pd₀) =
(profileParts R).1.value (values t₀ z₀ p₀ pd₀) * ((Real.pi^2/4)*z₀^3-3*t₀*(2-t₀^3)*z₀-
2*R.coefficient (t₀^3*(2-t₀^3))*(2-t₀^3))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem values_basic (t₀ z₀ p₀ pd₀ : ℝ) :
    let v := values t₀ z₀ p₀ pd₀
    t.value v=t₀ ∧ z.value v=z₀ ∧ p.value v=p₀ ∧ pd.value v=pd₀ ∧
    k.value v=Real.pi^2/4 ∧ h.value v=2-t₀^3 ∧ Q.value v=t₀^3*(2-t₀^3) := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_⟩ <;>
    simp only [values, t, k, h, Q, sub, cube, sq, times, pi,
      Expr.value, Expr.rational_value] <;> ring

/--
Exact identity `(rootResidual R).value (values t₀ z₀ p₀ pd₀) = (profileParts R).1.value (values
t₀ z₀ p₀ pd₀) * ((Real.pi^2/4)*z₀^3-3*t₀*(2-t₀^3)*z₀- 2*R.coefficient
(t₀^3*(2-t₀^3))*(2-t₀^3))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_root_sound` rewrites with
this identity to prove the bound `|(ReferenceJetSource.referenceData
R).normalizedRoot ((values s r 0).eval x)- (values s r 2).eval x|≤(r.delta:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.values_basic`,
`«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.profileParts_value`,
`«2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem` with the arguments shown
in the proof.
-/
theorem rootResidual_value (R : RationalReference) {t₀ : ℝ} (ht : t₀∈Icc (0:ℝ) 1)
    (z₀ p₀ pd₀ : ℝ) :
    (rootResidual R).value (values t₀ z₀ p₀ pd₀) =
      (profileParts R).1.value (values t₀ z₀ p₀ pd₀) *
      ((Real.pi^2/4)*z₀^3-3*t₀*(2-t₀^3)*z₀-
        2*R.coefficient (t₀^3*(2-t₀^3))*(2-t₀^3)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.values_basic`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.profileParts_value`,
  -- `«2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem` with the arguments
  -- shown in the proof.
  have hb := values_basic t₀ z₀ p₀ pd₀
  have hparts := profileParts_value R (values t₀ z₀ p₀ pd₀) (by
    rw [hb.2.2.2.2.2.2]
    exact (ReferenceData.normalized_coefficient_mem ht).1)
  simp only [rootResidual, sub, Expr.value, times, Expr.rational_value,
    hparts.2, hb.2.2.2.2.2.2, cube, sq, hb.1, hb.2.1, hb.2.2.2.2.1,
    hb.2.2.2.2.2.1]
  ring

/--
Exact identity `(odeResidual σ).value (values t₀ z₀ p₀ pd₀) =
(Real.pi^2/4)*(3*t₀^2-pd₀)*z₀^2+pd₀*t₀*(2-t₀^3)-6*p₀-3*(σ:ℝ)*p₀^2`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` rewrites with this
identity to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem odeResidual_value (σ : ℚ) (t₀ z₀ p₀ pd₀ : ℝ) :
    (odeResidual σ).value (values t₀ z₀ p₀ pd₀) =
      (Real.pi^2/4)*(3*t₀^2-pd₀)*z₀^2+pd₀*t₀*(2-t₀^3)-6*p₀-3*(σ:ℝ)*p₀^2 := by
  simp only [odeResidual, factor, sub, times, sq, cube, k, h, t, pi, z, p, pd,
    Expr.value, Expr.rational_value, values, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_div, Rat.cast_one]
  ring

/--
Exact identity `factor.value (values t₀ z₀ p₀ pd₀) = (Real.pi^2/4)*(3*t₀^2-pd₀)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_sound` rewrites with this
identity to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value` with the arguments shown in
the proof.
-/
theorem factor_value (t₀ z₀ p₀ pd₀ : ℝ) :
    factor.value (values t₀ z₀ p₀ pd₀) = (Real.pi^2/4)*(3*t₀^2-pd₀) := by
  simp only [factor, k, sub, times, sq, t, pd, pi, Expr.value,
    Expr.rational_value, values]
  ring

end ResidualExpr

end «2610.05164v2».Numerics.IntegerCertificate
