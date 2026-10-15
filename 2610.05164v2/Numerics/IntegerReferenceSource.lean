import «2610.05164v2».Numerics.IntegerExpression
import «2610.05164v2».Numerics.ReferenceJetSource

/-!
Article: 2610.05164v2, Section 4.1.
Independent literal expressions for the actual reference ODE.
Use: `«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value` feeds
`«2610.05164v2».Numerics.IntegerCertificate.ResidualExpr.profileParts_value` (profile Parts value).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate
open Set «2610.05164v2».DualCertificate
set_option autoImplicit false

/--
Defines `Expr.rational` of type `Expr` by `.literal q.num q.den`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value` uses this definition to
establish exact identity `(Expr.rational q).value v = (q : ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Expr.rational (q : ℚ) : Expr := .literal q.num q.den

/--
Exact identity `(Expr.rational q).value v = (q : ℝ)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.coefficient_values` rewrites
with this identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Expr.rational_value (q : ℚ) (v : Nat → ℝ) :
    (Expr.rational q).value v = (q : ℝ) := by simp [rational, value, Rat.cast_def]

namespace ReferenceExpr
/--
Defines `t` of type `Expr` by `.input 0`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.alpha` uses this definition in
the displayed construction of `alpha`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Section 4.1.
-/
def t : Expr := .input 0
/--
Defines `pi` of type `Expr` by `.input 1`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.k` uses this definition in the
displayed construction of `k`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def pi : Expr := .input 1
/--
Defines `cube` of type `Expr` by `.mul (.mul t t) t`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def cube : Expr := .mul (.mul t t) t
/--
Defines `h` of type `Expr` by `.add (.rational 2) (.neg cube)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.Q` uses this definition in the
displayed construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def h : Expr := .add (.rational 2) (.neg cube)
/--
Defines `Q` of type `Expr` by `.mul cube h`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.term` uses this definition in
the displayed construction of `term`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Section 4.1.
-/
def Q : Expr := .mul cube h
/--
Defines `k` of type `Expr` by `.mul (.rational (1/4)) (.mul pi pi)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.C` uses this definition in the
displayed construction of `C`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def k : Expr := .mul (.rational (1/4)) (.mul pi pi)
/--
Defines `term` of type `Expr` by `.mul (.rational (R.p i)) (.mul Q (.inv (.add Q (.rational
(R.ζ i)))))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.p` uses this definition in the
displayed construction of `p`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def term (R : RationalReference) (i : Fin R.count) : Expr :=
  .mul (.rational (R.p i)) (.mul Q (.inv (.add Q (.rational (R.ζ i)))))
/--
Defines `p` of type `Expr` by `(List.ofFn (term R)).foldl Expr.add (.rational R.p₀)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.beta` uses this definition in
the displayed construction of `beta`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Section 4.1.
-/
def p (R : RationalReference) : Expr :=
  (List.ofFn (term R)).foldl Expr.add (.rational R.p₀)
/--
Defines `alpha` of type `Expr` by `.mul (.mul (.rational 3) (.mul t h)) (.inv k)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.root` uses this definition in
the displayed construction of `root`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Section 4.1.
-/
def alpha (_R : RationalReference) : Expr :=
  .mul (.mul (.rational 3) (.mul t h)) (.inv k)
/--
Defines `beta` of type `Expr` by `.mul (.mul (.rational 2) (.mul (p R) h)) (.inv k)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.root` uses this definition in
the displayed construction of `root`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Section 4.1.
-/
def beta (R : RationalReference) : Expr :=
  .mul (.mul (.rational 2) (.mul (p R) h)) (.inv k)
/--
Defines `root` of type `Expr` by `.cubic (alpha R) (beta R)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.amplitude` uses this definition
in the displayed construction of `amplitude`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Section 4.1.
-/
def root (R : RationalReference) : Expr := .cubic (alpha R) (beta R)
/--
Defines `speed` of type `Expr` by `.add (.mul (.rational 2) (.mul t h)) (.mul (.rational 2)
(.mul (.mul (p R) h) (.inv (root R))))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.speed_value` rewrites with this
definition to establish the identity `(speed R).value (inputs x) =
(ReferenceJetSource.referenceData R).normalizedSpeed x`.

Article: 2610.05164v2, Section 4.1.
-/
def speed (R : RationalReference) : Expr :=
  .add (.mul (.rational 2) (.mul t h))
    (.mul (.rational 2) (.mul (.mul (p R) h) (.inv (root R))))
/--
Defines `velocity` of type `Expr` by `.mul (.rational 3) (.inv (speed R))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.A` uses this definition in the
displayed construction of `A`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def velocity (R : RationalReference) : Expr := .mul (.rational 3) (.inv (speed R))
/--
Defines `amplitude` of type `Expr` by `.mul t (root R)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.C` uses this definition in the
displayed construction of `C`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def amplitude (R : RationalReference) : Expr := .mul t (root R)
/--
Defines `C` of type `Expr` by `.mul (.mul (velocity R) k) (.mul (amplitude R) (amplitude R))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.coefficient_values` rewrites
with this definition to establish the identity stated in that declaration.

Article: 2610.05164v2, Section 4.1.
-/
def C (R : RationalReference) : Expr :=
  .mul (.mul (velocity R) k) (.mul (amplitude R) (amplitude R))
/--
Defines `A` of type `Expr` by `.mul (.rational (-2)) (velocity R)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.coefficient_values` rewrites
with this definition to establish the identity stated in that declaration.

Article: 2610.05164v2, Section 4.1.
-/
def A (R : RationalReference) : Expr := .mul (.rational (-2)) (velocity R)
/--
Defines `B` of type `Expr` by `.mul (.rational (-sigma)) (velocity R)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.coefficient_values` rewrites
with this definition to establish the identity stated in that declaration.

Article: 2610.05164v2, Section 4.1.
-/
def B (R : RationalReference) (sigma : ℚ) : Expr := .mul (.rational (-sigma)) (velocity R)

/--
Defines `inputs` by pattern matching with result type `Nat → ℝ`. The displayed branches
determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.coefficient_values` rewrites
with this definition to establish the identity stated in that declaration.

Article: 2610.05164v2, Section 4.1.
-/
noncomputable def inputs (x : ℝ) : Nat → ℝ
  | 0 => x
  | 1 => Real.pi
  | _ => 0

/--
Exact identity `(es.foldl Expr.add e).value v = e.value v + (es.map (Expr.value v)).sum`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.p_value` rewrites with this
identity to establish the identity `(p R).value (inputs x) = R.coefficient (x^3*(2-x^3))`.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `es` while keeping `e` arbitrary; the recursive step uses the
previous-stage assertion.
-/
private theorem foldl_value (es : List Expr) (e : Expr) (v : Nat → ℝ) :
    (es.foldl Expr.add e).value v = e.value v + (es.map (Expr.value v)).sum := by
  induction es generalizing e with
  | nil => simp
  | cons a es ih => simp [ih, Expr.value, add_assoc]

/--
Exact identity `(p R).value (inputs x) = R.coefficient (x^3*(2-x^3))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.root_value` rewrites with this
identity to establish the identity `(root R).value (inputs x) =
(ReferenceJetSource.referenceData R).normalizedRoot x`.

Article: 2610.05164v2, Section 4.1.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem p_value (R : RationalReference) (x : ℝ) :
    (p R).value (inputs x) = R.coefficient (x^3*(2-x^3)) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  simp only [p, foldl_value, Expr.rational_value, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, term, Q, cube, h, t, Expr.value, inputs, Expr.rational_value,
    RationalReference.coefficient, div_eq_mul_inv, mul_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/--
Exact identity `(root R).value (inputs x) = (ReferenceJetSource.referenceData R).normalizedRoot
x`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.coefficient_values` rewrites
with this identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.root_value`,
`«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value`,
`«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.p_value` with the arguments shown in
the proof.
-/
theorem root_value (R : RationalReference) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (root R).value (inputs x) = (ReferenceJetSource.referenceData R).normalizedRoot x := by
  rw [← ReferenceJetSource.root_value R (fun _ => []) hx]
  simp only [root, alpha, beta, k, h, cube, t, pi, Expr.value, Expr.rational_value,
    inputs, p_value, ReferenceJetSource.root, JetExpr.value,
    ReferenceJetSource.alpha_value, ReferenceJetSource.beta_value]
  congr 1 <;> ring

/--
Exact identity `(speed R).value (inputs x) = (ReferenceJetSource.referenceData
R).normalizedSpeed x`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.velocity_value` rewrites with
this identity to establish the identity `(velocity R).value (inputs x) =
(ReferenceJetSource.referenceData R).normalizedVelocity x`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value`,
`«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.p_value`,
`«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.root_value` with the arguments shown
in the proof.
-/
theorem speed_value (R : RationalReference) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (speed R).value (inputs x) = (ReferenceJetSource.referenceData R).normalizedSpeed x := by
  simp only [speed, Expr.value, Expr.rational_value, t, h, cube, inputs, p_value,
    root_value R hx, «2610.05164v2».Calibration.ReferenceData.normalizedSpeed,
    ReferenceJetSource.referenceData, RationalReference.referenceData]
  ring

/--
Exact identity `(velocity R).value (inputs x) = (ReferenceJetSource.referenceData
R).normalizedVelocity x`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.coefficient_values` rewrites
with this identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value`,
`«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.speed_value` with the arguments shown
in the proof.
-/
theorem velocity_value (R : RationalReference) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (velocity R).value (inputs x) = (ReferenceJetSource.referenceData R).normalizedVelocity x := by
  simp only [velocity, Expr.value, Expr.rational_value, speed_value R hx,
    «2610.05164v2».Calibration.ReferenceData.normalizedVelocity, div_eq_mul_inv, Rat.cast_ofNat]

/--
Exact identity `(C R).value (inputs x) = (ReferenceJetSource.C R (fun _ => [])).value x ∧ (A
R).value (inputs x) = (ReferenceJetSource.A R (fun _ => [])).value x ∧ (B R sigma).value
(inputs x) = (ReferenceJetSource.B R (fun _ => []) sigma).value x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.velocity_value`,
`«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value`,
`«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.root_value` with the arguments shown
in the proof.
-/
theorem coefficient_values (R : RationalReference) (sigma : ℚ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (C R).value (inputs x) = (ReferenceJetSource.C R (fun _ => [])).value x ∧
    (A R).value (inputs x) = (ReferenceJetSource.A R (fun _ => [])).value x ∧
    (B R sigma).value (inputs x) = (ReferenceJetSource.B R (fun _ => []) sigma).value x := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.velocity_value`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Expr.rational_value`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.ReferenceExpr.root_value` with the arguments
  -- shown in the proof.
  simp only [C, A, B, k, amplitude, t, pi, Expr.value, Expr.rational_value,
    inputs, root_value R hx, velocity_value R hx,
    ReferenceJetSource.C, ReferenceJetSource.A, ReferenceJetSource.B,
    ReferenceJetSource.amplitude, JetExpr.scale, JetExpr.value,
    ReferenceJetSource.root_value R (fun _ => []) hx,
    ReferenceJetSource.velocity_value R (fun _ => []) hx, ReferenceJetSource.k_value,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one]
  constructor
  · ring
  · exact ⟨trivial, trivial⟩

end ReferenceExpr
end «2610.05164v2».Numerics.IntegerCertificate
