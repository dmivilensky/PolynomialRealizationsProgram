import chebyshev2.Numerics.ContactPolynomial

/-!
Article: chebyshev2, Section 4.1.
Contact Check.
Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.check_sound` feeds
`chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.Panel.valuePanel_actual` (value Panel
actual).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate.ContactPolynomial
open Set chebyshev2.Calibration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Inputs/checkpoints for the polynomial contact-residual program, or its computed
denominator/speed/residual summary. Acceptance requires explicit signs and residual budgets.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.check` uses this record of
data and proof obligations in the displayed construction of `check`. Its inputs and component
formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure Row where
  /-- Interval-polynomial inputs in the fixed contact-expression layout. -/
  inputs : List (List Bounds)
  /-- Retained polynomial degree for evaluation/truncation. -/
  degree : Nat
  /-- Optional intermediate enclosures, each validated against its computed node. -/
  checkpoints : List (Option (List Bounds))
  deriving Repr, DecidableEq

/--
Inputs/checkpoints for the polynomial contact-residual program, or its computed
denominator/speed/residual summary. Acceptance requires explicit signs and residual budgets.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.check` uses this record of
data and proof obligations in the displayed construction of `check`. Its inputs and component
formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure Summary where
  /-- Computed enclosure of the contact denominator. -/
  den : Bounds
  /-- Computed enclosure of the positive contact speed. -/
  speed : Bounds
  /-- Computed enclosure of the contact quadrature residual. -/
  residual : Bounds
  deriving Repr, DecidableEq

/--
Defines `summarize` of type `Option Summary` by `do let out ← Poly.Taylor.evalProgram s
r.degree r.inputs r.checkpoints ops return ⟨← ResidualCell.outputRange s out 26, ←
ResidualCell.outputRange s out 18, ← ResidualCell.outputRange s out 0⟩`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.check` uses this definition
in the displayed construction of `check`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def summarize (s : Nat) (ops : List Op) (r : Row) : Option Summary := do
  let out ← Poly.Taylor.evalProgram s r.degree r.inputs r.checkpoints ops
  return ⟨← ResidualCell.outputRange s out 26,
    ← ResidualCell.outputRange s out 18, ← ResidualCell.outputRange s out 0⟩

/--
Defines `Summary.check` of type `Bool` by `decide ( 0<b.den.lower s ∧ 0<b.speed.lower s ∧ 0≤ε ∧
b.residual.magnitude s≤ε*(b.den.lower s*b.speed.lower s))`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.check` uses this definition
in the displayed construction of `check`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Summary.check (s : Nat) (ε : ℚ) (b : Summary) : Bool := decide (
  0<b.den.lower s ∧ 0<b.speed.lower s ∧ 0≤ε ∧
    b.residual.magnitude s≤ε*(b.den.lower s*b.speed.lower s))

/--
Defines `check` of type `Bool` by `(summarize s ops r).any (Summary.check s ε)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.check_sound` rewrites with
this definition to prove the bound `|R.directContactCore (σ :=
(sigma:ℝ)) (by exact_mod_cast hsigma) t-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def check (s : Nat) (ops : List Op) (ε : ℚ) (r : Row) : Bool :=
  (summarize s ops r).any (Summary.check s ε)

/--
The precise assertion is `result.Mem s (source.value v)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.check_sound` uses this
assertion to prove the bound `|R.directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast hsigma) t-g|≤(ε:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Poly.Taylor.source_enclosed_at` with the arguments
shown in the proof.
-/
theorem sourceRange_sound {s : Nat} (hs : 0<s) {ops : List Op} {r : Row}
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) {v : Nat → ℝ}
    (hv : Poly.Taylor.Encloses s r.inputs x v) {out : List (List Bounds)}
    (he : Poly.Taylor.evalProgram s r.degree r.inputs r.checkpoints ops=some out)
    {i : Nat} {source : Expr} (hsource : codeExpressionCheck ops i source=true)
    {result : Bounds} (hr : ResidualCell.outputRange s out i=some result) :
    result.Mem s (source.value v) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.Poly.Taylor.source_enclosed_at` with the
  -- arguments shown in the proof.
  obtain ⟨p,hp,hrange⟩ : ∃ p, out[i]?=some p ∧ Poly.range s ⟨0,s⟩ p=some result := by
    simpa only [ResidualCell.outputRange,Option.bind_eq_bind,Option.bind_eq_some_iff] using hr
  exact Poly.Taylor.source_enclosed_at hs hx ops hv he hsource hp hrange

/--
The stated quantitative bound `|R.directContactCore (σ := (sigma:ℝ)) (by exact_mod_cast hsigma)
t-g|≤(ε:ℝ)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.Panel.valuePanel_actual`
uses this identity to establish `(p.valuePanel s ε).Actual s
(R.directContactCore (σ := (sigma:ℝ)) (by exact_mod_cast hsigma))`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.error_bound`,
`chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.sourceRange_sound` with the
arguments shown in the proof.
-/
theorem check_sound {s : Nat} (hs : 0<s) {ops : List Op} (R : ReferenceData)
    (hk : R.k=Real.pi^2/4) {sigma : ℚ} (hsigma : 0<sigma) {ε : ℚ}
    (shapeD : codeExpressionCheck ops 26 (ContactExpr.gammaDen sigma)=true)
    (shapeV : codeExpressionCheck ops 18 ContactExpr.speed=true)
    (shapeE : codeExpressionCheck ops 0 (ContactExpr.residual sigma)=true)
    {r : Row} (hc : check s ops ε r=true) {x t g : ℝ}
    (hx : x∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (hv : Poly.Taylor.Encloses s r.inputs x
      (ContactExpr.values t (R.normalizedRoot t)
        (R.normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t)
        (R.normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t) g)) :
    |R.directContactCore (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t-g|≤(ε:ℝ) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.error_bound`,
  -- `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.sourceRange_sound` with the
  -- arguments shown in the proof.
  cases he : summarize s ops r with
  | none => simp [check,he] at hc
  | some b =>
    have hb : b.check s ε=true := by simpa [check,he] using hc
    obtain ⟨out,hout,D,hD,V,hV,E,hE,heq⟩ :
        ∃ out, Poly.Taylor.evalProgram s r.degree r.inputs r.checkpoints ops=some out ∧
        ∃ D, ResidualCell.outputRange s out 26=some D ∧
        ∃ V, ResidualCell.outputRange s out 18=some V ∧
        ∃ E, ResidualCell.outputRange s out 0=some E ∧ Summary.mk D V E=b := by
      simpa only [summarize,Option.bind_eq_bind,Option.bind_eq_some_iff,
        Option.pure_def,Option.some.injEq] using he
    subst b
    exact error_bound R hk hsigma ht hs (sourceRange_sound hs hx hv hout shapeD hD)
      (sourceRange_sound hs hx hv hout shapeV hV) (sourceRange_sound hs hx hv hout shapeE hE)
      (of_decide_eq_true hb)

end chebyshev2.Numerics.IntegerCertificate.ContactPolynomial
