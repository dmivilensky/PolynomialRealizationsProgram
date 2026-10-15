import «2610.05164v2».Numerics.AmplitudePolynomial

/-!
Article: 2610.05164v2, Section 4.1.
Amplitude Check.
Use: `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.check_sound` feeds
`«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.Panel.actual_of_inputs` (actual of
inputs).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial
noncomputable section
open Set Polynomial «2610.05164v2».Calibration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
An amplitude panel based on the same contact panel, or the computed amplitude-residual summary.
The cubic-root and primitive polynomials are tied to the actual calibration by the checker's
soundness theorem.

Use: `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.Panel.row` uses this
record of data and proof obligations in the displayed construction of `Panel.row`. Its inputs
and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure Panel where
  /-- The underlying contact panel, ensuring both quadratures use identical reference rows and time endpoints. -/
  base : ContactPolynomial.Panel
  /-- Scaled coefficients of the proposed calibrated cubic-root polynomial. -/
  H : List Int
  /-- Scaled coefficients of the proposed amplitude-integral primitive. -/
  g : List Int
  /-- Retained degree of the polynomial amplitude residual program. -/
  degree : Nat
  /-- Optional node enclosures, each independently verified by the checker. -/
  checkpoints : List (Option (List Bounds))
  deriving Repr, DecidableEq

/--
Defines `Panel.row` of type `ContactPolynomial.Row` by `⟨Poly.exactBounds p.H::Poly.exactBounds
p.g::p.base.row.inputs,p.degree,p.checkpoints⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.check_sound` uses this
definition to prove the bound `|6*t^2*(R.calibration (σ := (sigma:ℝ))
(b := (b:ℝ)) (ω := (omega:ℝ)) (by exact_mod_cast hσ) (by exact_mod_cast hb) (by exact_mod_cast
hω)).amplitude (Real.pi^2/4) (t^3)-g|≤(ε:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Panel.row (p : Panel) : ContactPolynomial.Row :=
  ⟨Poly.exactBounds p.H::Poly.exactBounds p.g::p.base.row.inputs,p.degree,p.checkpoints⟩
/--
Defines `Panel.valuePanel` of type `Poly.ValuePanel` by `{p.base.valuePanel s ε with
coefficients := p.g}`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.quadraturePanels` uses this
definition in the displayed construction of `quadraturePanels`. Its inputs and component
formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Panel.valuePanel (s : Nat) (ε : ℚ) (p : Panel) : Poly.ValuePanel :=
  {p.base.valuePanel s ε with coefficients := p.g}

/--
An amplitude panel based on the same contact panel, or the computed amplitude-residual summary.
The cubic-root and primitive polynomials are tied to the actual calibration by the checker's
soundness theorem.

Use: `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.check` uses this record of
data and proof obligations in the displayed construction of `check`. Its inputs and component
formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure Summary where
  /-- Computed enclosure of the ground parameter. -/
  k : Bounds
  /-- Computed enclosure of the amplitude denominator. -/
  den : Bounds
  /-- Computed enclosure of the cubic-root residual. -/
  root : Bounds
  /-- Computed enclosure of the quadrature residual. -/
  quad : Bounds
  /-- Computed enclosure of the proposed calibrated cubic-root value. -/
  H : Bounds
  deriving Repr, DecidableEq

/--
Defines `summarize` of type `Option Summary` by `do let out ← Poly.Taylor.evalProgram s
p.degree p.row.inputs p.checkpoints ops return ⟨← ResidualCell.outputRange s out 33, ←
ResidualCell.outputRange s out 29, ← ResidualCell.outputRange s out 5, ←
ResidualCell.outputRange s out 0, ← Poly.range s ⟨0,s⟩ (Poly.exactBounds p.H)⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.check` uses this
definition in the displayed construction of `check`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def summarize (s : Nat) (ops : List Op) (p : Panel) : Option Summary := do
  let out ← Poly.Taylor.evalProgram s p.degree p.row.inputs p.checkpoints ops
  return ⟨← ResidualCell.outputRange s out 33, ← ResidualCell.outputRange s out 29,
    ← ResidualCell.outputRange s out 5, ← ResidualCell.outputRange s out 0,
    ← Poly.range s ⟨0,s⟩ (Poly.exactBounds p.H)⟩

/--
Defines `Summary.check` of type `Bool` by `decide ( 0<b.k.lower s ∧ 0<b.den.lower s ∧
(1/2:ℚ)≤b.H.lower s ∧ 0≤b.root.magnitude s ∧ 24*b.root.magnitude s/(b.den.lower s*b.k.lower
s)+b.quad.magnitude s≤ε)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.check` uses this
definition in the displayed construction of `check`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Summary.check (s : Nat) (ε : ℚ) (b : Summary) : Bool := decide (
  0<b.k.lower s ∧ 0<b.den.lower s ∧ (1/2:ℚ)≤b.H.lower s ∧
  0≤b.root.magnitude s ∧
  24*b.root.magnitude s/(b.den.lower s*b.k.lower s)+b.quad.magnitude s≤ε)
/--
Defines `check` of type `Bool` by `(summarize s ops p).any (Summary.check s ε)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.check_sound` rewrites with
this definition to prove the bound `|6*t^2*(R.calibration (σ :=
(sigma:ℝ)) (b := (b:ℝ)) (ω := (omega:ℝ)) (by exact_mod_cast hσ) (by exact_mod_cast hb) (by
exact_mod_cast hω)).amplitude (Real.pi^2/4) (t^3)-g|≤(ε:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def check (s : Nat) (ops : List Op) (ε : ℚ) (p : Panel) : Bool :=
  (summarize s ops p).any (Summary.check s ε)

/--
The stated quantitative bound `|6*t^2*(R.calibration (σ := (sigma:ℝ)) (b := (b:ℝ)) (ω :=
(omega:ℝ)) (by exact_mod_cast hσ) (by exact_mod_cast hb) (by exact_mod_cast hω)).amplitude
(Real.pi^2/4) (t^3)-g|≤(ε:ℝ)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.Panel.actual_of_inputs`
uses this identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.sourceRange_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.cleared_error` with the
arguments shown in the proof.
-/
theorem check_sound {s : Nat} (hs : 0<s) {ops : List Op} (R : ReferenceData)
    {sigma b omega : ℚ} (hσ : 0<sigma) (hb : 0<b) (hω : 0≤omega) {ε : ℚ}
    (shapeK : codeExpressionCheck ops 33 AmplitudeExpr.k=true)
    (shapeD : codeExpressionCheck ops 29 (AmplitudeExpr.den sigma)=true)
    (shapeE : codeExpressionCheck ops 5 (AmplitudeExpr.rootResidual sigma b omega)=true)
    (shapeQ : codeExpressionCheck ops 0 AmplitudeExpr.quadratureResidual=true)
    {p : Panel} (hc : check s ops ε p=true) {x t r l u c h g : ℝ}
    (hx : x∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (hl : l=R.normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hσ) t)
    (hu : u=R.normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hσ) t)
    (hv : Poly.Taylor.Encloses s p.row.inputs x
      (AmplitudeExpr.values t Real.pi r l u c h g)) :
    |6*t^2*(R.calibration (σ := (sigma:ℝ)) (b := (b:ℝ)) (ω := (omega:ℝ))
      (by exact_mod_cast hσ) (by exact_mod_cast hb) (by exact_mod_cast hω)).amplitude
        (Real.pi^2/4) (t^3)-g|≤(ε:ℝ) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.sourceRange_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.cleared_error` with the
  -- arguments shown in the proof.
  cases he : summarize s ops p with
  | none => simp [check,he] at hc
  | some B =>
    have hB : B.check s ε=true := by simpa [check,he] using hc
    obtain ⟨out,hout,K,hK,D,hD,E,hE,Qb,hQ,Hb,hH,heq⟩ :
        ∃ out, Poly.Taylor.evalProgram s p.degree p.row.inputs p.checkpoints ops=some out ∧
        ∃ K, ResidualCell.outputRange s out 33=some K ∧
        ∃ D, ResidualCell.outputRange s out 29=some D ∧
        ∃ E, ResidualCell.outputRange s out 5=some E ∧
        ∃ Qb, ResidualCell.outputRange s out 0=some Qb ∧
        ∃ Hb, Poly.range s ⟨0,s⟩ (Poly.exactBounds p.H)=some Hb ∧ Summary.mk K D E Qb Hb=B := by
      simpa only [summarize,Option.bind_eq_bind,Option.bind_eq_some_iff,
        Option.pure_def,Option.some.injEq] using he
    subst B
    have hK' := ContactPolynomial.sourceRange_sound hs hx hv hout shapeK hK
    have hD' := ContactPolynomial.sourceRange_sound hs hx hv hout shapeD hD
    have hE' := ContactPolynomial.sourceRange_sound hs hx hv hout shapeE hE
    have hQ' := ContactPolynomial.sourceRange_sound hs hx hv hout shapeQ hQ
    rw [AmplitudeExpr.k_value] at hK'
    rw [AmplitudeExpr.den_value,hl,hu] at hD'
    rw [AmplitudeExpr.rootResidual_value,hl,hu] at hE'
    rw [AmplitudeExpr.quadratureResidual_value] at hQ'
    obtain ⟨hp,hhp,hh⟩ := hv 0 (Poly.exactBounds p.H) rfl
    have hxi : (⟨0,s⟩:Bounds).Mem s x := by
      constructor <;> dsimp [Bounds.Mem]
      · simpa using mul_nonneg (Nat.cast_nonneg s) hx.1
      · simpa using mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg s)
    have hH' := Poly.range_sound hs hhp hxi hH
    change hp.eval x=h at hh
    rw [hh] at hH'
    obtain ⟨hkl,hdl,hlo,her,hbudget⟩ := of_decide_eq_true hB
    have hkl' : (0:ℝ)<(K.lower s:ℝ) := by exact_mod_cast hkl
    have hdl' : (0:ℝ)<(D.lower s:ℝ) := by exact_mod_cast hdl
    have hlo' : (1/2:ℝ)≤(Hb.lower s:ℝ) := by
      have hh : ((1/2:ℚ):ℝ)≤(Hb.lower s:ℝ) := by exact_mod_cast hlo
      norm_num at hh ⊢
      exact hh
    have her' : (0:ℝ)≤(E.magnitude s:ℝ) := by exact_mod_cast her
    have hbudget' : 24*(E.magnitude s:ℝ)/((D.lower s:ℝ)*(K.lower s:ℝ))+
        (Qb.magnitude s:ℝ)≤(ε:ℝ) := by exact_mod_cast hbudget
    apply (cleared_error R (by exact_mod_cast hσ) (by exact_mod_cast hb) (by exact_mod_cast hω)
      (by positivity : (0:ℝ)<Real.pi^2/4) hkl' (Bounds.real_mem hs hK').1 ht
      (hlo'.trans (Bounds.real_mem hs hH').1) hdl' (Bounds.real_mem hs hD').1 her'
      (Bounds.real_abs hs hE') (Bounds.real_abs hs hQ')).trans hbudget'

end
end «2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial
