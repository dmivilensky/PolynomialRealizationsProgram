import chebyshev2.Numerics.AmplitudeCheck
import chebyshev2.Numerics.TaylorInputExtension

/-!
Article: chebyshev2, Section 4.1.
Amplitude Actual.
Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.Panel.actual_of_inputs` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.ValidPanel.actual` (actual).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial
noncomputable section
open Set Polynomial chebyshev2.Calibration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
The precise assertion is `Poly.Taylor.pushValue h (Poly.Taylor.pushValue g (ContactExpr.values
t r l u c))= AmplitudeExpr.values t Real.pi r l u c h g`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.Panel.actual_of_inputs`
rewrites with this identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem extended_values (t r l u c h g : ℝ) :
    Poly.Taylor.pushValue h (Poly.Taylor.pushValue g (ContactExpr.values t r l u c))=
      AmplitudeExpr.values t Real.pi r l u c h g := by
  funext i
  rcases i with _|_|_|_|_|_|_|_|i <;> rfl

/--
The stated quantitative bound `(p.valuePanel s ε).Actual s (fun t => 6*t^2* (R.calibration (σ
:= (sigma:ℝ)) (b := (b:ℝ)) (ω := (omega:ℝ)) (by exact_mod_cast hσ) (by exact_mod_cast hb) (by
exact_mod_cast hω)).amplitude (Real.pi^2/4) (t^3))`.

Use: `chebyshev2.Certificates.Compact.AmplitudeValues.ValidPanel.actual` uses this identity
to establish `(p.valuePanel scale epsilon).Actual scale integrand`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Poly.Taylor.cons_encloses`,
`chebyshev2.Numerics.IntegerCertificate.Poly.Rep.at`,
`chebyshev2.Numerics.IntegerCertificate.Poly.exactBounds_sound` with the arguments shown in
the proof.
-/
theorem Panel.actual_of_inputs {s : Nat} (hs : 0<s) {piB : Bounds} {eL eR : Int}
    (p : Panel) (hc : p.base.modelCheck s piB eL eR=true) (R : ReferenceData)
    {sigma b omega : ℚ} (hσ : 0<sigma) (hb : 0<b) (hω : 0≤omega) {ops : List Op} {ε : ℚ}
    (shapeK : codeExpressionCheck ops 33 AmplitudeExpr.k=true)
    (shapeD : codeExpressionCheck ops 29 (AmplitudeExpr.den sigma)=true)
    (shapeE : codeExpressionCheck ops 5 (AmplitudeExpr.rootResidual sigma b omega)=true)
    (shapeQ : codeExpressionCheck ops 0 AmplitudeExpr.quadratureResidual=true)
    (hcheck : check s ops ε p=true)
    (hbase : ∀ x∈Icc (0:ℝ) 1,Poly.Taylor.Encloses s p.base.row.inputs x
      (ContactExpr.values (p.base.time s x) (R.normalizedRoot (p.base.time s x))
        (R.normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hσ) (p.base.time s x))
        (R.normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hσ) (p.base.time s x))
        ((Poly.exactPolynomial s p.base.g).eval x))) :
    (p.valuePanel s ε).Actual s (fun t => 6*t^2*
      (R.calibration (σ := (sigma:ℝ)) (b := (b:ℝ)) (ω := (omega:ℝ))
        (by exact_mod_cast hσ) (by exact_mod_cast hb) (by exact_mod_cast hω)).amplitude
          (Real.pi^2/4) (t^3)) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.Poly.Taylor.cons_encloses`,
  -- `chebyshev2.Numerics.IntegerCertificate.Poly.Rep.at`,
  -- `chebyshev2.Numerics.IntegerCertificate.Poly.exactBounds_sound` with the arguments
  -- shown in the proof.
  intro x hx
  have hv := Poly.Taylor.cons_encloses ((Poly.exactBounds_sound hs p.H).at x)
    (Poly.Taylor.cons_encloses ((Poly.exactBounds_sound hs p.g).at x) (hbase x hx))
  rw [extended_values] at hv
  have h := check_sound hs R hσ hb hω shapeK shapeD shapeE shapeQ hcheck hx
    (p.base.time_mem hs hc hx).1 rfl rfl hv
  have he : (((p.valuePanel s ε).domain.lo:ℝ)+
      (((p.valuePanel s ε).domain.hi:ℝ)-(p.valuePanel s ε).domain.lo)*x)=p.base.time s x := by
    dsimp [valuePanel,ContactPolynomial.Panel.valuePanel,ContactPolynomial.Panel.time]
    push_cast
    ring
  change |6*(((p.valuePanel s ε).domain.lo:ℝ)+
      (((p.valuePanel s ε).domain.hi:ℝ)-(p.valuePanel s ε).domain.lo)*x)^2*
      (R.calibration (σ := (sigma:ℝ)) (b := (b:ℝ)) (ω := (omega:ℝ))
        (by exact_mod_cast hσ) (by exact_mod_cast hb) (by exact_mod_cast hω)).amplitude
        (Real.pi^2/4) ((((p.valuePanel s ε).domain.lo:ℝ)+
          (((p.valuePanel s ε).domain.hi:ℝ)-(p.valuePanel s ε).domain.lo)*x)^3)-
      (Poly.exactPolynomial s p.g).eval x|≤(ε:ℝ)
  rw [he]
  exact h

end
end chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial
