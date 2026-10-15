import «2610.05164v2».Numerics.ContactModelSound
import «2610.05164v2».Numerics.ValueQuadrature
import «2610.05164v2».Numerics.IntegerReferenceTrajectory

/-!
Article: 2610.05164v2, Section 4.1.
Contact Actual.
Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.valuePanel_actual` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.ValidPanel.actual` (actual).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate
noncomputable section
open Set Polynomial «2610.05164v2».Calibration «2610.05164v2».DualCertificate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Membership in the specified domain/enclosure: `t∈Icc (0:ℝ) 1`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.ValidPanel.actual` uses this assertion
to establish `(p.valuePanel scale epsilon).Actual scale
((ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem ResidualCell.Row.left_interval_mem {s : Nat} (hs : 0<s) (r : ResidualCell.Row)
    (hc : ResidualCell.leftChartCheck s r=true) {t : ℝ}
    (ht : t∈Icc (r.left s) (r.right s)) : t∈Icc (0:ℝ) 1 := by
  obtain ⟨_,ha,hb⟩ := of_decide_eq_true hc
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  refine ⟨(div_nonneg (by exact_mod_cast ha) hs'.le).trans ht.1,ht.2.trans ?_⟩
  rw [ResidualCell.Row.right,div_le_iff₀ hs',one_mul]
  exact_mod_cast hb

/--
The stated quantitative bound `|(ReferenceJetSource.referenceData R).normalizedRoot t-
(Poly.exactPolynomial s r.z).eval (r.localCoordinate s t)|≤(r.delta:ℝ)`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.ValidPanel.actual` uses this bound to
establish the precise assertion is `(p.valuePanel scale epsilon).Actual scale
((ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.coordinate_eval`,
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_root_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.local_mem` with the arguments
shown in the proof.
-/
theorem ResidualCell.Row.root_error_left {s : Nat} (hs : 0<s) {ops : List Op} {piB : Bounds}
    (hpi : piB.Mem s Real.pi) (R : RationalReference) (η : ℚ)
    (shapeK : codeExpressionCheck ops 72 ResidualExpr.k=true)
    (shapeD : codeExpressionCheck ops 30 (ResidualExpr.profileParts R).1=true)
    (shapeRoot : codeExpressionCheck ops 16 (ResidualExpr.rootResidual R)=true)
    (r : ResidualCell.Row) (hc : ResidualCell.check s ops piB η r=true)
    (href : r.reflected=false) {t : ℝ} (ht : t∈Icc (r.left s) (r.right s))
    (ht01 : t∈Icc (0:ℝ) 1) :
    |(ReferenceJetSource.referenceData R).normalizedRoot t-
      (Poly.exactPolynomial s r.z).eval (r.localCoordinate s t)|≤(r.delta:ℝ) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.coordinate_eval`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.check_root_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.Row.local_mem` with the arguments
  -- shown in the proof.
  have hh : decide (0<r.width ∧ r.width*r.step=s)=true ∧
      (ResidualCell.summarize s ops piB r).any (ResidualCell.Summary.check s r.delta η)=true := by
    simpa only [ResidualCell.check,Bool.and_eq_true] using hc
  have hw : 0<r.width ∧ r.width*r.step=s := of_decide_eq_true hh.1
  have he : (ResidualCell.values s r 0).eval (r.localCoordinate s t)=t := by
    simpa only [ResidualCell.Row.chart,href,Bool.false_eq_true,↓reduceIte] using
      r.coordinate_eval hs hw.2 t
  have h := ResidualCell.check_root_sound hs hpi R η shapeK shapeD shapeRoot hc
    (r.local_mem hs hw.1 hw.2 ht) (by rw [he]; exact ht01)
  rw [he] at h
  exact h

namespace ContactPolynomial
/--
Constructs `Panel.valuePanel` of type `Poly.ValuePanel` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.valuePanel_actual`
uses this definition to establish `(p.valuePanel s ε).Actual s (R.directContactCore (σ :=
(sigma:ℝ)) (by exact_mod_cast hsigma))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Panel.valuePanel (s : Nat) (ε : ℚ) (p : Panel) : Poly.ValuePanel where
  domain := ⟨(p.start:ℚ)/s,((p.start:ℚ)+p.width)/s⟩
  coefficients := p.g
  error := ε

/--
The precise assertion is `(p.valuePanel s ε).Actual s (R.directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast hsigma))`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.ValidPanel.actual` uses this identity
to establish `(p.valuePanel scale epsilon).Actual scale
((ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.check_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.time_mem`,
`«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.inputs_sound` with the
arguments shown in the proof.
-/
theorem Panel.valuePanel_actual {s : Nat} (hs : 0<s) {piB : Bounds}
    (hpi : piB.Mem s Real.pi) {eL eR : Int} (p : Panel)
    (hc : p.modelCheck s piB eL eR=true) (R : ReferenceData) (hk : R.k=Real.pi^2/4)
    {sigma : ℚ} (hsigma : 0<sigma) {ops : List Op} {ε : ℚ}
    (shapeD : codeExpressionCheck ops 26 (ContactExpr.gammaDen sigma)=true)
    (shapeV : codeExpressionCheck ops 18 ContactExpr.speed=true)
    (shapeE : codeExpressionCheck ops 0 (ContactExpr.residual sigma)=true)
    (hcheck : check s ops ε p.row=true)
    (hleft : ∀ t∈Icc (p.left.left s) (p.left.right s),
      |R.normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t-
        p.left.approx s t|≤(eL:ℝ)/s)
    (hright : ∀ v∈Icc (p.right.left s) (p.right.right s),
      |R.normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) (2-v)-
        p.right.approx s v|≤(eR:ℝ)/s)
    (hroot : ∀ t∈Icc (p.left.left s) (p.left.right s),
      |R.normalizedRoot t-(Poly.exactPolynomial s p.left.z).eval
        (p.left.localCoordinate s t)|≤(p.left.delta:ℝ)) :
    (p.valuePanel s ε).Actual s
      (R.directContactCore (σ := (sigma:ℝ)) (by exact_mod_cast hsigma)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.check_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.time_mem`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.ContactPolynomial.Panel.inputs_sound` with the
  -- arguments shown in the proof.
  intro x hx
  have h := check_sound hs R hk hsigma shapeD shapeV shapeE hcheck hx
    (p.time_mem hs hc hx).1
    (p.inputs_sound hs hpi hc R (by exact_mod_cast hsigma) hleft hright hroot hx)
  have he : (((p.valuePanel s ε).domain.lo:ℝ)+
      (((p.valuePanel s ε).domain.hi:ℝ)-(p.valuePanel s ε).domain.lo)*x)=p.time s x := by
    dsimp [valuePanel,time]
    push_cast
    ring
  change |R.directContactCore (σ := (sigma:ℝ)) (by exact_mod_cast hsigma)
    (((p.valuePanel s ε).domain.lo:ℝ)+
      (((p.valuePanel s ε).domain.hi:ℝ)-(p.valuePanel s ε).domain.lo)*x)-
      (Poly.exactPolynomial s p.g).eval x|≤(ε:ℝ)
  rw [he]
  exact h

end ContactPolynomial
end
end «2610.05164v2».Numerics.IntegerCertificate
