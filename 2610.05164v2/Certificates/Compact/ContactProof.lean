import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectory
import «2610.05164v2».Numerics.ContactActual

/-!
Article: 2610.05164v2, Section 4.1.
Contact Proof.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.ValidPanel.actual` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_error` (contact integral error).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Certificates.Compact.ContactValues
noncomputable section
open Set «2610.05164v2».Numerics «2610.05164v2».Numerics.IntegerCertificate
open «2610.05164v2».Certificates.DualInputs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
The stated quantitative bound `(ReferenceTrajectory.leftBound:ℝ)≤(leftRadius:ℝ)/scale`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.ValidPanel.actual` uses this bound to
establish the precise assertion is `(p.valuePanel scale epsilon).Actual scale
((ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem leftRadius_bound : (ReferenceTrajectory.leftBound:ℝ)≤(leftRadius:ℝ)/scale := by
  exact_mod_cast (show ReferenceTrajectory.leftBound≤(leftRadius:ℚ)/scale by decide +kernel)
/--
The stated quantitative bound `(ReferenceTrajectory.rightBound:ℝ)≤(rightRadius:ℝ)/scale`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.ValidPanel.actual` uses this bound to
establish the precise assertion is `(p.valuePanel scale epsilon).Actual scale
((ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem rightRadius_bound : (ReferenceTrajectory.rightBound:ℝ)≤(rightRadius:ℝ)/scale := by
  exact_mod_cast (show ReferenceTrajectory.rightBound≤(rightRadius:ℚ)/scale by decide +kernel)

/--
The precise assertion is `Poly.Taylor.Encloses scale p.row.inputs x (ContactExpr.values (p.time
scale x) ((ReferenceJetSource.referenceData reference).normalizedRoot (p.time scale x))
((ReferenceJetSource.referenceData reference).normalizedFilter (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1) (p.time scale x)) ((ReferenceJetSource.referenceData
reference).normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1)
(p.time scale x)) ((Poly.exactPolynomial scale p.g).eval x))`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.ValidPanel.actual` uses this identity
to establish `(p.valuePanel scale epsilon).Actual scale integrand`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem ValidPanel.inputs {p : ContactPolynomial.Panel} (hp : ValidPanel p)
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    Poly.Taylor.Encloses scale p.row.inputs x
      (ContactExpr.values (p.time scale x)
        ((ReferenceJetSource.referenceData reference).normalizedRoot (p.time scale x))
        ((ReferenceJetSource.referenceData reference).normalizedFilter
          (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) (p.time scale x))
        ((ReferenceJetSource.referenceData reference).normalizedReflectedFilter
          (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1) (p.time scale x))
        ((Poly.exactPolynomial scale p.g).eval x)) := by
  -- Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
  -- against the proved checker; a generator's numerical report is not a premise.
  let R := ReferenceJetSource.referenceData reference
  have hs : 0<scale := by decide +kernel
  have hleft : p.left∈ReferenceTrajectory.leftRows := hp.2.2.1
  have hright : p.right∈ReferenceTrajectory.rightRows := hp.2.2.2
  have hchart := List.all_eq_true.mp ReferenceTrajectory.left_charts p.left hleft
  have href : p.left.reflected=false := (of_decide_eq_true hchart).1
  have hmem : p.left∈ReferenceResiduals.rows := by
    rw [← ReferenceTrajectory.split_rows]
    exact List.mem_append_left _ hleft
  have hcheck := ReferenceResiduals.checks p.left hmem
  apply p.inputs_sound hs ReferenceResiduals.pi_mem hp.1 R
    (by exact_mod_cast reference_signs.1) ?_ ?_ ?_ hx
  · intro t ht
    exact (ReferenceTrajectory.full_trajectory.1 p.left hleft t ht).trans leftRadius_bound
  · intro v hv
    convert! (ReferenceTrajectory.full_trajectory.2.1 p.right hright v hv).trans
      rightRadius_bound using 1
  · intro t ht
    exact p.left.root_error_left hs ReferenceResiduals.pi_mem reference ReferenceResiduals.eta
      ReferenceResiduals.shapeK ReferenceResiduals.shapeD ReferenceResiduals.shapeRoot
      hcheck href ht (p.left.left_interval_mem hs hchart ht)


/--
The precise assertion is `(p.valuePanel scale epsilon).Actual scale
((ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1))`.

Use: `«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_error` uses this
identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem ValidPanel.actual {p : ContactPolynomial.Panel} (hp : ValidPanel p) :
    (p.valuePanel scale epsilon).Actual scale
      ((ReferenceJetSource.referenceData reference).directContactCore
        (σ := (sigma:ℝ)) (by exact_mod_cast reference_signs.1)) := by
  -- Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
  -- against the proved checker; a generator's numerical report is not a premise.
  let R := ReferenceJetSource.referenceData reference
  have hs : 0<scale := by decide +kernel
  have hR : R.k=Real.pi^2/4 := rfl
  have hleft : p.left∈ReferenceTrajectory.leftRows := hp.2.2.1
  have hright : p.right∈ReferenceTrajectory.rightRows := hp.2.2.2
  have hchart := List.all_eq_true.mp ReferenceTrajectory.left_charts p.left hleft
  have href : p.left.reflected=false := (of_decide_eq_true hchart).1
  have hmem : p.left∈ReferenceResiduals.rows := by
    rw [← ReferenceTrajectory.split_rows]
    exact List.mem_append_left _ hleft
  have hcheck := ReferenceResiduals.checks p.left hmem
  apply p.valuePanel_actual hs ReferenceResiduals.pi_mem hp.1 R hR reference_signs.1
    shapeD shapeV shapeE hp.2.1
  · intro t ht
    exact (ReferenceTrajectory.full_trajectory.1 p.left hleft t ht).trans leftRadius_bound
  · intro v hv
    convert! (ReferenceTrajectory.full_trajectory.2.1 p.right hright v hv).trans
      rightRadius_bound using 1
  · intro t ht
    exact p.left.root_error_left hs ReferenceResiduals.pi_mem reference ReferenceResiduals.eta
      ReferenceResiduals.shapeK ReferenceResiduals.shapeD ReferenceResiduals.shapeRoot
      hcheck href ht (p.left.left_interval_mem hs hchart ht)

end
end «2610.05164v2».Certificates.Compact.ContactValues
