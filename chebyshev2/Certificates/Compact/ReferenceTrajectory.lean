import chebyshev2.Certificates.Compact.ReferenceResiduals
import chebyshev2.Certificates.Compact.ReferenceTrajectoryData

/-!
Article: chebyshev2, Section 4.1.
Reference Trajectory.
Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.full_trajectory` feeds
`chebyshev2.Certificates.Compact.ReferenceConstant.endpoint_mem` (endpoint mem).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Certificates.Compact.ReferenceTrajectory
noncomputable section
open Set chebyshev2.Numerics chebyshev2.Numerics.IntegerCertificate
open chebyshev2.Certificates.DualInputs ReferenceResiduals
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
/--
The stated quantitative bound `(∀ r∈leftRows, ∀ t∈Icc (r.left scale) (r.right scale),
|(ReferenceJetSource.referenceData reference).normalizedFilter (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1) t-r.approx scale t|≤(leftBound:ℝ)) ∧ (∀ r∈rightRows, ∀ t∈Icc
(r.left scale) (r.right scale), |ReferenceJetSource.rightFilter reference reference_signs.1
t-r.approx scale t|≤(rightBound:ℝ)) ∧ |ReferenceJetSource.rightFilter reference
reference_signs.1 2- (ResidualCell.lastValue scale (ResidualCell.lastValue scale 0 leftRows)
rightRows:ℝ)|≤ (rightBound:ℝ)`.

Use: `chebyshev2.Certificates.Compact.ContactValues.ValidPanel.actual` uses this identity
to establish `(p.valuePanel scale epsilon).Actual scale
((ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1))`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem full_trajectory :
    (∀ r∈leftRows, ∀ t∈Icc (r.left scale) (r.right scale),
      |(ReferenceJetSource.referenceData reference).normalizedFilter (σ := (sigma:ℝ))
        (by exact_mod_cast reference_signs.1) t-r.approx scale t|≤(leftBound:ℝ)) ∧
    (∀ r∈rightRows, ∀ t∈Icc (r.left scale) (r.right scale),
      |ReferenceJetSource.rightFilter reference reference_signs.1 t-r.approx scale t|≤(rightBound:ℝ)) ∧
    |ReferenceJetSource.rightFilter reference reference_signs.1 2-
      (ResidualCell.lastValue scale (ResidualCell.lastValue scale 0 leftRows) rightRows:ℝ)|≤
        (rightBound:ℝ) := by
  -- Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
  -- against the proved checker; a generator's numerical report is not a premise.
  apply ResidualCell.complete_reference_chain (by decide +kernel) pi_mem reference sigma eta
    shapeK shapeD shapeRoot shapeFactor shapeODE reference_signs.1 (by decide +kernel)
    leftRows rightRows leftBound rightBound ?_ ?_ ?_ left_chain right_chain
  · intro r hr
    rw [split_rows] at hr
    exact checks r hr
  · exact List.all_eq_true.mp left_charts
  · exact List.all_eq_true.mp right_charts

end
end chebyshev2.Certificates.Compact.ReferenceTrajectory
