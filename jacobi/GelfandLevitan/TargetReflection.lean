import jacobi.GelfandLevitan.TargetGreenOperator

/-!
Article: jacobi, Appendix C.2.
Physical reflection preserves the full target graph domain and commutes
with the actual unbounded operator and bounded Green inverse. Every
identity is checked on the complete original reflected transformed basis.
Use: targetOperator_reflection_mem, targetOperator_reflection and targetGreen_reflection prove physical reflection invariance on the full original domains.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Reflection multiplies every original target coordinate by its genuine spectral parity sign.
Use: targetOperator_reflection_mem, targetOperator_reflection and targetGreen_reflection prove physical reflection invariance on the full original domains.
Article: jacobi, Proposition C.2.
Proof: move the genuine symmetric unitary reflection onto the original basis vector and insert its proved exact parity. -/
theorem target_reflection_coordinates (a : ℝ) (ha : -1<a) (v : Space) (k : ℕ) :
    (fullTargetBasis a ha).repr (reflectionUnitary v) k=
      (-1:ℝ)^k*(fullTargetBasis a ha).repr v k := by
  rw [(fullTargetBasis a ha).repr_apply_apply,(fullTargetBasis a ha).repr_apply_apply,
    ← reflectionUnitary_inner,fullTargetBasis_reflection,real_inner_smul_left]

/-- Actual physical reflection preserves the entire original unbounded target graph domain.
Use: targetOperator_reflection states commutation as an actual full-domain operator equality, with genuine domain membership proved first.
Article: jacobi, Proposition C.2.
Proof: the reflected actual operator value is a graph witness. The proved genuine parity coordinate formula commutes with multiplication by each original sigma_k. -/
theorem targetOperator_reflection_mem (a : ℝ) (ha : -1<a) (v : (targetOperator a ha).domain) :
    reflectionUnitary (v:Space)∈(targetOperator a ha).domain := by
  refine ⟨reflectionUnitary (targetOperator a ha v),fun k => ?_⟩
  have h := chebyshev2.Continuum.unboundedDiagonalOperator_graph
    (fullTargetBasis a ha) (jacobi.Bessel.sigma a ha) v k
  change (fullTargetBasis a ha).repr (targetOperator a ha v) k=_ at h
  rw [target_reflection_coordinates,target_reflection_coordinates,h]
  ring

/-- The actual full target operator commutes with genuine physical reflection on its entire original unbounded domain.
Use: completes the spectral operator reflection assertion in Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: compare all coordinates in the original complete target basis, using the actual full graph equation and the proved original parity coordinate identity. -/
theorem targetOperator_reflection (a : ℝ) (ha : -1<a) (v : (targetOperator a ha).domain) :
    targetOperator a ha ⟨reflectionUnitary (v:Space),targetOperator_reflection_mem a ha v⟩=
      reflectionUnitary (targetOperator a ha v) := by
  -- Both sides are defined on the full genuine target graph, rather than on a finite spectral core only.
  apply (fullTargetBasis a ha).repr.injective
  apply lp.ext
  apply funext
  intro k
  have h := chebyshev2.Continuum.unboundedDiagonalOperator_graph
    (fullTargetBasis a ha) (jacobi.Bessel.sigma a ha) v k
  have hR := chebyshev2.Continuum.unboundedDiagonalOperator_graph
    (fullTargetBasis a ha) (jacobi.Bessel.sigma a ha)
      ⟨reflectionUnitary (v:Space),targetOperator_reflection_mem a ha v⟩ k
  change (fullTargetBasis a ha).repr (targetOperator a ha v) k=_ at h
  change (fullTargetBasis a ha).repr
    (targetOperator a ha ⟨reflectionUnitary (v:Space),targetOperator_reflection_mem a ha v⟩) k=_ at hR
  rw [hR,target_reflection_coordinates,target_reflection_coordinates,h]
  ring

/-- The actual bounded Green inverse commutes with genuine physical reflection on every full original L2 input.
Use: the spatial Green kernel inherits the original midpoint reflection symmetry once its actual integral representative is identified.
Article: jacobi, Proposition C.2.
Proof: both original coordinate multipliers, sigma_k^(-1) and (-1)^k, commute in every coordinate of the complete actual target Hilbert basis. -/
theorem targetGreen_reflection (a : ℝ) (ha : -1<a) (v : Space) :
    targetGreenOperator a ha (reflectionUnitary v)=reflectionUnitary (targetGreenOperator a ha v) := by
  apply (fullTargetBasis a ha).repr.injective
  apply lp.ext
  apply funext
  intro k
  rw [targetGreen_coordinates,target_reflection_coordinates,target_reflection_coordinates,targetGreen_coordinates]
  ring

end
end jacobi.GelfandLevitan
