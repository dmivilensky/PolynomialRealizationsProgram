import jacobi.GelfandLevitan.FiniteFeaturePrimitives

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual finite inverse-row transformed solution is exactly the
finite expansion in the genuine reference product primitives. This
identifies the function used in the finite differential calculation
with the original GL approximation, whose uniform limit was proved.
Use: finiteTransformedSolution_feature_formula evaluates the actual inverse-row feature synthesis under its original source coefficient functional.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution realSolution coefficientVector

/-- Pairing a genuine restricted finite feature with the reference solution is its actual physical product primitive.
Use: finiteTransformedSolution_feature_formula evaluates the actual inverse-row feature synthesis under its original source coefficient functional.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original restricted feature is its true prefix candidate vector. The genuine bounded prefix pairing equals its actual subtype integral, which the already proved physical-coordinate integral identity identifies with the original primitive. -/
theorem finiteFeatureVector_coefficient (a : ℝ) (ha : -1<a) {N : ℕ}
    (i : FeatureIndex N) (z : ℂ) (t : HalfInterval) :
    coefficientInput (halfSolution a ha z) (finiteFeatureVector a ha t i:Space)=finiteFeaturePrimitive a ha i z t := by
  -- No pointwise evaluation of an arbitrary L2 class is used: the actual physical candidate representative fixes the integral.
  have hv : finiteFeatureVector a ha t i=candidateVector t (realHalfWave a ha (finiteFeatureEnergy a ha i)) := by
    rw [finiteFeatureVector,coefficientVector,fullCoefficientVector]
    rfl
  rw [hv]
  change prefixPairing t (halfSolution a ha z) (realHalfWave a ha (finiteFeatureEnergy a ha i))=_
  rw [prefixPairing_apply,finiteFeaturePrimitive]
  have hp := prefix_integral (fun r : ℝ => (finiteFeatureWave a ha i r:ℂ)*finiteReferenceWave a ha z r)
    (show (t:ℝ)∈Icc (0:ℝ) 1 from ⟨t.property.1,by linarith [t.property.2]⟩)
  rw [← hp]
  apply setIntegral_congr_fun (prefixSet_measurable (t:ℝ))
  intro r _
  change (realSolution a (finiteFeatureEnergy a ha i) (halfTime r):ℂ)*halfSolution a ha z r=
    (realSolution a (finiteFeatureEnergy a ha i) ((halfParameterClamp r):ℝ):ℂ)*
      halfSolution a ha z (halfInclusion (halfParameterClamp r))
  rw [halfParameterClamp_unit,halfClamp_val,halfSolution_apply,halfSolution_apply]
  change _=(realSolution a (finiteFeatureEnergy a ha i) (halfTime r):ℂ)*solution a z (min (halfTime r) (1/2))
  rw [min_eq_left (halfTime_mem r).2]

/-- The actual original finite GL transformed solution is exactly its finite coefficient and genuine product-primitive expansion, with every inverse condition discharged.
Use: its actual spatial derivatives and ODE are proved by differentiating this same original finite expansion.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: substitute the independently proved actual finite inverse-row synthesis. The genuine bounded original coefficient functional preserves the finite sum and real scalar multiplication. Each actual restricted-feature coefficient is its proved original product primitive. -/
theorem finiteTransformedSolution_feature_formula (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z : ℂ),
      finiteTransformedSolution a ha N t z=solution a z t+
        ∑ i : FeatureIndex N,(finiteFeatureCoefficients a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t := by
  -- The original Hilbert row identity is retained under the same original source coefficient map.
  filter_upwards [finiteSolutionRow_feature_representation_eventually a ha] with N hRow t z
  rw [finiteTransformedSolution,hRow t,finiteFeatureSynthesis_apply]
  congr 1
  change coefficientInput (halfSolution a ha z)
    (halfSubspace.subtypeL (∑ i : FeatureIndex N,finiteFeatureCoefficients a ha N t i • finiteFeatureVector a ha t i))=_
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,map_smul]
  change finiteFeatureCoefficients a ha N t i •
    coefficientInput (halfSolution a ha z) (finiteFeatureVector a ha t i:Space)=_
  rw [finiteFeatureVector_coefficient]
  rfl

end
end jacobi.GelfandLevitan
