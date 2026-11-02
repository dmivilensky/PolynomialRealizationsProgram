import jacobi.GelfandLevitan.FiniteKernelDarboux

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The finite GL transform uses actual selected-solution product integrals.
Their endpoint derivatives and Green identities retain the singular
reference normalization. They give the finite transformed ODE without
assuming differentiability at the singular endpoint.
Use: finiteFeaturePrimitive has a globally continuous integrand while keeping the actual physical reference solution.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope realSolution realSlope

/-- The original complex selected solution continuously extended from the physical half interval.
Use: finiteFeaturePrimitive has a globally continuous integrand while keeping the actual physical reference solution.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteReferenceWave (a : ℝ) (ha : -1<a) (z : ℂ) : C(ℝ,ℂ) :=
  ((halfSolution a ha z).comp halfInclusion).comp halfParameterClamp

/-- The continuous extension preserves each original physical solution value.
Use: the finite primitive and its derivative are identified with the unchanged reference solution.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the physical half projection fixes the point and the half-coordinate minimum equals the original coordinate. -/
theorem finiteReferenceWave_value {a x : ℝ} (ha : -1<a) (z : ℂ) (hx : x∈Icc (0:ℝ) (1/2)) :
    finiteReferenceWave a ha z x=solution a z x := by
  change halfSolution a ha z (halfInclusion (halfParameterClamp x))=_
  rw [halfSolution_apply,show halfParameterClamp x=(⟨x,hx⟩:HalfInterval) from Set.projIcc_of_mem (by norm_num) hx]
  change solution a z (min x (1/2))=_
  rw [min_eq_left hx.2]

/-- The actual product primitive of one finite reference feature and the original energy solution.
Use: finiteTransformedSolution_feature_formula and the finite transformed ODE use these genuine integrals, including their original zero endpoint.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeaturePrimitive (a : ℝ) (ha : -1<a) {N : ℕ} (i : FeatureIndex N) (z : ℂ) (t : ℝ) : ℂ :=
  ∫ r in (0:ℝ)..t,(finiteFeatureWave a ha i r:ℂ)*finiteReferenceWave a ha z r

/-- The finite feature primitive equals its literal original physical selected-solution product integral.
Use: finiteFeaturePrimitive_green applies the independently proved singular-endpoint Green identity to this same original primitive.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the two continuous extensions equal their original selected solutions throughout the actual integration interval. -/
theorem finiteFeaturePrimitive_integral (a : ℝ) (ha : -1<a) {N : ℕ} (i : FeatureIndex N)
    (z : ℂ) (t : HalfInterval) :
    finiteFeaturePrimitive a ha i z t=∫ r in (0:ℝ)..(t:ℝ),solution a (finiteFeatureEnergy a ha i:ℂ) r*solution a z r := by
  rw [finiteFeaturePrimitive]
  apply intervalIntegral.integral_congr
  intro r hr
  have hp : r∈Icc (0:ℝ) (1/2) := by
    have hr' : r∈Icc (0:ℝ) (t:ℝ) := by simpa only [uIcc_of_le t.property.1] using hr
    exact ⟨hr'.1,hr'.2.trans t.property.2⟩
  dsimp only
  rw [finiteFeatureWave_value ha i hp,finiteReferenceWave_value ha z hp,realSolution_cast]

/-- The genuine feature primitive has its actual physical endpoint derivative, including the midpoint.
Use: the finite transformed solution is differentiated through its true finite primitive expansion.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: mathlib's endpoint fundamental theorem of calculus.
Proof: its continuously extended integrand satisfies the community FTC; its actual endpoint value agrees with the original physical solutions. -/
theorem finiteFeaturePrimitive_hasDerivAt (a : ℝ) (ha : -1<a) {N : ℕ} (i : FeatureIndex N)
    (z : ℂ) (t : HalfInterval) :
    HasDerivAt (finiteFeaturePrimitive a ha i z)
      ((realSolution a (finiteFeatureEnergy a ha i) t:ℂ)*solution a z t) (t:ℝ) := by
  have hc : Continuous (fun r : ℝ => (finiteFeatureWave a ha i r:ℂ)*finiteReferenceWave a ha z r) :=
    (Complex.continuous_ofReal.comp (finiteFeatureWave a ha i).continuous).mul (finiteReferenceWave a ha z).continuous
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (μ := volume) (0:ℝ) t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  rw [finiteFeatureWave_value ha i t.property,finiteReferenceWave_value ha z t.property] at h
  exact h

/-- The actual finite feature primitive satisfies the original Green identity at every positive physical point and arbitrary complex energy.
Use: cancels every mixed reference-feature term in the genuine finite transformed differential equation, without dividing by an energy difference.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: specialize the already proved original reference Green identity and substitute the actual primitive integral and genuine real feature slope. The original singular endpoint cancellation is inherited unchanged. -/
theorem finiteFeaturePrimitive_green (a : ℝ) (ha : -1<a) {N : ℕ} (i : FeatureIndex N)
    (z : ℂ) (t : HalfInterval) (ht : 0<(t:ℝ)) :
    ((finiteFeatureEnergy a ha i:ℂ)-z)*finiteFeaturePrimitive a ha i z t=
      (realSolution a (finiteFeatureEnergy a ha i) t:ℂ)*solutionSlope a z t-
        (realSlope a (finiteFeatureEnergy a ha i) t:ℂ)*solution a z t := by
  have hp : (t:ℝ)∈Ioo (0:ℝ) 1 := ⟨ht,by linarith [t.property.2]⟩
  rw [finiteFeaturePrimitive_integral]
  have h := reference_green_identity ha (finiteFeatureEnergy a ha i:ℂ) z hp
  simpa only [referenceWronskian,realSolution_cast,realSlope,solutionSlope_real a (finiteFeatureEnergy a ha i) hp] using h

end
end jacobi.GelfandLevitan
