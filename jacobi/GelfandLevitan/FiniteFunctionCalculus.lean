import jacobi.GelfandLevitan.FiniteWronskianEndpoint

/-!
Article: jacobi, Proposition C.2.
The original finite real-parameter solution expansion has its genuine
physical first derivative and transformed ODE. It is continuous up to
the selected singular endpoint. These statements supply the actual
FTC hypotheses in the finite Green identity from zero.
Use: finiteTransformedFunction_continuousOn discharges the original finite Green product integrability up to the singular endpoint.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope realSolution realSlope

/-- Every actual reference product primitive is genuinely continuous in its real endpoint.
Use: finiteTransformedFunction_continuousOn discharges the original finite Green product integrability up to the singular endpoint.
Article: jacobi, Proposition C.2.
Proof: its actual continuously extended integrand is globally continuous, so the community continuity theorem for its original interval primitive applies. -/
theorem finiteFeaturePrimitive_continuous (a : ℝ) (ha : -1<a) {N : ℕ} (i : FeatureIndex N) (z : ℂ) :
    Continuous (finiteFeaturePrimitive a ha i z) := by
  have hc := (Complex.continuous_ofReal.comp (finiteFeatureWave a ha i).continuous).mul
    (finiteReferenceWave a ha z).continuous
  exact intervalIntegral.continuous_primitive (hc.intervalIntegrable (μ := volume)) 0

/-- The actual original finite transformed primitive expansion is continuous up to the genuine singular endpoint whenever its original finite systems are proved units.
Use: the finite Green identity integrates the actual original finite product from zero with its true endpoint limits.
Article: jacobi, Proposition C.2.
Proof: the genuine finite matrix inverse is continuous at every original physical unit. Its actual source consists of the unchanged continuous selected reference features. Thus the true original coefficients are continuous on the physical half interval; the actual finite product primitives are continuous there as well. Their exact original finite expansion gives the result. -/
theorem finiteTransformedFunction_continuousOn (a : ℝ) (ha : -1<a) (N : ℕ)
    (hu : ∀ t : ℝ,IsUnit (finiteFeatureSystem a ha N t)) (z : ℂ) :
    ContinuousOn (finiteTransformedFunction a ha N z) (Icc (0:ℝ) (1/2)) := by
  -- The original singular selected solutions are continuous at zero; no boundedness or continuity of their singular slopes is asserted there.
  have hQ : Continuous (fun t => Ring.inverse (finiteFeatureSystem a ha N t)) :=
    continuous_iff_continuousAt.mpr (fun t => (differentiableAt_inverse (𝕜 := ℝ) (hu t)).continuousAt.comp
      (finiteFeatureSystem_continuous a ha N).continuousAt)
  have hB : ContinuousOn (finiteFeatureSource a ha N) (Icc (0:ℝ) (1/2)) := by
    apply continuousOn_pi.mpr
    intro i
    have hWave : ContinuousOn (realSolution a (finiteFeatureEnergy a ha i)) (Icc (0:ℝ) (1/2)) :=
      (finiteFeatureWave a ha i).continuous.continuousOn.congr
        (fun t ht => (finiteFeatureWave_value ha i ht).symm)
    exact continuousOn_const.mul hWave
  have hα : ContinuousOn (finiteFeatureCoefficients a ha N) (Icc (0:ℝ) (1/2)) :=
    (hQ.continuousOn.clm_apply hB).neg
  have hf : ContinuousOn (solution a z) (Icc (0:ℝ) (1/2)) :=
    (finiteReferenceWave a ha z).continuous.continuousOn.congr
      (fun t ht => (finiteReferenceWave_value ha z ht).symm)
  change ContinuousOn (fun t => solution a z t+
    ∑ i : FeatureIndex N,(finiteFeatureCoefficients a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t) _
  apply hf.add
  apply continuousOn_finsetSum
  intro i _
  exact (Complex.continuous_ofReal.comp_continuousOn
    ((ContinuousLinearMap.proj i : (FeatureIndex N→ℝ) →L[ℝ] ℝ).continuous.comp_continuousOn hα)).mul
      (finiteFeaturePrimitive_continuous a ha i z).continuousOn

/-- The genuine original finite real-parameter transformed solution has its independently identified actual physical slope, with every finite inverse condition discharged.
Use: finite Green's identity differentiates this same actual finite primitive solution, including the exact singular endpoint expansion proved separately.
Article: jacobi, Proposition C.2.
Proof: the original finite primitive expansion equals the actual inverse-row transformed solution at every physical point. Its already proved genuine derivative is preserved on the same physical strip by equality of all original values. -/
theorem finiteTransformedFunction_hasDerivWithinAt (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z : ℂ),0<(t:ℝ) →
      HasDerivWithinAt (finiteTransformedFunction a ha N z) (finiteTransformedSlope a ha N z t)
        (Icc ((t:ℝ)/2) (1/2)) (t:ℝ) := by
  -- The original finite solution identification is applied throughout the derivative domain before its true derivative is transferred.
  filter_upwards [finiteTransformedSolution_hasDerivWithinAt a ha,finiteTransformedFunction_eq a ha]
    with N hD hEq t z ht
  apply (hD t z ht).congr
  · intro x hx
    have hp : x∈Icc (0:ℝ) (1/2) := ⟨by linarith [hx.1],hx.2⟩
    rw [show halfParameterClamp x=(⟨x,hp⟩:HalfInterval) from Set.projIcc_of_mem (by norm_num) hp]
    exact hEq ⟨x,hp⟩ z
  · rw [show halfParameterClamp (t:ℝ)=t from Set.projIcc_of_mem (by norm_num) t.property]
    exact hEq t z

/-- The true original finite transformed slope satisfies its actual original ODE in the same real-parameter primitive expansion.
Use: finite Green's Wronskian identity uses the actual finite solution whose selected singular endpoint cancellation is independently proved.
Article: jacobi, Proposition C.2.
Proof: replace the original actual finite inverse-row solution in its independently proved finite transformed ODE by its proved identical original primitive expansion. -/
theorem finiteTransformedFunction_ODE (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z : ℂ),0<(t:ℝ) →
      HasDerivWithinAt (finiteTransformedSlope a ha N z)
        ((((potential a t+2*finiteKernelDiagonalSlope a ha N t:ℝ):ℂ)-z)*finiteTransformedFunction a ha N z t)
        (Icc ((t:ℝ)/2) (1/2)) (t:ℝ) := by
  filter_upwards [finiteTransformedSolution_ODE a ha,finiteTransformedFunction_eq a ha]
    with N hD hEq t z ht
  rw [hEq t z]
  exact hD t z ht

end
end jacobi.GelfandLevitan
