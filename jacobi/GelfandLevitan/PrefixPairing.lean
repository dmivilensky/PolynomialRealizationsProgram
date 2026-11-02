import jacobi.GelfandLevitan.TransformationRowsDerivative
import jacobi.GelfandLevitan.SpatialSolution

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The original fixed-prefix integral against a complex reference solution
is a genuine bounded real-linear functional of the continuous real K
row. This supplies its derivative directly from the actual uniform-row
derivative, retaining the original physical Lebesgue measure.
Use: differentiates the original K integral by composing this genuine functional with the actual uniform-row derivative.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformationKernel

/-- The actual original physical-prefix integral against a fixed continuous complex input, as a bounded functional of continuous real rows.
Use: differentiates the original K integral by composing this genuine functional with the actual uniform-row derivative.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the community L2 embedding and physical orthogonal projections, with the already proved actual coefficient integral functional. -/
def prefixPairing (t : HalfInterval) (w : C(Interval,ℂ)) : C(Interval,ℝ) →L[ℝ] ℂ :=
  coefficientInput w ∘L halfSubspace.subtypeL ∘L cutoffProjection (t:ℝ) ∘L
    halfSubspace.orthogonalProjectionOnto ∘L ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume

/-- The bounded actual prefix functional is exactly its genuine original spatial integral.
Use: identifies its true derivative with the actual integral in the printed transformed-solution derivative formula.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: its actual projected L2 vector is candidateVector, whose genuine representative is the original physical indicator times the original row. Substitute this representative in its true coefficient integral. -/
theorem prefixPairing_apply (t : HalfInterval) (w : C(Interval,ℂ)) (g : C(Interval,ℝ)) :
    prefixPairing t w g=∫ r : Interval in prefixSet (t:ℝ),(g r:ℂ)*w r := by
  change (∫ r : Interval,((candidateVector t g:Space) r:ℂ)*w r)=_
  rw [← integral_indicator (prefixSet_measurable (t:ℝ))]
  apply integral_congr_ae
  filter_upwards [candidateVector_ae t g] with r hr
  rw [hr]
  by_cases hp : r∈prefixSet (t:ℝ)
  · rw [indicator_of_mem hp,indicator_of_mem hp]
  · rw [indicator_of_notMem hp,indicator_of_notMem hp,Complex.ofReal_zero,zero_mul]

/-- The paired actual fixed-prefix K row has exactly the literal original K integral, independently of its varying first parameter.
Use: the transformed-solution quotient splits into the derivative of this same original prefix integral and its actual moving tail.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the fixed spatial clipping fixes every genuine physical integration point. The original continuous row therefore has exactly its original K values throughout the integration interval. -/
theorem prefixPairing_fixedTransformationRows (a : ℝ) (ha : -1<a) (t : HalfInterval)
    (w : C(Interval,ℂ)) (x : ℝ) :
    prefixPairing t w (fixedTransformationRows a ha t x)=
      ∫ r : Interval in prefixSet (t:ℝ),(transformationKernel a ha (halfParameterClamp x) (halfClamp r):ℂ)*w r := by
  rw [prefixPairing_apply]
  apply setIntegral_congr_fun (prefixSet_measurable (t:ℝ))
  intro r hr
  change (transformationKernel a ha (halfParameterClamp x) (halfClamp (prefixClamp t r)):ℂ)*w r=_
  rw [prefixClamp_fix t r hr]

/-- The actual fixed-prefix derivative row pairs to the original partial_t K integral at the unchanged original endpoint.
Use: gives the literal integral term of the actual transformed-solution derivative, with its genuine derivative-forcing solution already identified as partial_t K.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: both physical clippings fix their original prefix values and the actual positive parameter. Evaluate the genuine original derivative row in the unchanged original integral. -/
theorem prefixPairing_fixedTransformationSlopeRows {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (t : HalfInterval) (hdt : d≤(t:ℝ)) (w : C(Interval,ℂ)) :
    prefixPairing t w (fixedTransformationSlopeRows ha hd (hdt.trans t.property.2) t (t:ℝ))=
      ∫ r : Interval in prefixSet (t:ℝ),
        (derivativeCandidateRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩ r:ℂ)*w r := by
  rw [prefixPairing_apply]
  apply setIntegral_congr_fun (prefixSet_measurable (t:ℝ))
  intro r hr
  change (derivativeCandidateRows ha hd
    (positiveStripClamp (hdt.trans t.property.2) (halfParameterClamp (t:ℝ))) (prefixClamp t r):ℂ)*w r=_
  rw [show halfParameterClamp (t:ℝ)=t from Set.projIcc_of_mem (by norm_num) t.property,
    positiveStripClamp_of_mem (hdt.trans t.property.2) t hdt,prefixClamp_fix t r hr]

end
end jacobi.GelfandLevitan
