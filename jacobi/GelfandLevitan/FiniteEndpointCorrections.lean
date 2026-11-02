import jacobi.GelfandLevitan.FiniteEndpointCoefficients
import jacobi.GelfandLevitan.FiniteEndpointPrimitives

/-!
Article: jacobi, Proposition C.2.
The genuine finite transformed solution's original primitive expansion
has the printed selected endpoint correction bounds. Its actual slope
correction has the independently proved derivative bound. These are
the original quantities in the finite Green Wronskian cancellation.
Use: finiteTransformedFunction_eq identifies it with the actual finite GL inverse-row solution at every physical point; its genuine endpoint bounds remove the original finite Green boundary term.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter Asymptotics jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope realSolution realSlope

/-- The original actual finite transformed solution's primitive expansion with a real physical parameter.
Use: finiteTransformedFunction_eq identifies it with the actual finite GL inverse-row solution at every physical point; its genuine endpoint bounds remove the original finite Green boundary term.
Article: jacobi, Proposition C.2.
-/
def finiteTransformedFunction (a : ℝ) (ha : -1<a) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  solution a z t+∑ i : FeatureIndex N,(finiteFeatureCoefficients a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t

/-- The real-parameter finite primitive expansion is the same actual original GL transformed solution on the unchanged physical half interval.
Use: finite Green identities and endpoint estimates for this real-parameter expression concern precisely the already constructed actual finite approximation and its proved original uniform limit.
Article: jacobi, Proposition C.2.
Proof: this is the independently proved actual finite inverse-row feature formula, with no new solution or derivative hypothesis. -/
theorem finiteTransformedFunction_eq (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z : ℂ),
      finiteTransformedFunction a ha N z t=finiteTransformedSolution a ha N t z := by
  filter_upwards [finiteTransformedSolution_feature_formula a ha] with N hN t z
  exact (hN t z).symm

/-- Each genuine finite coefficient has its true complex-included selected endpoint power bound.
Use: finiteTransformedFunction_endpoint_correction and the genuine finite slope correction combine the same original coefficients with their actual reference primitives.
Article: jacobi, Proposition C.2.
Proof: the actual finite coefficient vector has the independently proved true norm bound. The community finite product-space estimate gives the original coordinate bound, and the bounded complex inclusion preserves it. -/
theorem finiteFeatureCoefficient_complex_endpoint_bigO (a : ℝ) (ha : -1<a) (N : ℕ)
    (hu : IsUnit (finiteFeatureSystem a ha N 0)) (i : FeatureIndex N) :
    (fun t => (finiteFeatureCoefficients a ha N t i:ℂ))=O[𝓝[>] 0](fun t : ℝ => t^(gamma a)) :=
  (Complex.ofRealCLM.isBigO_comp (fun t => finiteFeatureCoefficients a ha N t i) (𝓝[>] 0)).trans
    (isBigO_pi.mp (finiteFeatureCoefficients_endpoint_bigO a ha N hu) i)

/-- Each true finite coefficient slope has its complex-included singular endpoint power bound.
Use: the actual finite transformed slope correction gains the printed original triple selected power.
Article: jacobi, Proposition C.2.
Proof: the actual original finite coefficient-slope vector bound gives every original coordinate, and genuine bounded complex inclusion preserves the unchanged singular power. -/
theorem finiteFeatureCoefficientSlope_complex_endpoint_bigO (a : ℝ) (ha : -1<a) (N : ℕ)
    (hu : IsUnit (finiteFeatureSystem a ha N 0)) (i : FeatureIndex N) :
    (fun t => (finiteFeatureCoefficientsSlope a ha N t i:ℂ))=O[𝓝[>] 0](fun t : ℝ => t^(gamma a-1)) :=
  (Complex.ofRealCLM.isBigO_comp (fun t => finiteFeatureCoefficientsSlope a ha N t i) (𝓝[>] 0)).trans
    (isBigO_pi.mp (finiteFeatureCoefficientsSlope_endpoint_bigO a ha N hu) i)

/-- The actual finite transformed solution has the printed higher-order endpoint correction relative to the original selected reference branch.
Use: the genuine finite Green Wronskian's original boundary term vanishes even when the reference slope is singular.
Article: jacobi, Proposition C.2.
Proof: each actual original coefficient is O(t^gamma), and each actual reference product primitive is O(t^(2*gamma+1)). Multiply the original bounds and sum the genuine finite primitive expansion. -/
theorem finiteTransformedFunction_endpoint_correction (a : ℝ) (ha : -1<a) (N : ℕ)
    (hu : IsUnit (finiteFeatureSystem a ha N 0)) (z : ℂ) :
    (fun t => finiteTransformedFunction a ha N z t-solution a z t)=O[𝓝[>] 0](fun t : ℝ => t^(3*gamma a+1)) := by
  -- The estimate concerns the literal original transformation correction in the independently identified actual finite solution.
  have hi (i : FeatureIndex N) :
      (fun t => (finiteFeatureCoefficients a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t)=O[𝓝[>] 0]
        (fun t : ℝ => t^(3*gamma a+1)) := by
    have h := endpointBigO_mul (finiteFeatureCoefficient_complex_endpoint_bigO a ha N hu i)
      (finiteFeaturePrimitive_endpoint_bigO a ha i z)
    simpa only [show gamma a+(2*gamma a+1)=3*gamma a+1 by ring] using h
  have he : (fun t => finiteTransformedFunction a ha N z t-solution a z t)=
      (fun t => ∑ i : FeatureIndex N,(finiteFeatureCoefficients a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t) := by
    funext t
    rw [finiteTransformedFunction]
    ring
  rw [he]
  exact IsBigO.fun_sum (s := Finset.univ) (fun i _ => hi i)

/-- The actual finite transformed solution's genuine slope has the printed higher-order endpoint correction relative to the true original reference slope.
Use: combines with the original finite solution correction and the actual reference Green endpoint cancellation to remove the genuine transformed Wronskian boundary term.
Article: jacobi, Proposition C.2.
Proof: the true differentiated primitive expansion contains a_i' times its original product primitive and a_i*h_i*f. Their independently proved actual endpoint powers are respectively gamma-minus-one plus twice gamma plus one, and three times gamma. The genuine finite sum gives the printed original bound. -/
theorem finiteTransformedSlope_endpoint_correction (a : ℝ) (ha : -1<a) (N : ℕ)
    (hu : IsUnit (finiteFeatureSystem a ha N 0)) (z : ℂ) :
    (fun t => finiteTransformedSlope a ha N z t-solutionSlope a z t)=O[𝓝[>] 0](fun t : ℝ => t^(3*gamma a)) := by
  -- Both terms are genuine derivatives of the original finite primitive expansion, not derivatives inferred from a Landau estimate.
  have hi (i : FeatureIndex N) :
      (fun t => (finiteFeatureCoefficientsSlope a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t+
        (finiteFeatureCoefficients a ha N t i:ℂ)*(realSolution a (finiteFeatureEnergy a ha i) t:ℂ)*solution a z t)=O[𝓝[>] 0]
        (fun t : ℝ => t^(3*gamma a)) := by
    have hFirst := endpointBigO_mul (finiteFeatureCoefficientSlope_complex_endpoint_bigO a ha N hu i)
      (finiteFeaturePrimitive_endpoint_bigO a ha i z)
    have hWave := (Complex.ofRealCLM.isBigO_comp (realSolution a (finiteFeatureEnergy a ha i)) (𝓝[>] 0)).trans
      (realSolution_endpoint_bigO a (finiteFeatureEnergy a ha i))
    have hSecond := endpointBigO_mul (endpointBigO_mul (finiteFeatureCoefficient_complex_endpoint_bigO a ha N hu i) hWave)
      (solution_endpoint_bigO a z)
    simp only [show gamma a-1+(2*gamma a+1)=3*gamma a by ring] at hFirst
    simp only [show gamma a+gamma a+gamma a=3*gamma a by ring] at hSecond
    exact hFirst.add hSecond
  have he : (fun t => finiteTransformedSlope a ha N z t-solutionSlope a z t)=
      (fun t => ∑ i : FeatureIndex N,((finiteFeatureCoefficientsSlope a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t+
        (finiteFeatureCoefficients a ha N t i:ℂ)*(realSolution a (finiteFeatureEnergy a ha i) t:ℂ)*solution a z t)) := by
    funext t
    rw [finiteTransformedSlope]
    ring
  rw [he]
  exact IsBigO.fun_sum (s := Finset.univ) (fun i _ => hi i)

end
end jacobi.GelfandLevitan
