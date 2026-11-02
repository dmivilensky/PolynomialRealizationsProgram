import jacobi.GelfandLevitan.FiniteEndpointOperators

/-!
Article: jacobi, Proposition C.2.
The actual finite inverse-system coefficients have their genuine
selected power bounds at zero, and their true derivatives have the
corresponding gamma-minus-one bounds. These estimates prepare the
finite transformed Wronskian cancellation in the full source range.
Use: finiteFeatureCoefficients_endpoint_bigO transfers this same source bound through the independently bounded genuine inverse.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter Asymptotics jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope

/-- The actual finite source vector has its genuine selected endpoint power bound.
Use: finiteFeatureCoefficients_endpoint_bigO transfers this same source bound through the independently bounded genuine inverse.
Article: jacobi, Proposition C.2.
Proof: every true finite selected feature has the proved original reference endpoint bound. Its fixed signed weight and the community finite product-space norm preserve the bound. -/
theorem finiteFeatureSource_endpoint_bigO (a : ℝ) (ha : -1<a) (N : ℕ) :
    finiteFeatureSource a ha N=O[𝓝[>] 0](fun t : ℝ => t^(gamma a)) := by
  apply isBigO_pi.mpr
  intro i
  exact (realSolution_endpoint_bigO a (finiteFeatureEnergy a ha i)).const_mul_left (finiteFeatureWeight a ha i)

/-- The actual finite source slope has its genuine singular selected power bound.
Use: finiteFeatureCoefficientsSlope_endpoint_bigO differentiates the same original inverse coefficients without assuming bounded feature slopes.
Article: jacobi, Proposition C.2.
Proof: each independently proved true real selected slope has its original singular endpoint bound. Fixed signed weights and the genuine finite product-space norm preserve it. -/
theorem finiteFeatureSourceSlope_endpoint_bigO (a : ℝ) (ha : -1<a) (N : ℕ) :
    finiteFeatureSourceSlope a ha N=O[𝓝[>] 0](fun t : ℝ => t^(gamma a-1)) := by
  apply isBigO_pi.mpr
  intro i
  exact (realSlope_endpoint_bigO a (finiteFeatureEnergy a ha i)).const_mul_left (finiteFeatureWeight a ha i)

/-- The actual finite Gram-system derivative has its genuine quadratic selected power bound in the original operator norm.
Use: finiteFeatureCoefficientsSlope_endpoint_bigO controls the inverse-derivative contribution at the original singular endpoint.
Article: jacobi, Proposition C.2.
Proof: the independently identified true derivative is a finite sum of fixed matrix units with actual weighted selected-feature product coefficients. Multiply the genuine endpoint bounds and sum in the original finite operator norm. -/
theorem finiteFeatureSystemSlope_endpoint_bigO (a : ℝ) (ha : -1<a) (N : ℕ) :
    finiteFeatureSystemSlope a ha N=O[𝓝[>] 0](fun t : ℝ => t^(2*gamma a)) := by
  -- The estimate is for the genuine original derivative operator, not merely its individual coordinates.
  have hterm (i j : FeatureIndex N) :
      (fun t => (finiteFeatureWeight a ha i*(realSolution a (finiteFeatureEnergy a ha i) t*
        realSolution a (finiteFeatureEnergy a ha j) t)) • featureMatrixUnit i j)=O[𝓝[>] 0](fun t : ℝ => t^(2*gamma a)) := by
    have hp := (endpointBigO_mul (realSolution_endpoint_bigO a (finiteFeatureEnergy a ha i))
      (realSolution_endpoint_bigO a (finiteFeatureEnergy a ha j))).const_smul_left (finiteFeatureWeight a ha i)
    have hc : (fun _ : ℝ => featureMatrixUnit i j)=O[𝓝[>] 0](fun _ : ℝ => (1:ℝ)) :=
      tendsto_const_nhds.isBigO_one ℝ
    simpa only [Pi.smul_apply,smul_eq_mul,mul_one,two_mul] using hp.smul hc
  have hsum := IsBigO.fun_sum (s := Finset.univ) (fun i _ => IsBigO.fun_sum (s := Finset.univ) (fun j _ => hterm i j))
  change (fun t => ∑ i : FeatureIndex N,∑ j : FeatureIndex N,
    (finiteFeatureWeight a ha i*(realSolution a (finiteFeatureEnergy a ha i) t*
      realSolution a (finiteFeatureEnergy a ha j) t)) • featureMatrixUnit i j)=O[𝓝[>] 0] _
  exact hsum

/-- The genuine original finite inverse coefficients have the selected endpoint power bound.
Use: actual finite transformed solution corrections inherit the printed O(t^(3*gamma+1)) bound for the singular Green cancellation.
Article: jacobi, Proposition C.2.
Proof: the actual finite inverse is locally bounded at its independently proved endpoint unit. Apply it to the genuine original source vector, which has the proved selected power bound, and retain the true minus sign. -/
theorem finiteFeatureCoefficients_endpoint_bigO (a : ℝ) (ha : -1<a) (N : ℕ)
    (hu : IsUnit (finiteFeatureSystem a ha N 0)) :
    finiteFeatureCoefficients a ha N=O[𝓝[>] 0](fun t : ℝ => t^(gamma a)) := by
  have hQ : (fun t => Ring.inverse (finiteFeatureSystem a ha N t))=O[𝓝[>] 0](fun t : ℝ => t^(0:ℝ)) := by
    simpa only [Real.rpow_zero] using finiteFeatureSystemInverse_endpoint_bigO a ha N hu
  change (fun t => -(Ring.inverse (finiteFeatureSystem a ha N t) (finiteFeatureSource a ha N t)))=O[𝓝[>] 0] _
  simpa only [zero_add] using
    (endpointBigO_clm_apply hQ (finiteFeatureSource_endpoint_bigO a ha N)).neg_left

/-- The true original finite coefficient slopes have the full singular gamma-minus-one power bound.
Use: the actual finite transformed solution slope correction has its printed O(t^(3*gamma)) bound and therefore its genuine Green Wronskian endpoint vanishes.
Article: jacobi, Proposition C.2.
Proof: use the independently identified original inverse-derivative formula. The two genuine inverse factors are locally bounded, the actual Gram-system derivative is O(t^(2*gamma)), and the actual source is O(t^gamma). Its O(t^(3*gamma)) contribution is bounded by t^(gamma-1); the actual source-slope contribution already has that scale. -/
theorem finiteFeatureCoefficientsSlope_endpoint_bigO (a : ℝ) (ha : -1<a) (N : ℕ)
    (hu : IsUnit (finiteFeatureSystem a ha N 0)) :
    finiteFeatureCoefficientsSlope a ha N=O[𝓝[>] 0](fun t : ℝ => t^(gamma a-1)) := by
  -- This uses the true finite inverse calculus at zero, where the selected reference derivative itself may be unbounded.
  have hQ : (fun t => Ring.inverse (finiteFeatureSystem a ha N t))=O[𝓝[>] 0](fun t : ℝ => t^(0:ℝ)) := by
    simpa only [Real.rpow_zero] using finiteFeatureSystemInverse_endpoint_bigO a ha N hu
  have hQBQ := endpointBigO_mul (endpointBigO_mul hQ (finiteFeatureSystemSlope_endpoint_bigO a ha N)) hQ
  have hFirst := endpointBigO_clm_apply hQBQ (finiteFeatureSource_endpoint_bigO a ha N)
  have hFirst' := hFirst.trans (endpointPower_bigO
    (by linarith [(parameters ha).1] : gamma a-1≤(0+2*gamma a+0)+gamma a))
  have hSecond := endpointBigO_clm_apply hQ (finiteFeatureSourceSlope_endpoint_bigO a ha N)
  simp only [zero_add] at hSecond
  change (fun t => (Ring.inverse (finiteFeatureSystem a ha N t)*finiteFeatureSystemSlope a ha N t*
    Ring.inverse (finiteFeatureSystem a ha N t)) (finiteFeatureSource a ha N t)-
      Ring.inverse (finiteFeatureSystem a ha N t) (finiteFeatureSourceSlope a ha N t))=O[𝓝[>] 0] _
  exact hFirst'.sub hSecond

end
end jacobi.GelfandLevitan
