import jacobi.GelfandLevitan.FiniteQuasiDerivative
import jacobi.Reference.EndpointGrowth

/-!
Article: jacobi, Proposition C.2.
The genuine finite Gram operator is continuous even at the singular
endpoint. Its actual inverse is locally bounded at every proved unit.
These statements prepare the original finite transformed Wronskian
endpoint cancellation, without assuming bounded selected slopes.
Use: finiteFeatureSystemInverse_endpoint_bigO uses the same actual operator norm as the finite GL derivative calculation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter Asymptotics jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope coefficientVector

/-- The genuine finite endomorphism norm structure, cached for the original inverse-continuity inference.
Use: finiteFeatureSystemInverse_endpoint_bigO uses the same actual operator norm as the finite GL derivative calculation.
Article: jacobi, Proposition C.2.
-/
local instance (N : ℕ) : NormedAddCommGroup ((FeatureIndex N→ℝ) →L[ℝ] (FeatureIndex N→ℝ)) := inferInstance

/-- The genuine finite physical Gram entries vary continuously even at the singular endpoint.
Use: finiteFeatureSystem_continuous obtains actual endpoint inverse continuity in the original finite-system norm.
Article: jacobi, Proposition C.2.
Proof: the original prefix projection is strongly continuous on each genuine fixed feature vector. Continuity of the unchanged real Hilbert inner product gives the actual Gram entry. -/
theorem finiteFeatureGram_continuous (a : ℝ) (ha : -1<a) (N : ℕ) (i j : FeatureIndex N) :
    Continuous (fun t : ℝ => finiteFeatureGram a ha N t i j) :=
  (cutoffProjection_strong_continuous (coefficientVector a ha (finiteFeatureEnergy a ha i))).inner
    (cutoffProjection_strong_continuous (coefficientVector a ha (finiteFeatureEnergy a ha j)))

/-- The actual original finite Gram system is continuous in its genuine matrix operator norm at every physical parameter, including zero.
Use: finiteFeatureSystemInverse_endpoint_bigO proves actual local boundedness of the genuine finite inverse at the selected singular endpoint.
Article: jacobi, Proposition C.2.
Proof: the independently identified original finite coordinate-matrix expansion has continuous genuine Gram coefficients. Fixed matrix units and finite operator sums preserve norm continuity. -/
theorem finiteFeatureSystem_continuous (a : ℝ) (ha : -1<a) (N : ℕ) :
    Continuous (finiteFeatureSystem a ha N) := by
  have he : finiteFeatureSystem a ha N=(fun t => ContinuousLinearMap.id ℝ (FeatureIndex N→ℝ)+
      ∑ i : FeatureIndex N,∑ j : FeatureIndex N,
        (finiteFeatureWeight a ha i*finiteFeatureGram a ha N t i j) • featureMatrixUnit i j) :=
    funext (finiteFeatureSystem_operator_formula a ha N)
  rw [he]
  exact continuous_const.add (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
    (continuous_const.mul (finiteFeatureGram_continuous a ha N i j)).smul continuous_const)))

/-- The actual finite-system inverse is bounded near the genuine singular endpoint whenever the independently constructed original finite system is a proved unit there.
Use: finite coefficient endpoint estimates apply this only beyond the original spectral threshold, where all units have already been proved.
Article: jacobi, Proposition C.2.
Source: continuity of inversion at a unit in a real Banach algebra.
Proof: the original finite system is norm-continuous. The community derivative of inversion at its genuine unit gives true inverse continuity, hence local norm boundedness on the original positive zero-endpoint filter. -/
theorem finiteFeatureSystemInverse_endpoint_bigO (a : ℝ) (ha : -1<a) (N : ℕ)
    (hu : IsUnit (finiteFeatureSystem a ha N 0)) :
    (fun t => Ring.inverse (finiteFeatureSystem a ha N t))=O[𝓝[>] 0](fun _ : ℝ => (1:ℝ)) := by
  have hi := (differentiableAt_inverse (𝕜 := ℝ) hu).continuousAt.comp
    (finiteFeatureSystem_continuous a ha N).continuousAt
  exact (hi.tendsto.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)).isBigO_one ℝ

/-- Applying genuine endpoint-bounded operators to endpoint-bounded vectors multiplies their true power scales.
Use: the actual finite inverse coefficient and coefficient-slope endpoint bounds follow from their independently proved original operator formulas.
Article: jacobi, Proposition C.2.
Source: the operator norm inequality and multiplication of Landau bounds.
Proof: actual bounded-operator evaluation is dominated by the product of the actual operator and vector norms. Multiply the genuine power bounds and use the unchanged positive-axis power addition identity. -/
theorem endpointBigO_clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {A : ℝ→E→L[ℝ] F} {v : ℝ→E} {p q : ℝ}
    (hA : A=O[𝓝[>] 0](fun t : ℝ => t^p)) (hv : v=O[𝓝[>] 0](fun t : ℝ => t^q)) :
    (fun t => A t (v t))=O[𝓝[>] 0](fun t : ℝ => t^(p+q)) := by
  have hEval : (fun t => A t (v t))=O[𝓝[>] 0](fun t => ‖A t‖*‖v t‖) :=
    IsBigO.of_bound 1 (Eventually.of_forall (fun t => by simpa only [one_mul,norm_mul,norm_norm] using (A t).le_opNorm (v t)))
  exact hEval.trans (endpointBigO_mul hA.norm_left hv.norm_left)

end
end jacobi.GelfandLevitan
