import jacobi.GelfandLevitan.FiniteEndpointCorrections

/-!
Article: jacobi, Proposition C.2.
The actual finite transformed Wronskian tends to zero at the original
selected singular endpoint. The original reference Green cancellation
and the genuine finite solution/slope correction bounds prove this in
the full gamma greater than one quarter range.
Use: the original finite transformed Wronskian correction is O(t^(4*gamma)), whose actual exponent is positive over the full article range.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter Asymptotics jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope

/-- A genuine positive endpoint power bound forces the actual function to tend to zero.
Use: the original finite transformed Wronskian correction is O(t^(4*gamma)), whose actual exponent is positive over the full article range.
Article: jacobi, Proposition C.2.
Source: the norm squeeze theorem and continuity of positive real powers at zero.
Proof: the actual Landau bound dominates the original norm by a fixed constant times the true positive power, which tends to zero on the original positive-axis endpoint filter. -/
theorem endpointBigO_tendsto_zero {E : Type*} [NormedAddCommGroup E] {f : ℝ→E} {p : ℝ}
    (hp : 0<p) (hf : f=O[𝓝[>] 0](fun t : ℝ => t^p)) :
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,_,hC⟩ := hf.exists_pos
  have hP : Tendsto (fun t : ℝ => t^p) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    simpa only [Real.zero_rpow hp.ne'] using
      (Real.continuous_rpow_const hp.le).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  apply squeeze_zero_norm' hC.bound
  simpa only [norm_zero,mul_zero] using hP.norm.const_mul C

/-- The genuine original finite transformed Wronskian built from the actual finite solution and independently identified true slope.
Use: its proved selected-endpoint limit removes the actual finite Green boundary term; the original finite feature formula identifies this same solution with the finite GL inverse-row construction.
Article: jacobi, Proposition C.2.
-/
def finiteTransformedWronskian (a : ℝ) (ha : -1<a) (N : ℕ) (z w : ℂ) (t : ℝ) : ℂ :=
  finiteTransformedFunction a ha N z t*finiteTransformedSlope a ha N w t-
    finiteTransformedSlope a ha N z t*finiteTransformedFunction a ha N w t

/-- The actual finite transformed Wronskian differs from the genuine original reference Wronskian by a strictly vanishing selected power.
Use: finiteTransformedWronskian_zero combines this true correction estimate with the independently proved reference selected-endpoint cancellation.
Article: jacobi, Proposition C.2.
Proof: expand the original finite Wronskian through the independently proved actual solution and slope corrections. Its four mixed reference/correction terms have exact exponent four gamma; the two correction products have the higher exponent six gamma plus one. The true gamma range permits the unchanged positive-axis comparison and finite addition. -/
theorem finiteTransformedWronskian_endpoint_correction (a : ℝ) (ha : -1<a) (N : ℕ)
    (hu : IsUnit (finiteFeatureSystem a ha N 0)) (z w : ℂ) :
    (fun t => finiteTransformedWronskian a ha N z w t-referenceWronskian a z w t)=O[𝓝[>] 0]
      (fun t : ℝ => t^(4*gamma a)) := by
  -- The potentially singular reference slope is multiplied by the independently proved extra primitive power in the actual finite solution correction.
  let dz := fun t => finiteTransformedFunction a ha N z t-solution a z t
  let dw := fun t => finiteTransformedFunction a ha N w t-solution a w t
  let ez := fun t => finiteTransformedSlope a ha N z t-solutionSlope a z t
  let ew := fun t => finiteTransformedSlope a ha N w t-solutionSlope a w t
  have hdz := finiteTransformedFunction_endpoint_correction a ha N hu z
  have hdw := finiteTransformedFunction_endpoint_correction a ha N hu w
  have hez := finiteTransformedSlope_endpoint_correction a ha N hu z
  have hew := finiteTransformedSlope_endpoint_correction a ha N hu w
  have h1 : (fun t => dz t*solutionSlope a w t)=O[𝓝[>] 0](fun t : ℝ => t^(4*gamma a)) := by
    simpa only [show (3*gamma a+1)+(gamma a-1)=4*gamma a by ring] using
      endpointBigO_mul hdz (solutionSlope_endpoint_bigO a w)
  have h2 : (fun t => solutionSlope a z t*dw t)=O[𝓝[>] 0](fun t : ℝ => t^(4*gamma a)) := by
    simpa only [show (gamma a-1)+(3*gamma a+1)=4*gamma a by ring] using
      endpointBigO_mul (solutionSlope_endpoint_bigO a z) hdw
  have h3 : (fun t => solution a z t*ew t)=O[𝓝[>] 0](fun t : ℝ => t^(4*gamma a)) := by
    simpa only [show gamma a+3*gamma a=4*gamma a by ring] using
      endpointBigO_mul (solution_endpoint_bigO a z) hew
  have h4 : (fun t => ez t*solution a w t)=O[𝓝[>] 0](fun t : ℝ => t^(4*gamma a)) := by
    simpa only [show 3*gamma a+gamma a=4*gamma a by ring] using
      endpointBigO_mul hez (solution_endpoint_bigO a w)
  have h5 : (fun t => dz t*ew t)=O[𝓝[>] 0](fun t : ℝ => t^(4*gamma a)) :=
    (endpointBigO_mul hdz hew).trans (endpointPower_bigO
      (by linarith [(parameters ha).1] : 4*gamma a≤(3*gamma a+1)+3*gamma a))
  have h6 : (fun t => ez t*dw t)=O[𝓝[>] 0](fun t : ℝ => t^(4*gamma a)) :=
    (endpointBigO_mul hez hdw).trans (endpointPower_bigO
      (by linarith [(parameters ha).1] : 4*gamma a≤3*gamma a+(3*gamma a+1)))
  apply (((h1.sub h2).add (h3.sub h4)).add (h5.sub h6)).congr' ?_ EventuallyEq.rfl
  apply Eventually.of_forall
  intro t
  dsimp only [dz,dw,ez,ew]
  rw [finiteTransformedWronskian,referenceWronskian]
  ring

/-- The true original finite transformed Wronskian vanishes at the selected singular endpoint.
Use: removes the actual finite Green boundary term without imposing a transformed endpoint condition or assuming bounded reference slopes.
Article: jacobi, Proposition C.2.
Proof: the independently proved original reference Wronskian tends to zero. Its actual finite transformed correction is O(t^(4*gamma)), with strictly positive genuine exponent, and therefore tends to zero by the norm squeeze theorem. -/
theorem finiteTransformedWronskian_zero (a : ℝ) (ha : -1<a) (N : ℕ)
    (hu : IsUnit (finiteFeatureSystem a ha N 0)) (z w : ℂ) :
    Tendsto (finiteTransformedWronskian a ha N z w) (𝓝[>] 0) (𝓝 0) := by
  have hc := endpointBigO_tendsto_zero (by linarith [(parameters ha).1] : 0<4*gamma a)
    (finiteTransformedWronskian_endpoint_correction a ha N hu z w)
  have h := (referenceWronskian_zero ha z w).add hc
  simpa only [add_sub_cancel,add_zero] using h

end
end jacobi.GelfandLevitan
