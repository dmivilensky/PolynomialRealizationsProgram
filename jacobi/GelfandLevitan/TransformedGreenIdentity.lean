import jacobi.GelfandLevitan.FiniteSolutionHalfMap

/-!
Article: jacobi, Proposition C.2.
Use: the actual original finite Wronskians converge in transformedWronskian_tendsto, discharging the boundary side of the full original Green limit.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original finite transformed slopes converge to the independently identified genuine original u derivative at every positive physical point, including the midpoint.
Use: the actual original finite Wronskians converge in transformedWronskian_tendsto, discharging the boundary side of the full original Green limit.
Article: jacobi, Proposition C.2.
Proof: the genuine finite quasi-derivatives converge in the proved original strip uniform norm. Add twice the product of the actual original convergent finite diagonals and solutions. The exact original quasi-derivative identities cancel at every eventual physical point; the limiting same identity is the already identified original transformed slope. -/
theorem finiteTransformedSlope_tendsto_strip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d<(1/2:ℝ)) (z : ℂ) (t : ClosedStrip d (1/2)) :
    Tendsto (fun N => finiteTransformedSlope a ha N z t) atTop (𝓝 (transformedSlopeRows ha hd z t)) := by
  -- The original first-derivative limit is derived from actual solution/diagonal limits and the proved true quasi-derivative limit.
  have hV := ((continuous_eval_const t).tendsto _).comp (transformedQuasiStrip_limit a ha hd hds z).1
  have hW := ((continuous_eval_const t).tendsto _).comp (finiteDiagonalStrip_tendsto a ha hd)
  have hU := ((continuous_eval_const t).tendsto _).comp (finiteSolutionStrip_tendsto a ha hd z)
  have h := hV.add (((Complex.continuous_ofReal.continuousAt.tendsto.comp hW).const_mul (2:ℂ)).mul hU)
  have hvalue : transformedQuasiStrip a ha hd z t+
      2*(transformedDiagonalStrip a ha hd t:ℂ)*transformedSolutionStrip a ha hd z t=transformedSlopeRows ha hd z t := by
    have he : transformedQuasiStrip a ha hd z+ContinuousMap.const _ (2:ℂ)*
        stripComplex (transformedDiagonalStrip a ha hd)*transformedSolutionStrip a ha hd z=
        transformedSlopeRows ha hd z := by
      rw [transformedQuasiStrip]
      abel_nf
    exact congrArg (fun F : C(ClosedStrip d (1/2),ℂ) => F t) he
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [finiteStripData_values a ha hd] with N hN
  change finiteQuasiStrip a ha N d z t+2*(finiteDiagonalStrip a ha N d t:ℂ)*finiteSolutionStrip a ha N d z t=_
  rw [(hN z t).1,(hN z t).2.1,(hN z t).2.2,finiteTransformedQuasiDerivative]
  ring

/-- The actual original finite transformed primitive solutions converge pointwise on the entire physical half interval, including zero.
Use: transformedWronskian_tendsto combines this same original solution limit with the genuine finite slope limit.
Article: jacobi, Proposition C.2.
Proof: evaluate the independently proved actual full-half norm limit and remove the eventual original continuous-map totalization using its genuine source-value identity. -/
theorem finiteTransformedFunction_tendsto (a : ℝ) (ha : -1<a) (z : ℂ) (t : HalfInterval) :
    Tendsto (fun N => finiteTransformedFunction a ha N z t) atTop (𝓝 (transformedSolution a ha t z)) := by
  have h := ((continuous_eval_const t).tendsto _).comp (finiteTransformedHalfMap_tendsto a ha z)
  apply h.congr'
  filter_upwards [finiteTransformedHalfMap_values a ha] with N hN
  exact hN z t

/-- The genuine original finite transformed Wronskians converge to the actual original transformed Wronskian at every positive physical point, including the midpoint.
Use: transformed_green_identity passes the independently proved full finite Green identity to its actual infinite original GL solution with no separately supplied Wronskian or derivative-limit premise.
Article: jacobi, Proposition C.2.
Proof: multiply the independently proved original finite solution and true finite slope limits, then subtract the actual original cross products. -/
theorem transformedWronskian_tendsto (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d<(1/2:ℝ)) (z w : ℂ) (t : ClosedStrip d (1/2)) :
    Tendsto (fun N => finiteTransformedWronskian a ha N z w t) atTop
      (𝓝 (transformedWronskianStrip a ha hd z w t)) := by
  exact ((finiteTransformedFunction_tendsto a ha z (derivativeStripInclusion hd t)).mul
    (finiteTransformedSlope_tendsto_strip a ha hd hds w t)).sub
      ((finiteTransformedSlope_tendsto_strip a ha hd hds z t).mul
        (finiteTransformedFunction_tendsto a ha w (derivativeStripInclusion hd t)))

/-- The actual infinite original GL transformed solutions satisfy the full genuine Green identity from their selected singular endpoint zero, at all complex energies and every positive physical endpoint including the midpoint.
Use: supplies the original app-CD identity used with the two transformed orthonormal bases to determine the genuine midpoint boundary classes and exact characteristic products in general Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: the original actual finite transformed solutions satisfy the independently proved full Green identity, including the genuine selected singular endpoint cancellation. Their original product integrals converge from zero by the actual full-half uniform limit. Their genuine Wronskians converge by the independently proved actual first-derivative limit. Uniqueness of limits gives the exact same original infinite identity. -/
theorem transformed_green_identity (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d<(1/2:ℝ)) (z w : ℂ) (t : ClosedStrip d (1/2)) :
    (z-w)*(∫ r in (0:ℝ)..(t:ℝ),transformedSolution a ha (halfParameterClamp r) z*
      transformedSolution a ha (halfParameterClamp r) w)=transformedWronskianStrip a ha hd z w t := by
  -- Every finite differential, endpoint, integral-limit and first-derivative premise has already been proved for the same original GL approximation sequence.
  have hLeft := (finiteTransformedFunction_integral_tendsto a ha z w (derivativeStripInclusion hd t)).const_mul (z-w)
  have hRight := transformedWronskian_tendsto a ha hd hds z w t
  apply tendsto_nhds_unique hLeft
  apply hRight.congr'
  filter_upwards [finiteTransformed_green_identity a ha] with N hN
  exact (hN (derivativeStripInclusion hd t) z w (hd.trans_le t.property.1)).symm

/-- The original actual midpoint characteristics satisfy the exact genuine Green identity from the selected singular endpoint.
Use: the two original transformed orthonormal bases determine the true odd/even boundary conditions and the exact midpoint characteristic formula of general Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: specialize the full actual original transformed Green identity to the midpoint on the original quarter strip. Its genuine endpoint value and actual left derivative are precisely the independently defined original characteristics a and b. -/
theorem midpoint_green_identity (a : ℝ) (ha : -1<a) (z w : ℂ) :
    (z-w)*(∫ r in (0:ℝ)..(1/2:ℝ),transformedSolution a ha (halfParameterClamp r) z*
      transformedSolution a ha (halfParameterClamp r) w)=
        midpointValue a ha z*midpointSlope a ha w-midpointSlope a ha z*midpointValue a ha w := by
  exact transformed_green_identity a ha (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)<1/2) z w ⟨1/2,by norm_num⟩

end
end jacobi.GelfandLevitan
