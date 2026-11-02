import jacobi.GelfandLevitan.FiniteFunctionCalculus

/-!
Article: jacobi, Proposition C.2.
Use: finiteTransformed_green_identity integrates the true finite transformed ODE with the independently proved singular endpoint cancellation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine original finite transformed Wronskian has its actual Green derivative at every positive physical point beyond the proved original spectral threshold.
Use: finiteTransformed_green_identity integrates the true finite transformed ODE with the independently proved singular endpoint cancellation.
Article: jacobi, Proposition C.2.
Source: the actual Lagrange identity for the Schrodinger equation.
Proof: differentiate the original finite solution/slope product difference using their independently proved actual derivatives. The true shared finite transformed potential and slope-product terms cancel exactly. -/
theorem finiteTransformedWronskian_hasDerivWithinAt (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z w : ℂ),0<(t:ℝ) →
      HasDerivWithinAt (finiteTransformedWronskian a ha N z w)
        ((z-w)*finiteTransformedFunction a ha N z t*finiteTransformedFunction a ha N w t)
        (Icc ((t:ℝ)/2) (1/2)) (t:ℝ) := by
  -- The original finite selected solution, true slope and original finite potential are identical in both energy equations.
  filter_upwards [finiteTransformedFunction_hasDerivWithinAt a ha,finiteTransformedFunction_ODE a ha]
    with N hU hS t z w ht
  have h := ((hU t z ht).mul (hS t w ht)).sub ((hS t z ht).mul (hU t w ht))
  change HasDerivWithinAt (finiteTransformedWronskian a ha N z w) _ _ _ at h
  convert h using 1
  ring

/-- The actual original finite transformed solutions satisfy their full genuine Green identity from zero to every positive physical endpoint, including the midpoint, with all finite inverse and endpoint assumptions discharged.
Use: the actual infinite original Green identity passes this same original finite identity to its independently proved genuine solution and first-derivative limits.
Article: jacobi, Proposition C.2.
Proof: the original true Wronskian derivative follows from the independently proved actual finite transformed ODE. The genuine finite transformed Wronskian tends to zero at its selected singular endpoint by the proved original higher-order correction bounds. The continuous actual finite solution product is integrable up to zero, and the genuine Wronskian has its original one-sided endpoint limit. The community singular-endpoint FTC gives exactly the printed original identity. -/
theorem finiteTransformed_green_identity (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z w : ℂ),0<(t:ℝ) →
      (z-w)*(∫ r in (0:ℝ)..(t:ℝ),finiteTransformedFunction a ha N z r*finiteTransformedFunction a ha N w r)=
        finiteTransformedWronskian a ha N z w t := by
  -- Both original endpoint hypotheses are proved for the actual finite solution; no transformed boundary condition is inserted.
  filter_upwards [finiteFeatureSystem_isUnit a ha,finiteTransformedWronskian_hasDerivWithinAt a ha]
    with N hUnits hD t z w ht
  have hContinuous : ContinuousOn (fun r => (z-w)*finiteTransformedFunction a ha N z r*
      finiteTransformedFunction a ha N w r) (Icc (0:ℝ) (t:ℝ)) :=
    ((continuousOn_const.mul (finiteTransformedFunction_continuousOn a ha N hUnits z)).mul
      (finiteTransformedFunction_continuousOn a ha N hUnits w)).mono (Icc_subset_Icc le_rfl t.property.2)
  have hUpper : Tendsto (finiteTransformedWronskian a ha N z w) (𝓝[<] (t:ℝ))
      (𝓝 (finiteTransformedWronskian a ha N z w t)) := by
    apply ((hD t z w ht).continuousWithinAt.mono_of_mem_nhdsWithin ?_).tendsto
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : (t:ℝ)/2<(t:ℝ))),self_mem_nhdsWithin]
      with r hr hrt
    exact ⟨hr.le,hrt.le.trans t.property.2⟩
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht
    (fun r hr => (hD ⟨r,⟨hr.1.le,hr.2.le.trans t.property.2⟩⟩ z w hr.1).hasDerivAt
      (Icc_mem_nhds (by linarith [hr.1]) (hr.2.trans_le t.property.2)))
    (hContinuous.intervalIntegrable_of_Icc ht.le)
    (finiteTransformedWronskian_zero a ha N (hUnits 0) z w) hUpper
  simpa only [mul_assoc,intervalIntegral.integral_const_mul,sub_zero] using h

end
end jacobi.GelfandLevitan
