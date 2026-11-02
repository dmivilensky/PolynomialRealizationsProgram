import jacobi.GelfandLevitan.TransformedSecondSmoothness

/-!
Article: jacobi, Proposition C.2.
Use: transformedWronskianStrip_hasDerivWithinAt gives the actual Green differential identity, and transformedGreen_strip integrates it on the unchanged positive physical interval.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine Wronskian of the actual original transformed solutions and their independently identified physical derivatives.
Use: transformedWronskianStrip_hasDerivWithinAt gives the actual Green differential identity, and transformedGreen_strip integrates it on the unchanged positive physical interval.
Article: jacobi, Proposition C.2.
-/
def transformedWronskianStrip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) (z w : ℂ) :
    C(ClosedStrip d (1/2),ℂ) :=
  transformedSolutionStrip a ha hd z*transformedSlopeRows ha hd w-
    transformedSlopeRows ha hd z*transformedSolutionStrip a ha hd w

/-- The actual transformed Wronskian has its genuine original Green derivative at arbitrary complex energies throughout each positive physical strip.
Use: transformedGreen_strip integrates this actual original identity before the separate singular-endpoint cancellation needed for the full app-CD statement.
Article: jacobi, Proposition C.2.
Source: Lagrange's identity for the Schrodinger equation.
Proof: differentiate the actual original product difference using the independently proved true transformed solution derivatives and original transformed ODE. The shared actual potential and the slope-product terms cancel. -/
theorem transformedWronskianStrip_hasDerivWithinAt (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d<(1/2:ℝ)) (z w : ℂ) (t : ClosedStrip d (1/2)) :
    HasDerivWithinAt (stripExtension hds.le (transformedWronskianStrip a ha hd z w))
      ((z-w)*transformedSolutionStrip a ha hd z t*transformedSolutionStrip a ha hd w t)
      (Icc d (1/2)) (t:ℝ) := by
  -- Both energies use the same actual original transformed potential, so its contribution cancels exactly.
  have hUz := transformedSolutionStrip_hasDerivWithinAt a ha hd hds.le z t
  have hUw := transformedSolutionStrip_hasDerivWithinAt a ha hd hds.le w t
  have hSz := transformedSolution_ODE_strip a ha hd hds z t
  have hSw := transformedSolution_ODE_strip a ha hd hds w t
  have h := (hUz.mul hSw).sub (hSz.mul hUw)
  simp only [stripExtension_value] at h
  change HasDerivWithinAt (stripExtension hds.le (transformedWronskianStrip a ha hd z w)) _ _ _ at h
  convert h using 1
  ring

/-- The actual original transformed solutions satisfy Green's identity between the original positive strip endpoints at every pair of complex energies.
Use: the full original app-CD identity from zero requires the separate true transformed Wronskian endpoint cancellation; this theorem supplies its already proved nonsingular integral identity.
Article: jacobi, Proposition C.2.
Source: the integrated Lagrange identity.
Proof: the actual transformed Wronskian has the genuine continuous original product derivative. Apply the already proved physical-strip FTC, evaluate the exact primitive and factor out the fixed energy difference. The integration coordinate and measure remain the original physical ones. -/
theorem transformedGreen_strip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d<(1/2:ℝ)) (z w : ℂ) (t : ClosedStrip d (1/2)) :
    (z-w)*(∫ r in d..(t:ℝ),stripExtension hds.le (transformedSolutionStrip a ha hd z) r*
      stripExtension hds.le (transformedSolutionStrip a ha hd w) r)=
        transformedWronskianStrip a ha hd z w t-
          transformedWronskianStrip a ha hd z w ⟨d,⟨le_rfl,hds.le⟩⟩ := by
  -- The lower endpoint remains the actual positive d; a zero-endpoint boundary condition is not inserted into this identity.
  have h := stripPrimitive_eq_sub hds (transformedWronskianStrip a ha hd z w)
    (ContinuousMap.const _ (z-w)*transformedSolutionStrip a ha hd z*transformedSolutionStrip a ha hd w)
    (transformedWronskianStrip_hasDerivWithinAt a ha hd hds z w)
  have ht := congrArg (fun F : C(ClosedStrip d (1/2),ℂ) => F t) h
  change (∫ r in d..(t:ℝ),(z-w)*stripExtension hds.le (transformedSolutionStrip a ha hd z) r*
    stripExtension hds.le (transformedSolutionStrip a ha hd w) r)=_ at ht
  simpa only [mul_assoc,intervalIntegral.integral_const_mul,ContinuousMap.sub_apply,ContinuousMap.const_apply] using ht

end
end jacobi.GelfandLevitan
