import jacobi.GelfandLevitan.OriginalQuasiDerivative

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Its second derivative is obtained from the proved actual finite
quasi-system limit and the already identified original C1 diagonal.
Use: the original transformed ODE cancellation compares the actual real diagonal and potential with their unchanged complex values.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The bounded physical-strip complex inclusion has precisely its original pointwise scalar value.
Use: the original transformed ODE cancellation compares the actual real diagonal and potential with their unchanged complex values.
Article: jacobi, Theorem 2.1.
Proof: evaluate the genuine community postcomposition linear map. -/
theorem stripComplex_apply {p q : ℝ} (f : C(ClosedStrip p q,ℝ)) (t : ClosedStrip p q) :
    stripComplex f t=(f t:ℂ) := rfl

/-- The genuine transformed potential on an original positive physical strip.
Use: transformedSolution_ODE_strip proves that the actual GL u solves the Schrodinger equation with this original q+2*w' potential; the target operator must subsequently realize this same differential expression.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def transformedPotentialStrip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) (hds : d≤(1/2:ℝ)) :
    C(ClosedStrip d (1/2),ℝ) := stripPotential a hd+(2:ℝ) • diagonalSlopeRows ha hd hds

/-- The actual original diagonal restricted to a positive physical strip has its already identified genuine derivative.
Use: transformedSolution_ODE_strip differentiates the true original transformed slope after passing the actual quasi-derivative identity to the limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: transfer the independently proved genuine original diagonal derivative to its identical continuous physical-strip values. -/
theorem transformedDiagonalStrip_hasDerivWithinAt (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d≤(1/2:ℝ)) (t : ClosedStrip d (1/2)) :
    HasDerivWithinAt (stripExtension hds (transformedDiagonalStrip a ha hd))
      (diagonalSlopeRows ha hd hds t) (Icc d (1/2)) (t:ℝ) := by
  apply stripDerivative_congr hds (transformedDiagonalStrip a ha hd)
    (fun x => kernelDiagonal a ha (halfParameterClamp x))
    (fun x => by rw [halfParameterClamp_strip]; rfl)
  exact kernelDiagonal_hasDerivWithinAt ha hd (derivativeStripInclusion hd t) t.property.1

/-- The actual infinite GL transformed solution has its genuine second derivative and satisfies the original Schrodinger equation at arbitrary complex energy throughout every positive physical strip, including the midpoint left derivative.
Use: supplies the unconditional actual differential-equation assertion of Proposition C.2 (b); the original Green identity and the target differential-operator realization use this same constructed u and genuine potential.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual original finite GL quasi-derivatives converge to the independently identified original u_t-2*w*u and satisfy their genuine limiting first-order equation. Add the true derivative of 2*w*u, using the already proved original diagonal and transformed-solution derivatives. The two drift terms and the quadratic diagonal terms cancel, leaving precisely the original q_alpha+2*w'-z coefficient. -/
theorem transformedSolution_ODE_strip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d<(1/2:ℝ)) (z : ℂ) (t : ClosedStrip d (1/2)) :
    HasDerivWithinAt (stripExtension hds.le (transformedSlopeRows ha hd z))
      ((((transformedPotentialStrip a ha hd hds.le t:ℝ):ℂ)-z)*transformedSolutionStrip a ha hd z t)
      (Icc d (1/2)) (t:ℝ) := by
  -- The limiting actual quasi-derivative already has a true derivative; only the independently proved actual diagonal product is added back.
  have hV := (transformedQuasiStrip_limit a ha hd hds z).2 t
  have hW := (transformedDiagonalStrip_hasDerivWithinAt a ha hd hds.le t).ofReal_comp
  have hU := transformedSolutionStrip_hasDerivWithinAt a ha hd hds.le z t
  have h := hV.add ((hW.const_mul (2:ℂ)).mul hU)
  rw [stripExtension_value,stripExtension_value] at h
  have hfun : (fun x => stripExtension hds.le (transformedQuasiStrip a ha hd z) x+
      2*(stripExtension hds.le (transformedDiagonalStrip a ha hd) x:ℂ)*
        stripExtension hds.le (transformedSolutionStrip a ha hd z) x)=
      stripExtension hds.le (transformedSlopeRows ha hd z) := by
    have he : transformedQuasiStrip a ha hd z+ContinuousMap.const _ (2:ℂ)*
        stripComplex (transformedDiagonalStrip a ha hd)*transformedSolutionStrip a ha hd z=
        transformedSlopeRows ha hd z := by
      rw [transformedQuasiStrip]
      abel_nf
    funext x
    exact congrArg (fun F : C(ClosedStrip d (1/2),ℂ) => F (Set.projIcc d (1/2) hds.le x)) he
  change HasDerivWithinAt (fun x => stripExtension hds.le (transformedQuasiStrip a ha hd z) x+
    2*(stripExtension hds.le (transformedDiagonalStrip a ha hd) x:ℂ)*
      stripExtension hds.le (transformedSolutionStrip a ha hd z) x) _ _ _ at h
  rw [hfun] at h
  convert h using 1
  dsimp [transformedPotentialStrip,quasiEquationCoefficient,transformedQuasiStrip,stripPotential]
  simp only [stripComplex_apply,ContinuousMap.coe_mk]
  push_cast
  ring

end
end jacobi.GelfandLevitan
