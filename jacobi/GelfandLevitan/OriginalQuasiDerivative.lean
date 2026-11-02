import jacobi.GelfandLevitan.OriginalStripLimits

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual original GL quasi-derivative is the true uniform-norm limit
of the actual finite quasi-derivatives. Its genuine derivative follows
from the independently proved closed-system limit. The original
already identified u derivative fixes this limit by uniqueness.
Use: uniqueness of this same physical derivative identifies the quasi-system limit with the actual original quasi-derivative, rather than a new unrelated solution.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual positive-strip original transformed solution has its independently proved genuine original slope.
Use: uniqueness of this same physical derivative identifies the quasi-system limit with the actual original quasi-derivative, rather than a new unrelated solution.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: restrict the independently proved original transformed-solution derivative to the continuous strip function, whose physical values agree by the genuine original clamp identity. -/
theorem transformedSolutionStrip_hasDerivWithinAt (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d≤(1/2:ℝ)) (z : ℂ) (t : ClosedStrip d (1/2)) :
    HasDerivWithinAt (stripExtension hds (transformedSolutionStrip a ha hd z))
      (transformedSlopeRows ha hd z t) (Icc d (1/2)) (t:ℝ) := by
  apply stripDerivative_congr hds (transformedSolutionStrip a ha hd z)
    (fun x => transformedSolution a ha (halfParameterClamp x) z)
    (fun x => by rw [halfParameterClamp_strip]; rfl)
  exact transformedSolution_hasDerivWithinAt ha hd z (derivativeStripInclusion hd t) t.property.1

/-- The actual original finite quasi-derivatives converge uniformly on each positive physical strip to the genuine original quasi-derivative, which satisfies the actual limiting first-order equation.
Use: transformedSolution_ODE_strip differentiates the same original transformed slope, completing the genuine infinite GL differential-equation passage without a first-derivative convergence assumption.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual original finite strip system and the already proved original uniform diagonal and solution limits discharge every hypothesis of quasiSystem_limit. The independently proved genuine original u derivative identifies its limiting first-order component by derivative uniqueness on the nondegenerate physical strip. Therefore the limiting second component is exactly the actual original u_t-2*w*u, with its genuine derivative. -/
theorem transformedQuasiStrip_limit (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d<(1/2:ℝ)) (z : ℂ) :
    Tendsto (fun N => finiteQuasiStrip a ha N d z) atTop (𝓝 (transformedQuasiStrip a ha hd z)) ∧
      ∀ t : ClosedStrip d (1/2),
        HasDerivWithinAt (stripExtension hds.le (transformedQuasiStrip a ha hd z))
          (quasiEquationCoefficient a hd z (transformedDiagonalStrip a ha hd) t*transformedSolutionStrip a ha hd z t-
            2*(transformedDiagonalStrip a ha hd t:ℂ)*transformedQuasiStrip a ha hd z t)
          (Icc d (1/2)) (t:ℝ) := by
  -- The generic theorem's derivative-limit conclusion is instantiated only with the original finite GL functions and their proved actual first-order equations.
  have hW := finiteDiagonalStrip_tendsto a ha hd
  obtain ⟨v,hv,hF,hV⟩ := quasiSystem_limit hds hW (quasiEquationCoefficient_tendsto a hd z hW)
    (finiteSolutionStrip_tendsto a ha hd z) ((finiteStripSystem a ha hd hds).mono (fun _ h => h z))
  have he : v=transformedQuasiStrip a ha hd z := by
    ext t
    have hu : UniqueDiffWithinAt ℝ (Icc d (1/2)) (t:ℝ) := (uniqueDiffOn_Icc hds) t t.property
    have hc := ((hF t).derivWithin hu).symm.trans
      ((transformedSolutionStrip_hasDerivWithinAt a ha hd hds.le z t).derivWithin hu)
    change v t=transformedSlopeRows ha hd z t-
      2*(transformedDiagonalStrip a ha hd t:ℂ)*transformedSolutionStrip a ha hd z t
    linear_combination hc
  rw [he] at hv hV
  exact ⟨hv,hV⟩

end
end jacobi.GelfandLevitan
