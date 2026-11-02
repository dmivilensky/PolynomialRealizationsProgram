import jacobi.GelfandLevitan.GreenActionIdentification
import jacobi.GelfandLevitan.Profiles
import jacobi.GelfandLevitan.KernelRowEquation

/-!
Article: jacobi, Proposition C.3.
Use: the genuine finite target polynomial limit equals this same u, not an independently specified integral solution.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] transformationKernel realSolution

/-- The actual real transformed solution is exactly its original
reference wave plus the true real-prefix GL transformation integral.
Use: the genuine finite target polynomial limit equals this same u,
not an independently specified integral solution.
Article: jacobi, Proposition C.3.
Proof: the established real-energy expression contains the actual
inverse-row coefficient integral. The proved source row representative
identifies it with the genuine K integral, and the original subtype
prefix measure equals the unchanged real physical-prefix measure. -/
theorem realTransformedSolution_integral (a:ℝ) (ha:-1<a) (E:ℝ) (t:HalfInterval) :
    realTransformedSolution a ha E t=realSolution a E (t:ℝ)+
      ∫r in (0:ℝ)..(t:ℝ), transformationKernel a ha t (halfParameterClamp r)*
        realSolution a E (halfParameterClamp r:ℝ) := by
  -- The same genuine inverse row is used in both the entire and real integral constructions.
  change (transformedSolution a ha t (E:ℂ)).re=_
  rw [transformedSolution_real,Complex.ofReal_re]
  congr 1
  have hrow := solutionRow_pairing a ha t (realHalfWave a ha E)
  rw [spatialRowPairing_apply] at hrow
  change realCoefficient a (solutionRow a ha t:Space) E=_ at hrow
  rw [hrow]
  have hp := prefix_integral (fun r:ℝ => transformationKernel a ha t (halfParameterClamp r)*
    realSolution a E (halfParameterClamp r:ℝ))
    (show (t:ℝ)∈Icc (0:ℝ) 1 from ⟨t.property.1,t.property.2.trans (by norm_num)⟩)
  simp_rw [halfParameterClamp_unit,halfClamp_val] at hp
  exact hp

end
end jacobi.GelfandLevitan
