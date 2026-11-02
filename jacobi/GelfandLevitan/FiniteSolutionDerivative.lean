import jacobi.GelfandLevitan.FiniteSolutionExpansion

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual finite transformed solution has the genuine derivative of
its original finite primitive expansion. Its second derivative will
use the already proved finite coefficient Darboux ODE and the original
reference Green cancellation, rather than formal kernel differentiation
at the singular endpoint.
Use: finiteTransformedSolution_hasDerivWithinAt identifies this same finite expansion with the actual derivative, and its genuine second derivative gives the finite transformed ODE.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope realSolution realSlope

/-- The derivative expression of the original finite GL transformed solution.
Use: finiteTransformedSolution_hasDerivWithinAt identifies this same finite expansion with the actual derivative, and its genuine second derivative gives the finite transformed ODE.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteTransformedSlope (a : ℝ) (ha : -1<a) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  solutionSlope a z t+∑ i : FeatureIndex N,
    ((finiteFeatureCoefficientsSlope a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t+
      (finiteFeatureCoefficients a ha N t i:ℂ)*(realSolution a (finiteFeatureEnergy a ha i) t:ℂ)*solution a z t)

/-- The actual original finite transformed solution has the true physical derivative given by its original finite primitive expansion, with all finite inverse premises discharged.
Use: its subsequent genuine second-derivative equation concerns this same original finite GL approximation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: differentiate the independently identified finite primitive expansion. The actual original coefficients have their proved finite inverse derivatives, each actual primitive has its genuine endpoint FTC derivative, and the reference solution has its independently proved physical slope. Restriction to the physical strip preserves the original transformed solution. -/
theorem finiteTransformedSolution_hasDerivWithinAt (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z : ℂ),0<(t:ℝ) →
      HasDerivWithinAt (fun x => finiteTransformedSolution a ha N (halfParameterClamp x) z)
        (finiteTransformedSlope a ha N z t) (Icc ((t:ℝ)/2) (1/2)) (t:ℝ) := by
  -- All finite inverse conditions are already discharged before differentiating the actual GL transform.
  filter_upwards [finiteTransformedSolution_feature_formula a ha,
    finiteFeatureCoefficients_hasDerivWithinAt_eventually a ha] with N hU hCoeff t z ht
  have hd : 0<(t:ℝ)/2 := by linarith
  have hα := hCoeff ((t:ℝ)/2) hd (t:ℝ) ⟨by linarith,t.property.2⟩
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    (((hasDerivWithinAt_pi.mp hα) i).ofReal_comp).mul
      (finiteFeaturePrimitive_hasDerivAt a ha i z t).hasDerivWithinAt)
  have h := ((solution_hasDerivAt a z ⟨ht,by linarith [t.property.2]⟩).hasDerivWithinAt).add hsum
  have hv : solutionSlope a z t+∑ i : FeatureIndex N,
      ((finiteFeatureCoefficientsSlope a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t+
        (finiteFeatureCoefficients a ha N t i:ℂ)*((realSolution a (finiteFeatureEnergy a ha i) t:ℂ)*solution a z t))=
      finiteTransformedSlope a ha N z t := by
    rw [finiteTransformedSlope]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hv] at h
  apply h.congr
  · intro x hx
    have hp : x∈Icc (0:ℝ) (1/2) := ⟨(hd.trans_le hx.1).le,hx.2⟩
    rw [show halfParameterClamp x=(⟨x,hp⟩:HalfInterval) from Set.projIcc_of_mem (by norm_num) hp]
    exact hU ⟨x,hp⟩ z
  · rw [show halfParameterClamp (t:ℝ)=t from Set.projIcc_of_mem (by norm_num) t.property]
    exact hU t z

end
end jacobi.GelfandLevitan
