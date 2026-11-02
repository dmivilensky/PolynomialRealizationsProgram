import jacobi.GelfandLevitan.FiniteSolutionDerivative

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual finite transformed slope has its genuine second derivative.
All coefficient accelerations come from the proved original finite
Darboux equation. FiniteSolutionEquation then uses the actual reference
Green identity to reduce this expression to the transformed ODE.
Use: finiteTransformedSlope_hasDerivWithinAt proves this is the genuine acceleration, and finiteTransformedSolution_equation simplifies it to the original transformed Schrodinger equation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope realSolution realSlope

/-- The actual differentiated finite primitive expansion for the original transformed solution.
Use: finiteTransformedSlope_hasDerivWithinAt proves this is the genuine acceleration, and finiteTransformedSolution_equation simplifies it to the original transformed Schrodinger equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteTransformedAcceleration (a : ℝ) (ha : -1<a) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  solutionAcceleration a z t+∑ i : FeatureIndex N,
    ((((potential a t+2*finiteKernelDiagonalSlope a ha N t-finiteFeatureEnergy a ha i)*
        finiteFeatureCoefficients a ha N t i:ℝ):ℂ)*finiteFeaturePrimitive a ha i z t+
      (finiteFeatureCoefficientsSlope a ha N t i:ℂ)*((realSolution a (finiteFeatureEnergy a ha i) t:ℂ)*solution a z t)+
      (((finiteFeatureCoefficientsSlope a ha N t i:ℂ)*(realSolution a (finiteFeatureEnergy a ha i) t:ℂ)+
        (finiteFeatureCoefficients a ha N t i:ℂ)*(realSlope a (finiteFeatureEnergy a ha i) t:ℂ))*solution a z t+
      (finiteFeatureCoefficients a ha N t i:ℂ)*(realSolution a (finiteFeatureEnergy a ha i) t:ℂ)*solutionSlope a z t))

/-- The actual finite transformed slope has the genuine original acceleration, with all finite-system and coefficient-ODE premises discharged.
Use: the finite transformed differential equation identifies this same actual derivative, rather than an independently prescribed acceleration.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: differentiate the independently identified original finite slope. Its coefficient derivatives and accelerations are proved for the original finite inverse system, its primitives have their actual FTC derivatives, and its reference features have the genuine original slopes. Products and the true finite sum give exactly the displayed acceleration. -/
theorem finiteTransformedSlope_hasDerivWithinAt (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z : ℂ),0<(t:ℝ) →
      HasDerivWithinAt (finiteTransformedSlope a ha N z)
        (finiteTransformedAcceleration a ha N z t) (Icc ((t:ℝ)/2) (1/2)) (t:ℝ) := by
  -- The actual coefficient accelerations are supplied by the proved Darboux ODE, uniformly beyond one original spectral threshold.
  filter_upwards [finiteFeatureCoefficients_hasDerivWithinAt_eventually a ha,
    finiteDarboux_coefficient_equation_eventually a ha] with N hCoeff hODE t z ht
  have hd : 0<(t:ℝ)/2 := by linarith
  have hα := hCoeff ((t:ℝ)/2) hd (t:ℝ) ⟨by linarith,t.property.2⟩
  have hα1 := hODE t ht
  have hp : (t:ℝ)∈Ioo (0:ℝ) 1 := ⟨ht,by linarith [t.property.2]⟩
  have hf := (solution_hasDerivAt a z hp).hasDerivWithinAt (s := Icc ((t:ℝ)/2) (1/2))
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((((hasDerivWithinAt_pi.mp hα1) i).ofReal_comp).mul
      (finiteFeaturePrimitive_hasDerivAt a ha i z t).hasDerivWithinAt).add
    (((((hasDerivWithinAt_pi.mp hα) i).ofReal_comp).mul
      ((realSolution_hasDerivAt a (finiteFeatureEnergy a ha i) hp).ofReal_comp.hasDerivWithinAt)).mul hf))
  have h := ((solutionSlope_hasDerivAt a z hp).hasDerivWithinAt).add hsum
  change HasDerivWithinAt (finiteTransformedSlope a ha N z) (finiteTransformedAcceleration a ha N z t) _ _ at h
  exact h

end
end jacobi.GelfandLevitan
