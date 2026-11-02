import jacobi.GelfandLevitan.FiniteSolutionSecondDerivative

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The original finite transformed solution satisfies the actual finite
Schrodinger equation. Its genuine acceleration is simplified by the
original reference Green identity and the independently proved actual
finite diagonal derivative. No finite differential equation is assumed.
Use: finiteTransformedSolution_ODE identifies the derivative of the actual finite transformed slope with the transformed potential; its quasi-derivative form is the identity required in the subsequent original infinite-limit argument.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope realSolution realSlope

/-- The genuine finite transformed acceleration satisfies the exact original finite Schrodinger equation, at arbitrary complex energy and with every approximation premise discharged.
Use: finiteTransformedSolution_ODE identifies the derivative of the actual finite transformed slope with the transformed potential; its quasi-derivative form is the identity required in the subsequent original infinite-limit argument.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: use the genuine finite primitive expansion of the actual original transformed solution. In each differentiated summand the independently proved reference Green identity cancels its spectral energy term. The remaining product-rule sum is exactly twice the actual finite diagonal derivative, cancelling the reference potential discrepancy. -/
theorem finiteTransformedSolution_equation (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z : ℂ),0<(t:ℝ) →
      -finiteTransformedAcceleration a ha N z t+
        ((potential a t+2*finiteKernelDiagonalSlope a ha N t:ℝ):ℂ)*finiteTransformedSolution a ha N t z=
          z*finiteTransformedSolution a ha N t z := by
  -- The original primitive Green identities contain the already proved singular-endpoint cancellation, so there is no unproved transformed boundary term.
  filter_upwards [finiteTransformedSolution_feature_formula a ha] with N hU t z ht
  let V := potential a t+2*finiteKernelDiagonalSlope a ha N t
  have hterm (i : FeatureIndex N) :
      ((((potential a t+2*finiteKernelDiagonalSlope a ha N t-finiteFeatureEnergy a ha i)*
          finiteFeatureCoefficients a ha N t i:ℝ):ℂ)*finiteFeaturePrimitive a ha i z t+
        (finiteFeatureCoefficientsSlope a ha N t i:ℂ)*((realSolution a (finiteFeatureEnergy a ha i) t:ℂ)*solution a z t)+
        (((finiteFeatureCoefficientsSlope a ha N t i:ℂ)*(realSolution a (finiteFeatureEnergy a ha i) t:ℂ)+
          (finiteFeatureCoefficients a ha N t i:ℂ)*(realSlope a (finiteFeatureEnergy a ha i) t:ℂ))*solution a z t+
        (finiteFeatureCoefficients a ha N t i:ℂ)*(realSolution a (finiteFeatureEnergy a ha i) t:ℂ)*solutionSlope a z t))=
      (((V:ℂ)-z)*((finiteFeatureCoefficients a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t)+
        2*((finiteFeatureCoefficientsSlope a ha N t i*realSolution a (finiteFeatureEnergy a ha i) t+
          finiteFeatureCoefficients a ha N t i*realSlope a (finiteFeatureEnergy a ha i) t:ℝ):ℂ)*solution a z t) := by
    have hG := finiteFeaturePrimitive_green a ha i z t ht
    dsimp only [V]
    push_cast
    linear_combination -(finiteFeatureCoefficients a ha N t i:ℂ)*hG
  have hacc : finiteTransformedAcceleration a ha N z t=solutionAcceleration a z t+
      ((V:ℂ)-z)*(∑ i : FeatureIndex N,(finiteFeatureCoefficients a ha N t i:ℂ)*finiteFeaturePrimitive a ha i z t)+
      2*(finiteKernelDiagonalSlope a ha N t:ℂ)*solution a z t := by
    rw [finiteTransformedAcceleration]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    have hdiag : (∑ i : FeatureIndex N,
        2*((finiteFeatureCoefficientsSlope a ha N t i*realSolution a (finiteFeatureEnergy a ha i) t+
          finiteFeatureCoefficients a ha N t i*realSlope a (finiteFeatureEnergy a ha i) t:ℝ):ℂ)*solution a z t)=
        2*(finiteKernelDiagonalSlope a ha N t:ℂ)*solution a z t := by
      rw [finiteKernelDiagonalSlope,Complex.ofReal_sum,Finset.mul_sum,Finset.sum_mul]
    rw [hdiag]
    ring
  rw [hacc,hU t z]
  dsimp only [V]
  push_cast
  linear_combination solution_equation ha z ⟨ht,by linarith [t.property.2]⟩

/-- The actual finite transformed slope satisfies its genuine finite Schrodinger ODE on the positive physical strip, including the midpoint one-sided derivative.
Use: the finite quasi-derivative identity and the subsequent original limit use this same actual finite GL transformed solution and its independently identified first derivative.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: combine the independently proved genuine slope derivative with its exact finite Green simplification. The displayed acceleration is therefore the derivative of the original finite transformed solution's actual slope. -/
theorem finiteTransformedSolution_ODE (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z : ℂ),0<(t:ℝ) →
      HasDerivWithinAt (finiteTransformedSlope a ha N z)
        ((((potential a t+2*finiteKernelDiagonalSlope a ha N t:ℝ):ℂ)-z)*finiteTransformedSolution a ha N t z)
        (Icc ((t:ℝ)/2) (1/2)) (t:ℝ) := by
  filter_upwards [finiteTransformedSlope_hasDerivWithinAt a ha,finiteTransformedSolution_equation a ha]
    with N hD hODE t z ht
  have he := hODE t z ht
  have hv : finiteTransformedAcceleration a ha N z t=
      (((potential a t+2*finiteKernelDiagonalSlope a ha N t:ℝ):ℂ)-z)*finiteTransformedSolution a ha N t z := by
    linear_combination -he
  rw [← hv]
  exact hD t z ht

end
end jacobi.GelfandLevitan
