import jacobi.GelfandLevitan.FiniteDarboux

/-!
Article: jacobi, Appendix C.2.
The actual original finite GL transformation kernel satisfies its
genuine Darboux PDE. Its independently identified original partial
derivatives have the actual second derivatives displayed here. The
energy term is identical on both sides, so the original residual is
zero, with every finite inverse and approximation premise discharged.
Use: the genuine second t and s derivatives of the original finite K share this same original energy term, giving finiteKernelDarboux.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope

/-- The original finite spectral energy term in the actual transformation-kernel Darboux equation.
Use: the genuine second t and s derivatives of the original finite K share this same original energy term, giving finiteKernelDarboux.
Article: jacobi, Appendix C.2.
-/
def finiteKernelEnergyTerm (a : ℝ) (ha : -1<a) (N : ℕ) (t s : HalfInterval) : ℝ :=
  ∑ i : FeatureIndex N,finiteFeatureEnergy a ha i*finiteFeatureCoefficients a ha N t i*
    realSolution a (finiteFeatureEnergy a ha i) s

/-- The genuine first-coordinate derivative of the actual original finite K has its true Darboux second derivative at every positive physical parameter for all sufficiently long original spectral prefixes.
Use: finiteKernelDarboux combines this actual derivative with the genuine original second-coordinate derivative, proving the original finite transformation-kernel PDE.
Article: jacobi, Appendix C.2.
Proof: differentiate the independently identified original finite coefficient slope sum using the proved genuine original coefficient Darboux equation. The actual original finite kernel feature identity recombines its potential term, retaining the same original energy term.
-/
theorem finiteTransformationKernelSlope_hasDerivWithinAt (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ t s : HalfInterval,0<(t:ℝ) →
      HasDerivWithinAt (fun x => finiteTransformationKernelSlope a ha N x s)
        ((potential a t+2*finiteKernelDiagonalSlope a ha N t)*finiteTransformationKernel a ha N t s-
          finiteKernelEnergyTerm a ha N t s) (Icc ((t:ℝ)/2) (1/2)) (t:ℝ) := by
  -- The actual coefficient Darboux equation is already unconditional for sufficiently long original spectral prefixes.
  filter_upwards [finiteDarboux_coefficient_equation_eventually a ha,
    finiteTransformationKernel_feature_formula_eventually a ha] with N hCoeff hK t s ht
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hasDerivWithinAt_pi.mp (hCoeff t ht)) i).mul_const (realSolution a (finiteFeatureEnergy a ha i) s))
  change HasDerivWithinAt (fun x => finiteTransformationKernelSlope a ha N x s) _ _ _ at h
  convert h using 1
  rw [hK t s,finiteKernelEnergyTerm,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The genuine second-coordinate derivative of the actual original finite K has its true selected-solution second derivative throughout the positive physical strip for sufficiently long original spectral prefixes.
Use: finiteKernelDarboux compares this same actual original derivative with its independently proved first-coordinate second derivative.
Article: jacobi, Appendix C.2.
Proof: differentiate the original actual finite selected slopes at their genuine original feature energies using the independently proved original reference ODE. The exact finite kernel feature formula recombines the true potential term, leaving the same original energy term. -/
theorem finiteTransformationKernelSpatialSlope_hasDerivWithinAt (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ t s : HalfInterval,0<(s:ℝ) →
      HasDerivWithinAt (fun x => finiteTransformationKernelSpatialSlope a ha N t x)
        (potential a s*finiteTransformationKernel a ha N t s-finiteKernelEnergyTerm a ha N t s)
        (Icc ((s:ℝ)/2) (1/2)) (s:ℝ) := by
  -- The selected-slope acceleration is the genuine original reference differential equation, at each original finite feature energy.
  filter_upwards [finiteTransformationKernel_feature_formula_eventually a ha] with N hK t s hs
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((realSlope_hasDerivAt_equation ha (finiteFeatureEnergy a ha i)
      ⟨hs,by linarith [s.property.2]⟩).const_mul (finiteFeatureCoefficients a ha N t i)).hasDerivWithinAt
        (s := Icc ((s:ℝ)/2) (1/2)))
  change HasDerivWithinAt (fun x => finiteTransformationKernelSpatialSlope a ha N t x) _ _ _ at h
  convert h using 1
  rw [hK t s,finiteKernelEnergyTerm,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual original finite GL transformation kernel has zero genuine Darboux residual at every positive physical pair for sufficiently long original spectral prefixes, including the original midpoint one-sided derivatives.
Use: supplies the actual finite kernel intertwining identity in the original finite transformed ODE and quasi-derivative calculation, before passing to the infinite original GL solution.
Article: jacobi, Appendix C.2.
Proof: the already identified actual original partial slopes have their independently proved true second derivatives on their original positive physical strips. Unique derivatives on these nondegenerate strips identify the community derivWithin values. The same original finite energy term occurs on both sides and cancels exactly. -/
theorem finiteKernelDarboux (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ t s : HalfInterval,0<(t:ℝ) → 0<(s:ℝ) →
      derivWithin (fun x => finiteTransformationKernelSlope a ha N x s) (Icc ((t:ℝ)/2) (1/2)) (t:ℝ)-
        (potential a t+2*finiteKernelDiagonalSlope a ha N t)*finiteTransformationKernel a ha N t s=
      derivWithin (fun x => finiteTransformationKernelSpatialSlope a ha N t x) (Icc ((s:ℝ)/2) (1/2)) (s:ℝ)-
        potential a s*finiteTransformationKernel a ha N t s := by
  -- These derivative values refer to the actual original finite partial slopes already identified with K^(N), not an independently assumed PDE kernel.
  filter_upwards [finiteTransformationKernelSlope_hasDerivWithinAt a ha,
    finiteTransformationKernelSpatialSlope_hasDerivWithinAt a ha] with N hT hS t s ht hs
  have htu : UniqueDiffWithinAt ℝ (Icc ((t:ℝ)/2) (1/2)) (t:ℝ) :=
    (uniqueDiffOn_Icc (by linarith [t.property.2] : (t:ℝ)/2<(1/2:ℝ))) t ⟨by linarith,t.property.2⟩
  have hsu : UniqueDiffWithinAt ℝ (Icc ((s:ℝ)/2) (1/2)) (s:ℝ) :=
    (uniqueDiffOn_Icc (by linarith [s.property.2] : (s:ℝ)/2<(1/2:ℝ))) s ⟨by linarith,s.property.2⟩
  rw [(hT t s ht).derivWithin htu,(hS t s hs).derivWithin hsu]
  ring

end
end jacobi.GelfandLevitan
