import jacobi.GelfandLevitan.FiniteSecondDerivative

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual original finite physical Gram matrix satisfies its exact
spectral commutator Green identity. It includes coincident energies
without division by their difference and uses the already proved true
selected-branch endpoint Green identity of the original reference ODE.
This is the original finite Darboux identity's Gram input.
Use: finiteFeatureGram_green transfers the independently proved true original reference Green identity to the actual finite Gram matrix.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope realSolution realSlope

/-- The actual finite physical Gram matrix has exactly its original complex selected-solution integral, with the genuine physical normalization.
Use: finiteFeatureGram_green transfers the independently proved true original reference Green identity to the actual finite Gram matrix.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: substitute the already identified genuine original real Gram integral. Every integration point is in the unchanged physical half interval, where the explicit feature extensions retain the original selected solution. Complex inclusion commutes with the actual original integral. -/
theorem finiteFeatureGram_complex_integral (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (i j : FeatureIndex N) :
    (finiteFeatureGram a ha N t i j:ℂ)=∫ r in (0:ℝ)..(t:ℝ),
      solution a (finiteFeatureEnergy a ha i:ℂ) r*solution a (finiteFeatureEnergy a ha j:ℂ) r := by
  -- The actual original singular endpoint branch and original integration measure have already been fixed in both integrals.
  rw [finiteFeatureGram_integral,← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r∈Icc (0:ℝ) (t:ℝ) := by simpa only [uIcc_of_le t.property.1] using hr
  have hp : r∈Icc (0:ℝ) (1/2) := ⟨hr'.1,hr'.2.trans t.property.2⟩
  dsimp only
  rw [finiteFeatureWave_value ha i hp,finiteFeatureWave_value ha j hp,Complex.ofReal_mul,
    realSolution_cast,realSolution_cast]

/-- The genuine original finite Gram matrix satisfies its exact spectral commutator Green identity at every positive physical endpoint, including coincident energies.
Use: the original finite Darboux calculation uses this actual Gram identity with the differentiated true coefficient equation to obtain the finite transformed differential equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: specialize the independently proved original reference Green identity to the two actual finite feature energies. Identify its genuine original integral with the actual finite Gram entry, and use the independently proved real selected solutions and actual real slopes. No eigenvalue-difference division or feature-independence hypothesis is used. -/
theorem finiteFeatureGram_green (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (ht : 0<(t:ℝ)) (i j : FeatureIndex N) :
    (finiteFeatureEnergy a ha i-finiteFeatureEnergy a ha j)*finiteFeatureGram a ha N t i j=
      realSolution a (finiteFeatureEnergy a ha i) t*realSlope a (finiteFeatureEnergy a ha j) t-
        realSlope a (finiteFeatureEnergy a ha i) t*realSolution a (finiteFeatureEnergy a ha j) t := by
  -- The finite commutator identity inherits the independently proved actual selected-endpoint Green boundary cancellation.
  have hp : (t:ℝ)∈Ioo (0:ℝ) 1 := ⟨ht,by linarith [t.property.2]⟩
  have h := reference_green_identity ha (finiteFeatureEnergy a ha i:ℂ) (finiteFeatureEnergy a ha j:ℂ) hp
  rw [← finiteFeatureGram_complex_integral a ha N t i j] at h
  have hw : referenceWronskian a (finiteFeatureEnergy a ha i:ℂ) (finiteFeatureEnergy a ha j:ℂ) t=
      ((realSolution a (finiteFeatureEnergy a ha i) t*realSlope a (finiteFeatureEnergy a ha j) t-
        realSlope a (finiteFeatureEnergy a ha i) t*realSolution a (finiteFeatureEnergy a ha j) t:ℝ):ℂ) := by
    simp only [referenceWronskian,Complex.ofReal_sub,Complex.ofReal_mul,realSolution_cast,realSlope,
      solutionSlope_real a (finiteFeatureEnergy a ha i) hp,solutionSlope_real a (finiteFeatureEnergy a ha j) hp]
  rw [hw,← Complex.ofReal_sub,← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

end
end jacobi.GelfandLevitan
