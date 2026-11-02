import jacobi.GelfandLevitan.FiniteSystemDerivative
import jacobi.GelfandLevitan.FiniteKernelFormula
import jacobi.GelfandLevitan.FiniteTransformedSolution

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual finite GL kernel and its original diagonal have their
genuine first spatial derivatives on the positive physical domain.
They follow from the independently identified original finite-system
coefficients, with every finite inverse condition discharged uniformly.
Use: finiteTransformationKernel_hasDerivWithinAt_first proves this same expression differentiates the actual reconstructed finite transformation kernel.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope

/-- The genuine finite-system expression for the first-coordinate derivative of the original finite K.
Use: finiteTransformationKernel_hasDerivWithinAt_first proves this same expression differentiates the actual reconstructed finite transformation kernel.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteTransformationKernelSlope (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) (s : HalfInterval) : ℝ :=
  ∑ i : FeatureIndex N,finiteFeatureCoefficientsSlope a ha N t i*realSolution a (finiteFeatureEnergy a ha i) s

/-- The genuine finite-system expression for the second-coordinate derivative of the original finite K.
Use: finiteTransformationKernel_hasDerivWithinAt_second identifies it as the actual derivative of the original finite kernel, needed in its true differential identity.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteTransformationKernelSpatialSlope (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (s : ℝ) : ℝ :=
  ∑ i : FeatureIndex N,finiteFeatureCoefficients a ha N t i*realSlope a (finiteFeatureEnergy a ha i) s

/-- The genuine finite-system expression for the derivative of the original finite GL diagonal.
Use: finiteKernelDiagonal_hasDerivWithinAt proves its actual displayed diagonal derivative, giving the original finite potential q+2*(w^(N))'.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteKernelDiagonalSlope (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i : FeatureIndex N,(finiteFeatureCoefficientsSlope a ha N t i*realSolution a (finiteFeatureEnergy a ha i) t+
    finiteFeatureCoefficients a ha N t i*realSlope a (finiteFeatureEnergy a ha i) t)

/-- The actual original finite transformation kernels have their genuine first-coordinate derivatives throughout every positive physical strip, once the original spectral prefix is sufficiently long.
Use: differentiating the true finite GL equations and transformed solutions uses these actual finite kernel derivatives; no derivative or inverse premise is supplied.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual original finite coefficients have proved genuine derivatives and the original K^(N) is independently identified with their finite selected-solution expansion. Differentiate this same finite sum and restrict to its unchanged physical coordinates.
-/
theorem finiteTransformationKernel_hasDerivWithinAt_first (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (d : ℝ) (_hd : 0<d) (t s : HalfInterval),d≤(t:ℝ) →
      HasDerivWithinAt (fun x => finiteTransformationKernel a ha N (halfParameterClamp x) s)
        (finiteTransformationKernelSlope a ha N t s) (Icc d (1/2)) (t:ℝ) := by
  -- Every finite inverse and feature-identification condition is discharged by the proved original common spectral thresholds.
  filter_upwards [finiteTransformationKernel_feature_formula_eventually a ha,
    finiteFeatureCoefficients_hasDerivWithinAt_eventually a ha] with N hK hCoeff d hd t s hdt
  have hα := hCoeff d hd t ⟨hdt,t.property.2⟩
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hasDerivWithinAt_pi.mp hα) i).mul_const (realSolution a (finiteFeatureEnergy a ha i) s))
  change HasDerivWithinAt _ (finiteTransformationKernelSlope a ha N t s) _ _ at h
  apply h.congr
  · intro x hx
    have hp : x∈Icc (0:ℝ) (1/2) := ⟨(hd.trans_le hx.1).le,hx.2⟩
    rw [show halfParameterClamp x=(⟨x,hp⟩:HalfInterval) from Set.projIcc_of_mem (by norm_num) hp]
    exact hK ⟨x,hp⟩ s
  · rw [show halfParameterClamp (t:ℝ)=t from Set.projIcc_of_mem (by norm_num) t.property]
    exact hK t s

/-- The actual original finite transformation kernels have their genuine second-coordinate derivatives on every positive spatial strip once the original spectral prefix is sufficiently long.
Use: the finite Green and Darboux calculations refer to the original actual K^(N), with all inverse-system identifications already proved.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: in the independently identified original finite kernel formula the first-coordinate coefficients are fixed. The actual selected solution at every original feature energy has its genuine derivative, and a true finite sum preserves it on the unchanged physical strip. -/
theorem finiteTransformationKernel_hasDerivWithinAt_second (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (d : ℝ) (_hd : 0<d) (t s : HalfInterval),d≤(s:ℝ) →
      HasDerivWithinAt (fun x => finiteTransformationKernel a ha N t (halfParameterClamp x))
        (finiteTransformationKernelSpatialSlope a ha N t s) (Icc d (1/2)) (s:ℝ) := by
  -- The original genuine source-feature derivatives are applied only at positive physical spatial points.
  filter_upwards [finiteTransformationKernel_feature_formula_eventually a ha] with N hK d hd t s hds
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((realSolution_hasDerivAt a (finiteFeatureEnergy a ha i)
      ⟨hd.trans_le hds,by linarith [s.property.2]⟩).const_mul (finiteFeatureCoefficients a ha N t i)).hasDerivWithinAt
      (s := Icc d (1/2)))
  change HasDerivWithinAt _ (finiteTransformationKernelSpatialSlope a ha N t s) _ _ at h
  apply h.congr
  · intro x hx
    have hp : x∈Icc (0:ℝ) (1/2) := ⟨(hd.trans_le hx.1).le,hx.2⟩
    rw [show halfParameterClamp x=(⟨x,hp⟩:HalfInterval) from Set.projIcc_of_mem (by norm_num) hp]
    exact hK t ⟨x,hp⟩
  · rw [show halfParameterClamp (s:ℝ)=s from Set.projIcc_of_mem (by norm_num) s.property]
    exact hK t s

/-- The actual original finite GL diagonal has the genuine sum-of-partials derivative for every sufficiently long original spectral prefix on every positive physical strip.
Use: supplies the true finite potential q+2*(w^(N))' in the original finite transformed differential equation, including its midpoint one-sided value.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: differentiate the original finite coefficient/selected-solution product sum, whose independently proved actual derivatives give both terms. Its genuine original finite kernel identity on the diagonal identifies this same product sum with w^(N). -/
theorem finiteKernelDiagonal_hasDerivWithinAt (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (d : ℝ) (_hd : 0<d) (t : HalfInterval),d≤(t:ℝ) →
      HasDerivWithinAt (fun x => finiteKernelDiagonal a ha N (halfParameterClamp x))
        (finiteKernelDiagonalSlope a ha N t) (Icc d (1/2)) (t:ℝ) := by
  -- Both product derivatives are of the actual original finite coefficients and selected solutions at their unchanged physical energies.
  filter_upwards [finiteTransformationKernel_feature_formula_eventually a ha,
    finiteFeatureCoefficients_hasDerivWithinAt_eventually a ha] with N hK hCoeff d hd t hdt
  have hα := hCoeff d hd t ⟨hdt,t.property.2⟩
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hasDerivWithinAt_pi.mp hα) i).mul
      ((realSolution_hasDerivAt a (finiteFeatureEnergy a ha i)
        ⟨hd.trans_le hdt,by linarith [t.property.2]⟩).hasDerivWithinAt (s := Icc d (1/2))))
  change HasDerivWithinAt _ (finiteKernelDiagonalSlope a ha N t) _ _ at h
  apply h.congr
  · intro x hx
    have hp : x∈Icc (0:ℝ) (1/2) := ⟨(hd.trans_le hx.1).le,hx.2⟩
    rw [show halfParameterClamp x=(⟨x,hp⟩:HalfInterval) from Set.projIcc_of_mem (by norm_num) hp]
    exact hK ⟨x,hp⟩ ⟨x,hp⟩
  · rw [show halfParameterClamp (t:ℝ)=t from Set.projIcc_of_mem (by norm_num) t.property]
    exact hK t t

end
end jacobi.GelfandLevitan
