import jacobi.GelfandLevitan.GreenActionIdentification

/-!
Article: jacobi, Theorem 2.1.
The original reconstruction, split into its actual regularized and Green
terms, has its genuine second-coordinate derivative on the physical
positive triangle. The selected primitives differentiate the Green term;
the original continuous L2 pairing differentiates the regularized term.
Use: the genuine kernelRows_regularized decomposition can be substituted directly into the actual constructed K.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope transformationKernel kernel regularizedKernel

/-- The original K reconstruction is exactly the original continuous spatial-row pairing.
Use: the genuine kernelRows_regularized decomposition can be substituted directly into the actual constructed K.
Article: jacobi, Theorem 2.1.
Proof: the already proved actual reconstruction integral is the spatialRowPairing integral, by exact original row evaluation and source kernel symmetry. -/
theorem transformationKernel_pairing (a : ℝ) (ha : -1<a) (t s : HalfInterval) :
    transformationKernel a ha t s= -kernel a ha t s-
      spatialRowPairing (solutionRow a ha t:Space) (kernelRows a ha s) := by
  rw [transformationKernel_reconstruction,spatialRowPairing_apply]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun r => by dsimp only; rw [kernelRows_apply,kernel_symmetric])

/-- The original K equals its exact four-term regularized and selected-primitive reconstruction on the required physical triangle.
Use: the derivative theorem for each of these independently constructed actual terms gives transformationKernel_hasDerivWithinAt_second.
Article: jacobi, Theorem 2.1.
Proof: decompose the genuine original source row, apply its true linear pairing, identify the original Green action, and use its actual lower-triangle selected factor. -/
theorem transformationKernel_regularized {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ))
    (t s : HalfInterval) (hs : d≤(s:ℝ)) (hst : (s:ℝ)≤t) :
    transformationKernel a ha t s=
      -regularizedRows a ha s (halfInclusion t)-
      displacementMass a ha*(realSolution a (jacobi.Jacobi.endpointCorrection a) s*
        realSolution a (jacobi.Jacobi.endpointCorrection a) (1-(t:ℝ))/zeroGreenConstant a)-
      spatialRowPairing (solutionRow a ha t:Space) (regularizedRows a ha s)-
      displacementMass a ha*greenActionFormula a ha hd hds t s := by
  -- The true original Hilbert inverse row remains fixed; only the actual source kernel is separated into its proved two parts.
  rw [transformationKernel_pairing,kernelRows_regularized,map_add,map_smul,smul_eq_mul,
    greenActionIdentification ha hd hds t s hs hst]
  change -kernel a ha t s-(_+_)= -regularizedKernel a ha s (halfTime (halfInclusion t))-_ - _ - _
  have ht : halfTime (halfInclusion t)=(t:ℝ) := by
    change min (t:ℝ) (1/2)=(t:ℝ)
    exact min_eq_left t.property.2
  rw [ht,regularizedKernel,kernel_symmetric,zeroGreen_factorization ha s.property t.property,
    zeroGreenFactor,min_eq_left hst,max_eq_right hst]
  ring

/-- The genuine second-coordinate derivative formula for the original K, built entirely from the actual regularized derivative, original inverse row and selected Green primitives.
Use: transformationKernel_hasDerivWithinAt_second proves it is the derivative of the original constructed kernel; its joint continuity gives diagonal differentiation.
Article: jacobi, Theorem 2.1.
-/
def secondDerivativeValue {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ))
    (t : HalfInterval) (s : DerivativeStrip d) : ℝ :=
  -regularizedSlopeRows ha hd s (halfInclusion t)-
    displacementMass a ha*(realSlope a (jacobi.Jacobi.endpointCorrection a) s*
      realSolution a (jacobi.Jacobi.endpointCorrection a) (1-(t:ℝ))/zeroGreenConstant a)-
    spatialRowPairing (solutionRow a ha t:Space) (regularizedSlopeRows ha hd s)-
    displacementMass a ha*greenActionSlope a ha hd hds t s

/-- The actual original K has its genuine second-coordinate derivative on each required closed positive physical slice, including its true diagonal and midpoint one-sided values.
Use: proves existence in Differentiability of K (b), and supplies the actual spatial derivative in the diagonal identity of (c).
Article: jacobi, Theorem 2.1.
Proof: differentiate the exact original four-term reconstruction. The regularized curve is differentiated in its genuine uniform norm and through the actual continuous L2 pairing; the selected solutions and the genuine Green primitives have their already proved actual derivatives. Restrict to the original physical interval and identify the unchanged original K there. -/
theorem transformationKernel_hasDerivWithinAt_second {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (t s : HalfInterval) (hs : d≤(s:ℝ)) (hst : (s:ℝ)≤t) :
    HasDerivWithinAt (fun x : ℝ => transformationKernel a ha t (halfParameterClamp x))
      (secondDerivativeValue ha hd (hs.trans s.property.2) t ⟨(s:ℝ),⟨hs,s.property.2⟩⟩)
      (Icc d (t:ℝ)) (s:ℝ) := by
  -- Every differentiated expression is independently identified with its actual original term before the physical reconstruction is substituted.
  have hds := hs.trans s.property.2
  have hsub : Icc d (t:ℝ)⊆Icc d (1/2:ℝ) := Icc_subset_Icc le_rfl t.property.2
  have hreg := (ContinuousMap.evalCLM ℝ (halfInclusion t)).hasFDerivAt.comp_hasDerivWithinAt (s:ℝ)
    (regularizedRows_hasDerivWithinAt ha hd ⟨hs,s.property.2⟩)
  have hpair := regularizedPairing_hasDerivWithinAt ha hd ⟨hs,s.property.2⟩ (solutionRow a ha t:Space)
  have hsol := (realSolution_hasDerivAt a (jacobi.Jacobi.endpointCorrection a)
    (show (s:ℝ)∈Ioo (0:ℝ) 1 from ⟨hd.trans_le hs,by linarith [s.property.2]⟩)).mul_const
      (realSolution a (jacobi.Jacobi.endpointCorrection a) (1-(t:ℝ)))
  have hgreen := greenActionFormula_hasDerivAt ha hd hds t ⟨hs,s.property.2⟩
  have h := (((hreg.mono hsub).neg.sub
      ((hsol.div_const (zeroGreenConstant a)).const_mul (displacementMass a ha)).hasDerivWithinAt).sub
      (hpair.mono hsub)).sub (hgreen.const_mul (displacementMass a ha)).hasDerivWithinAt
  change HasDerivWithinAt _ (secondDerivativeValue ha hd hds t ⟨(s:ℝ),⟨hs,s.property.2⟩⟩) _ _ at h
  apply h.congr
  · intro x hx
    have hp : x∈Icc (0:ℝ) (1/2) := ⟨(hd.trans_le hx.1).le,hx.2.trans t.property.2⟩
    have he : halfParameterClamp x=(⟨x,hp⟩:HalfInterval) := Set.projIcc_of_mem (by norm_num) hp
    dsimp only [Pi.sub_apply,Function.comp_apply,Pi.neg_apply,ContinuousMap.evalCLM_apply]
    rw [he]
    exact transformationKernel_regularized ha hd hds t ⟨x,hp⟩ hx.1 hx.2
  · have he : halfParameterClamp (s:ℝ)=s := Set.projIcc_of_mem (by norm_num) s.property
    dsimp only [Pi.sub_apply,Function.comp_apply,Pi.neg_apply,ContinuousMap.evalCLM_apply]
    rw [he]
    exact transformationKernel_regularized ha hd hds t s hs hst

end
end jacobi.GelfandLevitan
