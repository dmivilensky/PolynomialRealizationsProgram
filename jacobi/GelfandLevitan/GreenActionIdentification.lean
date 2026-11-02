import jacobi.GelfandLevitan.GreenActionPrimitives

/-!
Article: jacobi, Theorem 2.1.
The genuine reference Green contribution in the original GL reconstruction
is exactly its two selected-solution primitives. All integrals retain the
original physical measure. This identification allows the independently
proved primitive derivative to differentiate the original K itself.
Use: decomposes the original reconstruction pairing into its regularized and selected Green contributions, prior to differentiating K.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope transformationKernel zeroGreenKernel regularizedKernel

/-- The original reference Green rows in the same genuine continuous spatial space as the GL rows.
Use: decomposes the original reconstruction pairing into its regularized and selected Green contributions, prior to differentiating K.
Article: jacobi, Theorem 2.1.
-/
def greenRows (a : ℝ) (ha : -1<a) : C(HalfInterval,C(Interval,ℝ)) :=
  (⟨fun p : HalfInterval×Interval => zeroGreenKernel a (p.1:ℝ) (halfTime p.2),
    (zeroGreenKernel_continuousOn ha).comp_continuous
      (g := fun p : ℝ×ℝ => zeroGreenKernel a p.1 p.2)
      (f := fun p : HalfInterval×Interval => ((p.1:ℝ),halfTime p.2))
      ((continuous_subtype_val.comp continuous_fst).prodMk (halfTime.continuous.comp continuous_snd))
      (fun p => ⟨p.1.property,halfTime_mem p.2⟩)⟩ : C(HalfInterval×Interval,ℝ)).curry

/-- The original source row splits exactly into its original regularized row and the genuine reference Green row.
Use: the actual K reconstruction is differentiated by its two independently justified analytic contributions.
Article: jacobi, Proposition C.3.
Proof: evaluate the actual continuous rows and use the defining regularization of the original kernel. -/
theorem kernelRows_regularized (a : ℝ) (ha : -1<a) (s : HalfInterval) :
    kernelRows a ha s=regularizedRows a ha s+displacementMass a ha • greenRows a ha s := by
  ext r
  rw [kernelRows_apply]
  change kernel a ha s (halfTime r)=regularizedKernel a ha s (halfTime r)+
    displacementMass a ha*zeroGreenKernel a s (halfTime r)
  rw [regularizedKernel]
  ring

/-- Pairing the original inverse solution with a continuous spatial row is precisely its physical-prefix K integral.
Use: identifies the true Green pairing in the original K reconstruction with the selected-solution primitive formula, without evaluating arbitrary L2 representatives pointwise.
Article: jacobi, Theorem 2.1.
Proof: substitute the proved almost-everywhere original K representative, then use the community indicator-integral identity in the unchanged physical measure. -/
theorem solutionRow_pairing (a : ℝ) (ha : -1<a) (t : HalfInterval) (g : C(Interval,ℝ)) :
    spatialRowPairing (solutionRow a ha t:Space) g=
      ∫ r : Interval in prefixSet (t:ℝ),transformationKernel a ha t (halfClamp r)*g r := by
  rw [spatialRowPairing_apply,← integral_indicator (prefixSet_measurable (t:ℝ))]
  apply integral_congr_ae
  filter_upwards [solutionRow_representative a ha t] with r hr
  rw [hr]
  by_cases hp : r∈prefixSet (t:ℝ)
  · rw [indicator_of_mem hp,indicator_of_mem hp]
  · rw [indicator_of_notMem hp,indicator_of_notMem hp,zero_mul]

/-- The original inverse-row Green pairing equals the literal original real-coordinate Green action.
Use: greenActionIdentification proves that this same genuine term of the K reconstruction has the previously proved selected-primitive derivative.
Article: jacobi, Theorem 2.1.
Proof: substitute the actual original K prefix representative and use the proved equality of subtype-prefix and physical real interval integrals. -/
theorem greenPairing_integral (a : ℝ) (ha : -1<a) (t s : HalfInterval) :
    spatialRowPairing (solutionRow a ha t:Space) (greenRows a ha s)=
      ∫ r in (0:ℝ)..(t:ℝ),transformationKernel a ha t (halfParameterClamp r)*
        zeroGreenKernel a (s:ℝ) ((halfParameterClamp r):ℝ) := by
  rw [solutionRow_pairing]
  have hp := prefix_integral (fun r : ℝ => transformationKernel a ha t (halfParameterClamp r)*
      zeroGreenKernel a (s:ℝ) ((halfParameterClamp r):ℝ))
    (show (t:ℝ)∈Icc (0:ℝ) 1 from ⟨t.property.1,by linarith [t.property.2]⟩)
  simp_rw [halfParameterClamp_unit,halfClamp_val] at hp
  exact hp

/-- The actual original Green action equals exactly the selected-solution formula with the genuine two weighted K primitives.
Use: greenActionFormula_hasDerivAt now differentiates the original Green contribution to K, retaining its true diagonal kink and the true physical integration interval.
Article: jacobi, Theorem 2.1.
Proof: split the actual continuous original Green integrand at the physical spatial point. On each original interval use the independently proved full Green factorization and the correct minimum/maximum branch. Pull out the fixed selected factors and recognize the two genuine weighted primitives. -/
theorem greenActionIdentification {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ))
    (t s : HalfInterval) (hs : d≤(s:ℝ)) (hst : (s:ℝ)≤t) :
    spatialRowPairing (solutionRow a ha t:Space) (greenRows a ha s)=greenActionFormula a ha hd hds t s := by
  -- The branch split is applied to the original Green integral, with its own actual continuous integrand.
  rw [greenPairing_integral]
  let f : ℝ→ℝ := fun r => transformationKernel a ha t (halfParameterClamp r)*
    zeroGreenKernel a (s:ℝ) ((halfParameterClamp r):ℝ)
  have hc : Continuous f := by
    have hG : Continuous (fun r : ℝ => zeroGreenKernel a (s:ℝ) ((halfParameterClamp r):ℝ)) :=
      (zeroGreenKernel_continuousOn ha).comp_continuous
        (g := fun p : ℝ×ℝ => zeroGreenKernel a p.1 p.2)
        (f := fun r : ℝ => ((s:ℝ),((halfParameterClamp r):ℝ)))
        (continuous_const.prodMk (continuous_subtype_val.comp halfParameterClamp.continuous))
        (fun r => ⟨s.property,(halfParameterClamp r).property⟩)
    exact ((transformationKernel_continuous a ha).comp
      (continuous_const.prodMk halfParameterClamp.continuous)).mul hG
  have hleft : (∫ r in (0:ℝ)..(s:ℝ),f r)=
      (realSolution a (jacobi.Jacobi.endpointCorrection a) (1-(s:ℝ))/zeroGreenConstant a)*
        leftGreenPrimitive a ha (t,(s:ℝ)) := by
    rw [leftGreenPrimitive,weightedKernelPrimitive]
    dsimp only [ContinuousMap.coe_mk]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc (0:ℝ) (s:ℝ) := by simpa only [uIcc_of_le s.property.1] using hr
    have hp : r∈Icc (0:ℝ) (1/2) := ⟨hr'.1,hr'.2.trans s.property.2⟩
    have hcl : ((halfParameterClamp r):ℝ)=r := by
      exact congrArg Subtype.val (Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) hp)
    dsimp only [f,weightedKernelIntegrand,ContinuousMap.coe_mk]
    rw [hcl,zeroGreen_factorization ha s.property hp,zeroGreenFactor,
      min_eq_right hr'.2,max_eq_left hr'.2,leftZeroWeight_value ha hp]
    ring
  have hright : (∫ r in (s:ℝ)..(t:ℝ),f r)=
      (realSolution a (jacobi.Jacobi.endpointCorrection a) (s:ℝ)/zeroGreenConstant a)*
        rightGreenPrimitive a ha hd hds (t,(s:ℝ)) := by
    rw [rightGreenPrimitive_integral,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc (s:ℝ) (t:ℝ) := by simpa only [uIcc_of_le hst] using hr
    have hp : r∈Icc (0:ℝ) (1/2) := ⟨s.property.1.trans hr'.1,hr'.2.trans t.property.2⟩
    have hcl : ((halfParameterClamp r):ℝ)=r := by
      exact congrArg Subtype.val (Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) hp)
    dsimp only [f,weightedKernelIntegrand,ContinuousMap.coe_mk]
    rw [hcl,zeroGreen_factorization ha s.property hp,zeroGreenFactor,
      min_eq_left hr'.1,max_eq_right hr'.1,rightZeroWeight_value ha hd hds ⟨hs.trans hr'.1,hp.2⟩]
    ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (0:ℝ) (s:ℝ)) (hc.intervalIntegrable (μ := volume) (s:ℝ) (t:ℝ))
  change (∫ r in (0:ℝ)..(t:ℝ),f r)=_
  rw [← hadd,hleft,hright,greenActionFormula]
  ring

end
end jacobi.GelfandLevitan
