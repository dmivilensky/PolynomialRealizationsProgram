import jacobi.GelfandLevitan.CorrectionIntegral

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual original transformation correction has its genuine continuous
derivative on each full positive physical strip. The fixed-prefix term
uses its true Banach-space derivative; its moving tail uses the actual
continuous integrand's shrinking average. Their original physical
values are retained at the diagonal and midpoint.
Use: correction_hasDerivWithinAt proves this same expression is the genuine correction derivative, and transformedSolution_hasDerivWithinAt adds the actual reference derivative.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformationKernel
attribute [local irreducible] derivativeCandidateRows derivativeForcingRows kernelSlope

/-- The actual original differentiated transformation correction, continuously in its positive physical parameter.
Use: correction_hasDerivWithinAt proves this same expression is the genuine correction derivative, and transformedSolution_hasDerivWithinAt adds the actual reference derivative.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def correctionSlopeRows {a d : ℝ} (ha : -1<a) (hd : 0<d) (w : C(Interval,ℂ)) : C(DerivativeStrip d,ℂ) :=
  ⟨fun t => prefixPairing (derivativeStripInclusion hd t) w (derivativeCandidateRows ha hd t)+
      (kernelDiagonal a ha (derivativeStripInclusion hd t):ℂ)*w (halfInclusion (derivativeStripInclusion hd t)),by
    have hv : Continuous (fun t : DerivativeStrip d =>
        (candidateVector (derivativeStripInclusion hd t) (derivativeCandidateRows ha hd t):Space)) :=
      halfSubspace.subtypeL.continuous.comp
        (Continuous.comp (g := fun p : HalfInterval×C(Interval,ℝ) => candidateVector p.1 p.2)
          (f := fun t : DerivativeStrip d => (derivativeStripInclusion hd t,derivativeCandidateRows ha hd t))
          candidateVector_joint_continuous ((derivativeStripInclusion hd).continuous.prodMk
            (derivativeCandidateRows ha hd).continuous))
    exact ((coefficientInput w).continuous.comp hv).add
      ((Complex.continuous_ofReal.comp ((kernelDiagonal a ha).continuous.comp (derivativeStripInclusion hd).continuous)).mul
        (w.continuous.comp (halfInclusion.continuous.comp (derivativeStripInclusion hd).continuous)))⟩

/-- The true original transformation correction has its displayed actual right derivative at every positive physical parameter below the midpoint.
Use: correction_hasDerivWithinAt upgrades this actual quotient limit to the full closed-strip derivative by the already proved independent derivative continuity.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: apply the genuine fixed-prefix bounded functional to the actual uniform-row derivative. Add the independent continuous moving-tail average limit. The exact correctionIncrement_split identifies the sum of these actual quotients with the literal original correction quotient. -/
theorem correction_hasDerivWithinAt_right {a d : ℝ} (ha : -1<a) (hd : 0<d) (w : C(Interval,ℂ))
    (t : HalfInterval) (hdt : d≤(t:ℝ)) (htop : (t:ℝ)<1/2) :
    HasDerivWithinAt (fun x : ℝ => transformationCorrection a ha w (halfParameterClamp x))
      (correctionSlopeRows ha hd w ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩) (Ici (t:ℝ)) (t:ℝ) := by
  -- Both limits come from the genuine original integrals. The changing physical cutoff itself is never differentiated in operator norm.
  have hf := (prefixPairing t w).hasFDerivAt.comp_hasDerivWithinAt (t:ℝ)
    (fixedTransformationRows_hasDerivWithinAt ha hd t hdt ⟨le_rfl,t.property.2⟩)
  have hval : prefixPairing t w (fixedTransformationSlopeRows ha hd (hdt.trans t.property.2) t (t:ℝ))=
      prefixPairing t w (derivativeCandidateRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩) := by
    rw [prefixPairing_fixedTransformationSlopeRows ha hd t hdt w,prefixPairing_apply]
  rw [hval] at hf
  have hlimf := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (t:ℝ))).mp
    ((hf.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE htop)).Ioi_of_Ici)
  have hself : halfParameterClamp (t:ℝ)=t := Set.projIcc_of_mem (by norm_num) t.property
  have hlimc : Tendsto (fun x : ℝ => halfParameterClamp x) (𝓝[>] (t:ℝ)) (𝓝 t) := by
    simpa only [hself] using (halfParameterClamp.continuous.continuousAt (x := (t:ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (t:ℝ)))
  have hlims := (affineAverage_tendsto (correctionIntegrand a ha w) t).comp hlimc
  have hlim := hlimf.add hlims
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (t:ℝ))).mpr
  change Tendsto _ _ (𝓝 (prefixPairing t w (derivativeCandidateRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩)+
    correctionIntegrand a ha w (t,t)))
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT htop] with x hx
  have hp : x∈Icc (0:ℝ) (1/2) := ⟨t.property.1.trans hx.1.le,hx.2.le⟩
  have he : halfParameterClamp x=(⟨x,hp⟩:HalfInterval) := Set.projIcc_of_mem (by norm_num) hp
  have hn : (⟨x,hp⟩:HalfInterval)≠t := fun h => hx.1.ne' (congrArg Subtype.val h)
  dsimp only [Function.comp_apply]
  rw [slope_def_module,slope_def_module,hself,he,affineAverage_integral _ _ _ hn]
  change (x-(t:ℝ))⁻¹ • (prefixPairing t w (fixedTransformationRows a ha t x)-
    prefixPairing t w (fixedTransformationRows a ha t (t:ℝ)))+_=
      (x-(t:ℝ))⁻¹ • (transformationCorrection a ha w ⟨x,hp⟩-transformationCorrection a ha w t)
  rw [correctionIncrement_split a ha w t ⟨x,hp⟩,smul_add]

/-- The actual original GL correction has its genuine continuous derivative throughout each required positive physical interval, including its midpoint one-sided derivative.
Use: the actual transformed solution is the original reference solution plus this same correction, giving precisely equation app-du with no extra analytic premise.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original correction is continuous, its independently constructed actual derivative rows are continuous on each closed positive strip, and its genuine right derivatives have just been proved from the original quotient split. Apply the right-derivative FTC, retaining all original physical values. -/
theorem correction_hasDerivWithinAt {a d : ℝ} (ha : -1<a) (hd : 0<d) (w : C(Interval,ℂ))
    (t : HalfInterval) (hdt : d≤(t:ℝ)) :
    HasDerivWithinAt (fun x : ℝ => transformationCorrection a ha w (halfParameterClamp x))
      (correctionSlopeRows ha hd w ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩) (Icc d (1/2)) (t:ℝ) := by
  -- Actual continuous right derivatives reach the genuine closed-strip endpoints by the proved FTC extension theorem.
  have hds := hdt.trans t.property.2
  let P : C(ℝ,DerivativeStrip d) := ⟨Set.projIcc d (1/2) hds,continuous_projIcc⟩
  let g := (correctionSlopeRows ha hd w).comp P
  have he (x : ℝ) (hx : x∈Icc d (1/2)) : g x=correctionSlopeRows ha hd w ⟨x,hx⟩ := by
    change correctionSlopeRows ha hd w (Set.projIcc d (1/2) hds x)=_
    rw [Set.projIcc_of_mem hds hx]
  have hright (x : ℝ) (hx : x∈Ico d (1/2)) :
      HasDerivWithinAt (fun y : ℝ => transformationCorrection a ha w (halfParameterClamp y)) (g x) (Ici x) x := by
    rw [he x ⟨hx.1,hx.2.le⟩]
    exact correction_hasDerivWithinAt_right ha hd w ⟨x,⟨(hd.trans_le hx.1).le,hx.2.le⟩⟩ hx.1 hx.2
  have h := continuous_hasDerivWithinAt_of_right
    ((transformationCorrection a ha w).continuous.comp halfParameterClamp.continuous) g.continuous ⟨hdt,t.property.2⟩ hright
  rw [he (t:ℝ) ⟨hdt,t.property.2⟩] at h
  exact h

end
end jacobi.GelfandLevitan
