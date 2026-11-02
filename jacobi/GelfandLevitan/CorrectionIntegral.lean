import jacobi.GelfandLevitan.PrefixPairing

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The original GL correction has an exact original difference-quotient
split into a fixed-prefix integral and a moving tail. Both parts use
their genuine original continuous K and the original spatial measure.
The split is established before taking any derivative limit.
Use: its genuine derivative supplies the integral part of the original transformed solution derivative, uniformly reusing the actual inverse rows.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformationKernel

/-- The actual original GL integral correction against an arbitrary continuous complex reference row.
Use: its genuine derivative supplies the integral part of the original transformed solution derivative, uniformly reusing the actual inverse rows.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def transformationCorrection (a : ℝ) (ha : -1<a) (w : C(Interval,ℂ)) : C(HalfInterval,ℂ) :=
  ⟨fun t => coefficientInput w (solutionRow a ha t:Space),
    (coefficientInput w).continuous.comp
      (halfSubspace.subtypeL.continuous.comp (solutionRow_continuous a ha))⟩

/-- The genuine original continuous integrand of the transformation correction in both physical half coordinates.
Use: its actual affine averages give the true moving-tail contribution to the original correction derivative.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def correctionIntegrand (a : ℝ) (ha : -1<a) (w : C(Interval,ℂ)) : C(HalfInterval×HalfInterval,ℂ) :=
  ⟨fun p => (transformationKernel a ha p.1 p.2:ℂ)*w (halfInclusion p.2),
    (Complex.continuous_ofReal.comp (transformationKernel_continuous a ha)).mul
      (w.continuous.comp (halfInclusion.continuous.comp continuous_snd))⟩

/-- Every original fixed-prefix correction integral equals its unchanged real physical interval integral.
Use: the original correction quotient is split using actual interval additivity before taking its genuine derivative limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original prefix functional has its genuine subtype integral. On that prefix the original half inclusion fixes the original unit coordinate. The already proved prefix-integral identity identifies it with the same original real-coordinate integral. -/
theorem correctionPrefix_integral (a : ℝ) (ha : -1<a) (w : C(Interval,ℂ)) (u t : HalfInterval) :
    prefixPairing t w (transformationRows a ha u)=
      ∫ r in (0:ℝ)..(t:ℝ),correctionIntegrand a ha w (u,halfParameterClamp r) := by
  -- The only coordinate extension is the actual half clamp, which is the identity at every original integration point.
  rw [prefixPairing_apply]
  have hp := prefix_integral (fun r : ℝ => correctionIntegrand a ha w (u,halfParameterClamp r))
    (show (t:ℝ)∈Icc (0:ℝ) 1 from ⟨t.property.1,by linarith [t.property.2]⟩)
  rw [← hp]
  apply setIntegral_congr_fun (prefixSet_measurable (t:ℝ))
  intro r hr
  dsimp only
  rw [halfParameterClamp_unit]
  change (transformationKernel a ha u (halfClamp r):ℂ)*w r=
    (transformationKernel a ha u (halfClamp r):ℂ)*w (halfInclusion (halfClamp r))
  congr 2
  apply Subtype.ext
  exact (min_eq_left (hr.trans t.property.2)).symm

/-- The actual diagonal correction equals its genuine original real physical integral.
Use: correctionIncrement_split subtracts two original endpoint equations in the same actual complex Banach space.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: its original inverse row and the continuous K row have the same actual prefix representative. Their genuine coefficient integrals agree, and correctionPrefix_integral supplies the literal real physical interval. -/
theorem transformationCorrection_integral (a : ℝ) (ha : -1<a) (w : C(Interval,ℂ)) (t : HalfInterval) :
    transformationCorrection a ha w t=
      ∫ r in (0:ℝ)..(t:ℝ),correctionIntegrand a ha w (t,halfParameterClamp r) := by
  rw [← correctionPrefix_integral]
  change coefficientInput w (solutionRow a ha t:Space)=coefficientInput w (candidateVector t (transformationRows a ha t):Space)
  congr 2
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [solutionRow_representative a ha t,candidateVector_ae t (transformationRows a ha t)] with r hs hc
  rw [hs,hc]
  rfl

/-- Fixed-prefix clipping leaves the actual original correction functional unchanged.
Use: the exact correction increment uses the original fixedTransformationRows derivative and the same original real prefix integral.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: both original functionals integrate over precisely the physical prefix, where the independently fixed spatial clipping is the identity. -/
theorem correctionPrefix_fixed (a : ℝ) (ha : -1<a) (w : C(Interval,ℂ)) (t : HalfInterval) (x : ℝ) :
    prefixPairing t w (fixedTransformationRows a ha t x)=
      ∫ r in (0:ℝ)..(t:ℝ),correctionIntegrand a ha w (halfParameterClamp x,halfParameterClamp r) := by
  rw [← correctionPrefix_integral,prefixPairing_fixedTransformationRows,prefixPairing_apply]
  rfl

/-- The literal original correction increment splits exactly into its actual fixed-prefix increment and moving-tail integral.
Use: correction_hasDerivWithinAt_right takes two independently justified genuine limits of this same original quotient.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: rewrite the original correction and fixed-prefix functionals as their genuine real interval integrals; the original tail integrand is continuous, so actual interval additivity gives the asserted exact split. -/
theorem correctionIncrement_split (a : ℝ) (ha : -1<a) (w : C(Interval,ℂ)) (t u : HalfInterval) :
    transformationCorrection a ha w u-transformationCorrection a ha w t=
      (prefixPairing t w (fixedTransformationRows a ha t (u:ℝ))-
        prefixPairing t w (fixedTransformationRows a ha t (t:ℝ)))+
      ∫ r in (t:ℝ)..(u:ℝ),correctionIntegrand a ha w (u,halfParameterClamp r) := by
  -- The genuine moving interval is split only after all terms have been identified in the unchanged physical measure.
  rw [transformationCorrection_integral,transformationCorrection_integral,correctionPrefix_fixed,correctionPrefix_fixed,
    show halfParameterClamp (u:ℝ)=u from Set.projIcc_of_mem (by norm_num) u.property,
    show halfParameterClamp (t:ℝ)=t from Set.projIcc_of_mem (by norm_num) t.property]
  have hc : Continuous (fun r : ℝ => correctionIntegrand a ha w (u,halfParameterClamp r)) :=
    (correctionIntegrand a ha w).continuous.comp (continuous_const.prodMk halfParameterClamp.continuous)
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (0:ℝ) (t:ℝ)) (hc.intervalIntegrable (μ := volume) (t:ℝ) (u:ℝ))
  rw [← h]
  abel

end
end jacobi.GelfandLevitan
