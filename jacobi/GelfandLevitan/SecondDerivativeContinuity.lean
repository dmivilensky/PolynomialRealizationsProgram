import jacobi.GelfandLevitan.KernelSecondDerivative

/-!
Article: jacobi, Theorem 2.1.
The actual second-coordinate derivative is jointly continuous up to
the positive diagonal and the midpoint. The Green action is continuous
through its original physical primitives; no continuity of a derivative
across the Green kernel's diagonal kink is assumed.
Use: completes Differentiability of K (b) and supplies the actual continuous spatial derivative needed to differentiate the original diagonal in (c).
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope transformationKernel regularizedSlope

/-- The genuine second-coordinate derivative values of K on its positive physical triangle have a jointly continuous extension to the full positive square, including its diagonal and midpoint.
Use: completes Differentiability of K (b) and supplies the actual continuous spatial derivative needed to differentiate the original diagonal in (c).
Article: jacobi, Theorem 2.1.
Proof: the original regularized derivative rows are continuous in uniform norm and the original inverse rows are continuous in L2 norm. Continuous evaluation and their true Hilbert pairing treat the regularized terms. Both selected slopes avoid their singular endpoints on the positive strip; the two genuine Green primitives are jointly continuous independently of any derivatives of K. -/
theorem transformationKernel_secondDerivative_continuous {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (hds : d≤(1/2:ℝ)) :
    Continuous (fun p : DerivativeStrip d×DerivativeStrip d =>
      secondDerivativeValue ha hd hds (derivativeStripInclusion hd p.1) p.2) := by
  -- All continuity is in the genuine norms of the already constructed original functions; the selected Green formula retains both physical primitives.
  have hcheck : Continuous (fun t : DerivativeStrip d =>
      realSolution a (jacobi.Jacobi.endpointCorrection a) (1-(t:ℝ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (realSolution_hasDerivAt a _
      (show 1-(t:ℝ)∈Ioo (0:ℝ) 1 from ⟨by linarith [t.property.2],by linarith [t.property.1]⟩)).continuousAt.comp_of_eq
      (continuousAt_const.sub continuous_subtype_val.continuousAt) rfl
  have hslope : Continuous (fun s : DerivativeStrip d =>
      realSlope a (jacobi.Jacobi.endpointCorrection a) (s:ℝ)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (realSlope_continuousAt a _
      (show (s:ℝ)∈Ioo (0:ℝ) 1 from ⟨hd.trans_le s.property.1,by linarith [s.property.2]⟩)).comp_of_eq
      continuous_subtype_val.continuousAt rfl
  have hcheckSlope : Continuous (fun s : DerivativeStrip d =>
      realSlope a (jacobi.Jacobi.endpointCorrection a) (1-(s:ℝ))) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (realSlope_continuousAt a _
      (show 1-(s:ℝ)∈Ioo (0:ℝ) 1 from ⟨by linarith [s.property.2],by linarith [s.property.1]⟩)).comp_of_eq
      (continuousAt_const.sub continuous_subtype_val.continuousAt) rfl
  have hreg : Continuous (fun p : DerivativeStrip d×DerivativeStrip d =>
      regularizedSlopeRows ha hd p.2 (halfInclusion (derivativeStripInclusion hd p.1))) :=
    (regularizedSlopeRows ha hd).uncurry.continuous.comp
      (continuous_snd.prodMk (halfInclusion.continuous.comp
        ((derivativeStripInclusion hd).continuous.comp continuous_fst)))
  have hsol : Continuous (fun t : DerivativeStrip d =>
      (solutionRow a ha (derivativeStripInclusion hd t):Space)) :=
    (continuous_subtype_val.comp (solutionRow_continuous a ha)).comp (derivativeStripInclusion hd).continuous
  have hpair : Continuous (fun p : DerivativeStrip d×DerivativeStrip d =>
      spatialRowPairing (solutionRow a ha (derivativeStripInclusion hd p.1):Space)
        (regularizedSlopeRows ha hd p.2)) :=
    (hsol.comp continuous_fst).inner
      ((ContinuousMap.toLp (𝕜 := ℝ) (p := 2) (E := ℝ) (α := Interval) volume).continuous.comp
        ((regularizedSlopeRows ha hd).continuous.comp continuous_snd))
  have hparam : Continuous (fun p : DerivativeStrip d×DerivativeStrip d =>
      (derivativeStripInclusion hd p.1,(p.2:ℝ))) :=
    ((derivativeStripInclusion hd).continuous.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hgreen : Continuous (fun p : DerivativeStrip d×DerivativeStrip d =>
      greenActionSlope a ha hd hds (derivativeStripInclusion hd p.1) p.2) :=
    (((hcheckSlope.comp continuous_snd).neg.mul
      ((leftGreenPrimitive a ha).continuous.comp hparam)).add
      ((hslope.comp continuous_snd).mul
        ((rightGreenPrimitive a ha hd hds).continuous.comp hparam))).div_const _
  exact ((hreg.neg.sub (((hslope.comp continuous_snd).mul (hcheck.comp continuous_fst)).div_const
    (zeroGreenConstant a) |>.const_mul (displacementMass a ha))).sub hpair).sub
      (hgreen.const_mul (displacementMass a ha))

/-- The actual original spatial derivative packaged as a continuous function on the positive physical square.
Use: genuine shrinking-segment averages of this same derivative identify the derivative of the original diagonal, using the proved actual physical-slice derivatives.
Article: jacobi, Theorem 2.1.
-/
def secondDerivativeMap {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ)) :
    C(DerivativeStrip d×DerivativeStrip d,ℝ) :=
  ⟨fun p => secondDerivativeValue ha hd hds (derivativeStripInclusion hd p.1) p.2,
    transformationKernel_secondDerivative_continuous ha hd hds⟩

end
end jacobi.GelfandLevitan
