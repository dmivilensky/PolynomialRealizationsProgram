import jacobi.GelfandLevitan.CorrectionDerivative

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual original transformed solution u has the displayed genuine
first spatial derivative at every complex energy, continuously on each
positive physical strip and with the correct midpoint one-sided value.
All terms use the already identified original partial_t K.
Use: transformedSlopeRows adds the independently differentiated original GL correction to this same genuine reference derivative.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope transformationKernel

/-- The actual reference spatial slope restricted to an unchanged positive physical strip.
Use: transformedSlopeRows adds the independently differentiated original GL correction to this same genuine reference derivative.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def referenceSlopeStrip (a : ℝ) {d : ℝ} (hd : 0<d) (z : ℂ) : C(DerivativeStrip d,ℂ) :=
  ⟨fun t => solutionSlope a z t,by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (solutionSlope_hasDerivAt a z
      (show (t:ℝ)∈Ioo (0:ℝ) 1 from ⟨hd.trans_le t.property.1,by linarith [t.property.2]⟩)).continuousAt.comp_of_eq
      continuous_subtype_val.continuousAt rfl⟩

/-- The actual original transformed spatial slope, continuously in its physical positive-strip parameter.
Use: transformedSolution_hasDerivWithinAt proves that these original values are the true first derivative of u at every complex energy, and the midpoint is the actual characteristic b.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def transformedSlopeRows {a d : ℝ} (ha : -1<a) (hd : 0<d) (z : ℂ) : C(DerivativeStrip d,ℂ) :=
  referenceSlopeStrip a hd z+correctionSlopeRows ha hd (halfSolution a ha z)

/-- The actual original transformed slope has exactly the literal displayed derivative formula, with its genuine original partial_t K integral.
Use: fixes the true derivative data in the subsequent differential equation, Green identity and midpoint characteristic b of the general target-operator Proposition C.2.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the original continuous derivative rows, identify the original half-solution value at its unchanged physical coordinate, and use the actual prefix pairing integral identity. -/
theorem transformedSlopeRows_apply {a d : ℝ} (ha : -1<a) (hd : 0<d) (z : ℂ) (t : DerivativeStrip d) :
    transformedSlopeRows ha hd z t=solutionSlope a z t+
      (kernelDiagonal a ha (derivativeStripInclusion hd t):ℂ)*solution a z t+
      ∫ r : Interval in prefixSet (t:ℝ),(derivativeCandidateRows ha hd t r:ℂ)*solution a z (halfTime r) := by
  change solutionSlope a z t+(prefixPairing _ _ _+_)=_
  rw [prefixPairing_apply,halfSolution_apply]
  have he : halfTime (halfInclusion (derivativeStripInclusion hd t))=(t:ℝ) := min_eq_left t.property.2
  rw [he]
  simp_rw [halfSolution_apply]
  dsimp only [derivativeStripInclusion,ContinuousMap.coe_mk]
  abel

/-- The original transformed solution has the actual displayed spatial derivative throughout every required positive physical interval, including its midpoint one-sided derivative, for every complex energy.
Use: proves the genuine first derivative asserted in equation app-du, before the separate original second-derivative and differential-equation argument.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: add the independently proved actual reference derivative and actual transformation-correction derivative. On the same original physical strip their unchanged values are exactly the original transformedSolution_reference_form. -/
theorem transformedSolution_hasDerivWithinAt {a d : ℝ} (ha : -1<a) (hd : 0<d) (z : ℂ)
    (t : HalfInterval) (hdt : d≤(t:ℝ)) :
    HasDerivWithinAt (fun x : ℝ => transformedSolution a ha (halfParameterClamp x) z)
      (transformedSlopeRows ha hd z ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩) (Icc d (1/2)) (t:ℝ) := by
  -- Both derivatives concern the original constructed functions; the original physical clamps fix every point of the required interval.
  have hf := (solution_hasDerivAt a z
    (show (t:ℝ)∈Ioo (0:ℝ) 1 from ⟨hd.trans_le hdt,by linarith [t.property.2]⟩)).hasDerivWithinAt
    (s := Icc d (1/2))
  have hc := correction_hasDerivWithinAt ha hd (halfSolution a ha z) t hdt
  have h := hf.add hc
  change HasDerivWithinAt _ (transformedSlopeRows ha hd z ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩) _ _ at h
  apply h.congr
  · intro x hx
    rw [transformedSolution_reference_form]
    have he : ((halfParameterClamp x):ℝ)=x :=
      congrArg Subtype.val (Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) ⟨(hd.trans_le hx.1).le,hx.2⟩)
    change solution a z ((halfParameterClamp x):ℝ)+_=solution a z x+_
    rw [he]
    rfl
  · rw [transformedSolution_reference_form]
    have he : halfParameterClamp (t:ℝ)=t := Set.projIcc_of_mem (by norm_num) t.property
    dsimp only [Pi.add_apply]
    rw [he]
    rfl

end
end jacobi.GelfandLevitan
