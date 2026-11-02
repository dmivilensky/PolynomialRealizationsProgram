import jacobi.GelfandLevitan.TransformationOperator
import jacobi.GelfandLevitan.SelectedEndpoint

/-!
Article: jacobi, Proposition C.2.
The actual transformation acts continuously on continuous complex waves.
Consequently u is entire in the uniform spatial norm, so the Green
product integral is continuous in energy. The selected endpoint branch
also excludes the identically zero solution at every complex energy.
Use: continuousTransformation constructs one bounded complex-linear operator whose application to the original reference wave is the original transformed solution.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual continuous complex Volterra transform, retaining the physical half-domain clamp.
Use: continuousTransformation constructs one bounded complex-linear operator whose application to the original reference wave is the original transformed solution.
Article: jacobi, Proposition C.2.
-/
def transformationWaveMap (a : ℝ) (ha : -1<a) (W : C(Interval,ℂ)) : C(Interval,ℂ) :=
  ⟨fun t => W t+coefficientFunctional (solutionRow a ha (halfClamp t):Space) W,
    W.continuous.add ((coefficientInput W).continuous.comp
      (halfSubspace.subtypeL.continuous.comp ((solutionRow_continuous a ha).comp halfClamp.continuous)))⟩

/-- The original complex Volterra transformation is bounded in the genuine uniform function norm.
Use: transformedWaveMap_analytic and the continuity of the original Green product integrals require this actual bounded operator, rather than separate pointwise analyticity assumptions.
Article: jacobi, Proposition C.2.
-/
def continuousTransformation (a : ℝ) (ha : -1<a) : C(Interval,ℂ) →L[ℂ] C(Interval,ℂ) :=
  LinearMap.mkContinuous
    { toFun := transformationWaveMap a ha
      map_add' W V := by
        ext t
        change W t+V t+coefficientFunctional _ (W+V)=_
        rw [map_add]
        change W t+V t+(coefficientFunctional _ W+coefficientFunctional _ V)=
          (W t+coefficientFunctional _ W)+(V t+coefficientFunctional _ V)
        ring
      map_smul' c W := by
        ext t
        change c*W t+coefficientFunctional _ (c • W)=c*(W t+coefficientFunctional _ W)
        rw [map_smul]
        change c*W t+c*coefficientFunctional _ W=_
        ring }
    (1+‖solutionRowMap a ha‖) (fun W => by
      -- The original L1 norm of each true GL row is controlled by its L2 norm and the common compact row bound.
      apply ((transformationWaveMap a ha W).norm_le (by positivity)).mpr
      intro t
      have hc := coefficient_integral_bound (solutionRow a ha (halfClamp t):Space) W
      have hL := space_L1_le_norm (solutionRow a ha (halfClamp t):Space)
      have hR := (solutionRowMap a ha).norm_coe_le_norm (halfClamp t)
      change ‖W t+coefficientFunctional _ W‖≤_
      exact (norm_add_le _ _).trans ((add_le_add (W.norm_coe_le_norm t)
        (hc.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg W)).trans
          (mul_le_mul_of_nonneg_right hR (norm_nonneg W))))).trans_eq (by ring)))

/-- The genuine transformed solution as a continuous complex wave on the common clamped physical domain.
Use: the characteristic-zero and simple-zero arguments use one entire continuous-function-valued u, with the original values unchanged.
Article: jacobi, Proposition C.2.
-/
def transformedWaveMap (a : ℝ) (ha : -1<a) (z : ℂ) : C(Interval,ℂ) :=
  continuousTransformation a ha (halfSolution a ha z)

/-- The uniformly defined transformed wave evaluates to the original constructed u at every physical coordinate.
Use: transfers the function-space energy regularity to the original Green integrals and characteristic derivatives.
Article: jacobi, Proposition C.2.
Proof: evaluation of the true bounded transformation gives the original reference value and the original inverse-row coefficient integral, which is precisely the already identified actual u. -/
theorem transformedWaveMap_apply (a : ℝ) (ha : -1<a) (z : ℂ) (t : Interval) :
    transformedWaveMap a ha z t=transformedSolution a ha (halfClamp t) z := by
  change halfSolution a ha z t+coefficientFunctional _ (halfSolution a ha z)=_
  rw [transformedSolution_reference_form,halfSolution_apply]
  rfl

/-- The original transformed solution is entire in energy in the uniform spatial norm.
Use: the simple characteristic-zero argument passes to the actual Green product integral as energy approaches a genuine spectral zero.
Article: jacobi, Proposition C.2.
Proof: compose the proved original reference function-space analyticity with the actual bounded complex-linear transformation. -/
theorem transformedWaveMap_analytic (a : ℝ) (ha : -1<a) (z : ℂ) :
    AnalyticAt ℂ (transformedWaveMap a ha) z :=
  ((continuousTransformation a ha).analyticAt _).comp (halfSolution_analytic a ha z)

/-- The original selected transformed solution is nonzero at some physical half-interval point at every complex energy.
Use: completeness excludes all additional separated characteristic zeros in Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: if u vanished identically, its proved normalized selected endpoint branch would give 1<=C*t arbitrarily close to the genuine left endpoint, contradicting C*t tending to zero. -/
theorem transformedSolution_not_identically_zero (a : ℝ) (ha : -1<a) (z : ℂ) :
    ∃ t:HalfInterval,transformedSolution a ha t z≠0 := by
  -- The one-sided half-interval filter is nontrivial since its actual midpoint lies strictly above zero.
  have : NeBot (𝓝[>] halfZero) :=
    nhdsGT_neBot_of_exists_gt ⟨⟨1/2,by norm_num⟩,by norm_num [halfZero]⟩
  obtain ⟨C,_,hC⟩ := transformedSolution_selected_branch a ha z
  have hlim : Tendsto (fun t:HalfInterval => C*(t:ℝ)) (𝓝[>] halfZero) (𝓝 0) := by
    have ht : Tendsto (fun t:HalfInterval => (t:ℝ)) (𝓝[>] halfZero) (𝓝 0) :=
      (continuous_subtype_val.continuousAt (x := halfZero)).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using ht.const_mul C
  by_contra h
  push Not at h
  have hf : ∀ᶠ t:HalfInterval in 𝓝[>] halfZero,(1:ℝ)≤C*(t:ℝ) := by
    filter_upwards [hC] with t ht
    simpa only [h t,zero_div,zero_sub,norm_neg,norm_one] using ht
  exact (not_le_of_gt (by norm_num : (0:ℝ)<1)) (ge_of_tendsto hlim hf)

end
end jacobi.GelfandLevitan
