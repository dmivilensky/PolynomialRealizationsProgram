import jacobi.GelfandLevitan.SecondDerivativeContinuity

/-!
Article: jacobi, Theorem 2.1.
The actual spatial increment of the original K is the integral of its
proved second-coordinate derivative. Its genuine shrinking-segment
average has the true continuous diagonal limit. This is the spatial
term in differentiating the original diagonal w(t)=K(t,t).
Use: positiveSecondDerivative extends the actual continuous spatial derivative only below that strip, allowing genuine compact-domain shrinking averages.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformationKernel

/-- Continuous clipping of the original half interval to a fixed positive physical strip.
Use: positiveSecondDerivative extends the actual continuous spatial derivative only below that strip, allowing genuine compact-domain shrinking averages.
Article: jacobi, Theorem 2.1.
-/
def positiveStripClamp {d : ℝ} (hds : d≤(1/2:ℝ)) : C(HalfInterval,DerivativeStrip d) :=
  ⟨fun t => Set.projIcc d (1/2) hds (t:ℝ),continuous_projIcc.comp continuous_subtype_val⟩

/-- Positive clipping preserves every original physical point in its required strip.
Use: the spatial derivative extension and its physical shrinking integral agree with the actual original derivative on the entire interval being integrated.
Article: jacobi, Theorem 2.1.
Proof: apply the community projection identity to the original physical strip membership. -/
theorem positiveStripClamp_of_mem {d : ℝ} (hds : d≤(1/2:ℝ)) (t : HalfInterval) (ht : d≤(t:ℝ)) :
    positiveStripClamp hds t=(⟨(t:ℝ),⟨ht,t.property.2⟩⟩:DerivativeStrip d) :=
  Set.projIcc_of_mem hds ⟨ht,t.property.2⟩

/-- The actual continuous spatial derivative, extended from its positive physical square by explicit clipping.
Use: affineAverage_tendsto gives the exact limit of the spatial term in the original K diagonal difference quotient; spatialIncrement_integral identifies the actual original increment.
Article: jacobi, Theorem 2.1.
-/
def positiveSecondDerivative {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ)) :
    C(HalfInterval×HalfInterval,ℝ) :=
  (secondDerivativeMap ha hd hds).comp
    ⟨fun p => (positiveStripClamp hds p.1,positiveStripClamp hds p.2),
      ((positiveStripClamp hds).continuous.comp continuous_fst).prodMk
        ((positiveStripClamp hds).continuous.comp continuous_snd)⟩

/-- The continuous extension of the actual spatial derivative has exactly the original derivative values at every physical point of its positive strip.
Use: spatialIncrement_integral integrates the independently proved original K derivative, without adding any new derivative premise.
Article: jacobi, Theorem 2.1.
Proof: both positive clippings fix their original physical inputs, and the unchanged first-coordinate strip inclusion is the original physical point. -/
theorem positiveSecondDerivative_apply {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ))
    (u s : HalfInterval) (hu : d≤(u:ℝ)) (hs : d≤(s:ℝ)) :
    positiveSecondDerivative ha hd hds (u,s)=secondDerivativeValue ha hd hds u ⟨(s:ℝ),⟨hs,s.property.2⟩⟩ := by
  change secondDerivativeValue ha hd hds (derivativeStripInclusion hd (positiveStripClamp hds u))
    (positiveStripClamp hds s)=_
  rw [positiveStripClamp_of_mem hds u hu,positiveStripClamp_of_mem hds s hs]
  rfl

/-- Every original spatial K increment in the positive physical triangle is exactly the integral of its independently proved actual spatial derivative.
Use: spatialIncrement_average turns the genuine spatial term of the original diagonal quotient into a continuous shrinking average.
Article: jacobi, Theorem 2.1.
Source: mathlib's interval fundamental theorem of calculus.
Proof: the original K slice is continuous. At every interior point of this true physical segment its proved within-strip derivative is an ordinary derivative, since the point is interior to that strip. Integrate this same genuine continuous derivative and use the exact physical endpoint values. -/
theorem spatialIncrement_integral {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ))
    (t u : HalfInterval) (ht : d≤(t:ℝ)) (htu : (t:ℝ)≤u) :
    (∫ r in (t:ℝ)..(u:ℝ),positiveSecondDerivative ha hd hds (u,halfParameterClamp r))=
      transformationKernel a ha u u-transformationKernel a ha u t := by
  -- The FTC uses the actual slice derivatives of the original K, not a separately chosen derivative candidate.
  have hf : Continuous (fun r : ℝ => transformationKernel a ha u (halfParameterClamp r)) :=
    (transformationKernel_continuous a ha).comp (continuous_const.prodMk halfParameterClamp.continuous)
  have hg : Continuous (fun r : ℝ => positiveSecondDerivative ha hd hds (u,halfParameterClamp r)) :=
    (positiveSecondDerivative ha hd hds).continuous.comp (continuous_const.prodMk halfParameterClamp.continuous)
  have hder (r : ℝ) (hr : r∈Ioo (t:ℝ) (u:ℝ)) :
      HasDerivAt (fun x : ℝ => transformationKernel a ha u (halfParameterClamp x))
        (positiveSecondDerivative ha hd hds (u,halfParameterClamp r)) r := by
    have hp : r∈Icc (0:ℝ) (1/2) := ⟨t.property.1.trans hr.1.le,hr.2.le.trans u.property.2⟩
    have he : halfParameterClamp r=(⟨r,hp⟩:HalfInterval) := Set.projIcc_of_mem (by norm_num) hp
    rw [he,positiveSecondDerivative_apply ha hd hds u ⟨r,hp⟩ (ht.trans htu) (ht.trans hr.1.le)]
    exact (transformationKernel_hasDerivWithinAt_second ha hd u ⟨r,hp⟩ (ht.trans hr.1.le) hr.2.le).hasDerivAt
      (Icc_mem_nhds (ht.trans_lt hr.1) hr.2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htu hf.continuousOn hder
    (hg.intervalIntegrable (μ := volume) (t:ℝ) (u:ℝ))
  rw [show halfParameterClamp (u:ℝ)=u from Set.projIcc_of_mem (by norm_num) u.property,
    show halfParameterClamp (t:ℝ)=t from Set.projIcc_of_mem (by norm_num) t.property] at h
  exact h

/-- The actual normalized original spatial increment is its genuine continuous shrinking-segment average.
Use: the original diagonal quotient has the true spatial derivative as its limit by affineAverage_tendsto, with no diagonal derivative assumption.
Article: jacobi, Theorem 2.1.
Proof: combine the proved physical affine substitution with the genuine spatial FTC identity for the original K. -/
theorem spatialIncrement_average {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ))
    (t u : HalfInterval) (ht : d≤(t:ℝ)) (htu : (t:ℝ)≤u) (hne : u≠t) :
    affineAverage (positiveSecondDerivative ha hd hds) t u=
      ((u:ℝ)-(t:ℝ))⁻¹*(transformationKernel a ha u u-transformationKernel a ha u t) := by
  rw [affineAverage_integral _ _ _ hne,spatialIncrement_integral ha hd hds t u ht htu,smul_eq_mul]

end
end jacobi.GelfandLevitan
