import jacobi.GelfandLevitan.KernelDifferenceQuotient

/-!
Article: jacobi, Theorem 2.1.
The true original K difference-quotient forcing converges in the
actual spatial uniform norm on its fixed physical prefix to the
original differentiated forcing dot F+w*F. Both the original F slope
and the parameter-dependent moving-tail average are controlled without
assuming any derivative of K.
Use: actual moving-tail averages tend to the same original physical diagonal as the genuine F difference quotient.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel kernelSlope transformationKernel

/-- The actual physical parameter on the fixed-prefix nonsingular strip, with its explicit continuous constant real extension.
Use: actual moving-tail averages tend to the same original physical diagonal as the genuine F difference quotient.
Article: jacobi, Theorem 2.1.
-/
def prefixPhysicalParameter (t : HalfInterval) (ht : 0<(t:ℝ)) : C(ℝ,HalfInterval) :=
  (derivativeStripInclusion ht).comp (prefixParameterClamp t)

/-- The original fixed physical endpoint is unchanged by its explicit parameter extension.
Use: the actual shrinking moving-tail average has exactly its original diagonal limit K(t,t)*F(t,.).
Article: jacobi, Theorem 2.1.
Proof: the original parameter is the left endpoint of its own physical clipping interval. -/
theorem prefixPhysicalParameter_self (t : HalfInterval) (ht : 0<(t:ℝ)) : prefixPhysicalParameter t ht (t:ℝ)=t := by
  apply Subtype.ext
  change ((Set.projIcc (t:ℝ) (1/2) t.property.2 (t:ℝ)):ℝ)=(t:ℝ)
  rw [Set.projIcc_left]

/-- On the original nonsingular physical strip, parameter extension retains precisely the original real coordinate.
Use: quotientForcingCurve_eq identifies the Banach-valued limit curve with the literal forcing of the actual original K quotient equation.
Article: jacobi, Theorem 2.1.
Proof: clipping fixes every original point in its closed physical strip. -/
theorem prefixPhysicalParameter_val (t : HalfInterval) (ht : 0<(t:ℝ)) {u : ℝ}
    (hu : u∈Icc (t:ℝ) (1/2)) : ((prefixPhysicalParameter t ht u):ℝ)=u := by
  change ((Set.projIcc (t:ℝ) (1/2) t.property.2 u):ℝ)=u
  rw [Set.projIcc_of_mem t.property.2 hu]

/-- The true original difference-quotient forcing as a real parameter curve in the fixed spatial uniform-norm space.
Use: quotientForcingCurve_tendsto proves its actual one-sided limit; quotientForcingCurve_eq identifies every physical nondegenerate value with the original K quotient forcing.
Article: jacobi, Theorem 2.1.
-/
def quotientForcingCurve (a : ℝ) (ha : -1<a) (t : HalfInterval) (ht : 0<(t:ℝ)) (u : ℝ) : C(Interval,ℝ) :=
  slope (prefixKernelRows a ha t ht) (t:ℝ) u+
    ContinuousMap.compCLM ℝ ℝ (prefixClamp t)
      (affineAverage (glTailIntegrand a ha) t (prefixPhysicalParameter t ht u))

/-- Every actual physical value of the uniform-norm forcing curve is exactly the original clipped K difference-quotient forcing.
Use: kernel_hasDerivWithinAt_right passes the proved genuine forcing limit through the independently proved exact inverse identity for actual K quotients.
Article: jacobi, Theorem 2.1.
Proof: the extended original F curve is the fixed-prefix restriction of the same actual source rows. The actual endpoint coordinate is unchanged on the physical strip; precomposition is a genuine linear map and commutes with the two original differences and scalar actions. -/
theorem quotientForcingCurve_eq {a : ℝ} (ha : -1<a) (t : HalfInterval) (ht : 0<(t:ℝ))
    {u : ℝ} (hu : u∈Icc (t:ℝ) (1/2)) :
    quotientForcingCurve a ha t ht u=
      (kernelQuotientForcing a ha t (prefixPhysicalParameter t ht u)).comp (prefixClamp t) := by
  -- Both sides contain the original same F quotient and the same genuine moving-tail average.
  have hrow (x : ℝ) : prefixKernelRows a ha t ht x=
      (kernelRows a ha (prefixPhysicalParameter t ht x)).comp (prefixClamp t) := rfl
  unfold quotientForcingCurve kernelQuotientForcing
  rw [slope_def_module,hrow u,hrow (t:ℝ),prefixPhysicalParameter_self]
  ext r
  change (u-(t:ℝ))⁻¹*(kernelRows a ha (prefixPhysicalParameter t ht u) (prefixClamp t r)-
      kernelRows a ha t (prefixClamp t r))+
    affineAverage (glTailIntegrand a ha) t (prefixPhysicalParameter t ht u) (prefixClamp t r)=
    (((prefixPhysicalParameter t ht u):ℝ)-(t:ℝ))⁻¹*
      (kernelRows a ha (prefixPhysicalParameter t ht u) (prefixClamp t r)-kernelRows a ha t (prefixClamp t r))+
    affineAverage (glTailIntegrand a ha) t (prefixPhysicalParameter t ht u) (prefixClamp t r)
  rw [prefixPhysicalParameter_val t ht hu]

/-- The original uniform-norm forcing limit is exactly the original dot F+w*F restricted to the same fixed physical prefix.
Use: quotientForcingCurve_tendsto identifies its independently proved two limiting summands with the exact actual forcing used to construct derivativeCandidateRows.
Article: jacobi, Theorem 2.1.
Proof: evaluate the proved original F derivative row and the true diagonal tail integrand, then evaluate the original differentiated forcing at the same clipped physical coordinate. -/
theorem quotientForcing_limit_value {a d : ℝ} (ha : -1<a) (hd : 0<d) (t : HalfInterval)
    (ht : 0<(t:ℝ)) (hdt : d≤(t:ℝ)) :
    prefixSlopeRows ha t ht (t:ℝ)+ContinuousMap.compCLM ℝ ℝ (prefixClamp t) (glTailIntegrand a ha (t,t))=
      (derivativeForcingRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩).comp (prefixClamp t) := by
  ext r
  change prefixSlopeRows ha t ht (t:ℝ) r+glTailIntegrand a ha (t,t) (prefixClamp t r)=_
  rw [prefixSlopeRows_apply ha t ht ⟨le_rfl,t.property.2⟩,glTailIntegrand_apply]
  change _=derivativeForcingRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩ (prefixClamp t r)
  rw [derivativeForcingRows_apply,prefixClamp_halfTime]
  rfl

/-- The actual original K quotient forcing converges in genuine spatial uniform norm to the original differentiated forcing on every fixed positive physical prefix below the midpoint.
Use: applying the already proved original uniform-norm inverse reconstruction continuity identifies the actual original K right derivative, with no derivative or convergence premise supplied by the caller.
Article: jacobi, Theorem 2.1.
Proof: the original F row has the independently proved genuine Banach derivative on the fixed-prefix strip. The original moving-tail average tends in that same norm to its independently evaluated diagonal. Add the two true limits and use the exact original forcing identity. -/
theorem quotientForcingCurve_tendsto {a d : ℝ} (ha : -1<a) (hd : 0<d) (t : HalfInterval)
    (ht : 0<(t:ℝ)) (hdt : d≤(t:ℝ)) (htop : (t:ℝ)<1/2) :
    Tendsto (quotientForcingCurve a ha t ht) (𝓝[>] (t:ℝ))
      (𝓝 ((derivativeForcingRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩).comp (prefixClamp t))) := by
  -- Each limiting summand is proved for the genuine original functions before their sum is identified as the true differentiated forcing.
  have hF := (prefixKernelRows_hasDerivWithinAt ha t ht ⟨le_rfl,t.property.2⟩).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE htop)
  have hFlim := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (t:ℝ))).mp hF.Ioi_of_Ici
  have hparam : Tendsto (prefixPhysicalParameter t ht) (𝓝[>] (t:ℝ)) (𝓝 t) := by
    simpa only [prefixPhysicalParameter_self] using
      ((prefixPhysicalParameter t ht).continuous.continuousAt.tendsto (x := (t:ℝ))).mono_left nhdsWithin_le_nhds
  have havg := (affineAverage_tendsto (glTailIntegrand a ha) t).comp hparam
  have htail := (ContinuousMap.compCLM ℝ ℝ (prefixClamp t)).continuous.continuousAt.tendsto.comp havg
  change Tendsto (fun x => slope (prefixKernelRows a ha t ht) (t:ℝ) x+
    ContinuousMap.compCLM ℝ ℝ (prefixClamp t)
      (affineAverage (glTailIntegrand a ha) t (prefixPhysicalParameter t ht x))) _ _
  rw [← quotientForcing_limit_value ha hd t ht hdt]
  exact hFlim.add htail

end
end jacobi.GelfandLevitan
