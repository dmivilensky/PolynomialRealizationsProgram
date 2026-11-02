import jacobi.GelfandLevitan.ContinuousRowsDerivative

/-!
Article: jacobi, Theorem 2.1.
For a fixed physical prefix [0,t], the actual rows F(x,.) have the
genuine uniform-norm derivative dot F(x,.) for t<=x<=1/2. Clipping
only the unused spatial tail embeds this fixed prefix in the existing
continuous-function space. The moving physical cutoff is never differentiated.
Use: original GL row difference quotients are tested uniformly on exactly [0,t], while the unused spatial tail is continuously copied from t.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel kernelSlope

/-- Continuous clipping to an actual fixed physical prefix, retaining the original unit-domain function space.
Use: original GL row difference quotients are tested uniformly on exactly [0,t], while the unused spatial tail is continuously copied from t.
Article: jacobi, Theorem 2.1.
-/
def prefixClamp (t : HalfInterval) : C(Interval,Interval) :=
  ⟨fun r => ⟨min (r:ℝ) (t:ℝ),⟨le_min r.property.1 t.property.1,
      (min_le_left _ _).trans r.property.2⟩⟩,
    (continuous_subtype_val.min continuous_const).subtype_mk _⟩

/-- Fixed-prefix clipping preserves every original point of that physical prefix.
Use: the clipped true difference-quotient forcing is unchanged on the original equation domain, so the original forced inverse applies to precisely the same physical data.
Article: jacobi, Theorem 2.1.
Proof: min(r,t)=r for every actual original r<=t; subtype extensionality keeps the same coordinate. -/
theorem prefixClamp_fix (t : HalfInterval) (r : Interval) (hr : (r:ℝ)≤(t:ℝ)) : prefixClamp t r=r :=
  Subtype.ext (min_eq_left hr)

/-- Clipping to an actual physical prefix already lies in the physical half interval.
Use: evaluates original kernel and derivative rows on the unchanged prefix coordinate, removing the earlier half clamp without altering any original point.
Article: jacobi, Theorem 2.1.
Proof: min(r,t)<=t<=1/2, so the existing half-coordinate minimum is the prefix coordinate itself. -/
theorem prefixClamp_halfTime (t : HalfInterval) (r : Interval) :
    halfTime (prefixClamp t r)=min (r:ℝ) (t:ℝ) := by
  change min (min (r:ℝ) (t:ℝ)) (1/2)=_
  exact min_eq_left ((min_le_right _ _).trans t.property.2)

/-- The genuine original F rows restricted to a fixed actual prefix, continuously in the nonsingular physical parameter strip.
Use: prefixKernelRows extends this same uniform-norm curve by constant parameter clipping to apply the closed-interval Banach FTC.
Article: jacobi, Theorem 2.1.
-/
def prefixKernelStripRows (a : ℝ) (ha : -1<a) (t : HalfInterval) (ht : 0<(t:ℝ)) :
    C(DerivativeStrip (t:ℝ),C(Interval,ℝ)) :=
  ⟨fun u => ContinuousMap.compCLM ℝ ℝ (prefixClamp t)
      (kernelRows a ha (derivativeStripInclusion ht u)),
    (ContinuousMap.compCLM ℝ ℝ (prefixClamp t)).continuous.comp
      ((kernelRows a ha).continuous.comp (derivativeStripInclusion ht).continuous)⟩

/-- The genuine original dot F rows restricted to exactly the same fixed actual prefix.
Use: these continuous uniform-norm rows are identified as the actual derivatives of prefixKernelRows, so their value at the fixed endpoint is the true F difference-quotient limit.
Article: jacobi, Theorem 2.1.
-/
def prefixSlopeStripRows {a : ℝ} (ha : -1<a) (t : HalfInterval) (ht : 0<(t:ℝ)) :
    C(DerivativeStrip (t:ℝ),C(Interval,ℝ)) :=
  ⟨fun u => ContinuousMap.compCLM ℝ ℝ (prefixClamp t) (kernelSlopeRows ha ht u),
    (ContinuousMap.compCLM ℝ ℝ (prefixClamp t)).continuous.comp (kernelSlopeRows ha ht).continuous⟩

/-- Constant clipping of a real parameter to the actual closed positive physical strip.
Use: the original F and dot F curves receive continuous whole-real-line extensions solely to invoke the community Banach FTC; on the required strip this map is the identity.
Article: jacobi, Theorem 2.1.
-/
def prefixParameterClamp (t : HalfInterval) : C(ℝ,DerivativeStrip (t:ℝ)) :=
  ⟨Set.projIcc (t:ℝ) (1/2) t.property.2,continuous_projIcc⟩

/-- The actual fixed-prefix F row curve with its explicit constant parameter extension.
Use: prefixKernelRows_hasDerivWithinAt proves a genuine derivative in the original spatial uniform norm, which supplies the first term of the GL difference-quotient forcing limit.
Article: jacobi, Theorem 2.1.
-/
def prefixKernelRows (a : ℝ) (ha : -1<a) (t : HalfInterval) (ht : 0<(t:ℝ)) : C(ℝ,C(Interval,ℝ)) :=
  (prefixKernelStripRows a ha t ht).comp (prefixParameterClamp t)

/-- The actual fixed-prefix dot F row curve with the same explicit constant parameter extension.
Use: its actual endpoint value is the independently constructed uniform-norm derivative of prefixKernelRows.
Article: jacobi, Theorem 2.1.
-/
def prefixSlopeRows {a : ℝ} (ha : -1<a) (t : HalfInterval) (ht : 0<(t:ℝ)) : C(ℝ,C(Interval,ℝ)) :=
  (prefixSlopeStripRows ha t ht).comp (prefixParameterClamp t)

/-- The actual extended fixed-prefix F rows retain every original physical value on their required parameter strip.
Use: proves their pointwise derivatives by the already proved original kernel derivative, without assuming a derivative in uniform norm.
Article: jacobi, Theorem 2.1.
Proof: parameter clipping fixes every point in the physical strip, and the earlier exact prefix-clamp identity removes the unused spatial half clamp. -/
theorem prefixKernelRows_apply {a : ℝ} (ha : -1<a) (t : HalfInterval) (ht : 0<(t:ℝ))
    {u : ℝ} (hu : u∈Icc (t:ℝ) (1/2)) (r : Interval) :
    prefixKernelRows a ha t ht u r=kernel a ha u (min (r:ℝ) (t:ℝ)) := by
  change kernelRows a ha (derivativeStripInclusion ht (Set.projIcc (t:ℝ) (1/2) t.property.2 u)) (prefixClamp t r)=_
  rw [Set.projIcc_of_mem t.property.2 hu,kernelRows_apply,prefixClamp_halfTime]
  rfl

/-- The actual extended derivative rows retain precisely the original dot F values on the same physical strip.
Use: the Banach-space derivative theorem uses the same original dot F as the original differentiated GL forcing.
Article: jacobi, Theorem 2.1.
Proof: constant parameter clipping fixes the required physical strip, and fixed spatial clipping lies inside the original half interval. -/
theorem prefixSlopeRows_apply {a : ℝ} (ha : -1<a) (t : HalfInterval) (ht : 0<(t:ℝ))
    {u : ℝ} (hu : u∈Icc (t:ℝ) (1/2)) (r : Interval) :
    prefixSlopeRows ha t ht u r=kernelSlope a ha u (min (r:ℝ) (t:ℝ)) := by
  change kernelSlope a ha ((Set.projIcc (t:ℝ) (1/2) t.property.2 u):ℝ) (halfTime (prefixClamp t r))=_
  rw [Set.projIcc_of_mem t.property.2 hu,prefixClamp_halfTime]

/-- The actual original F rows on a fixed physical prefix have the original dot F rows as their true derivative in spatial uniform norm.
Use: gives the genuine uniform difference-quotient limit in Differentiability of K (a); the subsequent original inverse continuity transfers that limit to the actual K difference quotients.
Article: jacobi, Theorem 2.1.
Proof: both original clipped row curves are independently continuous in uniform norm. Their pointwise derivatives are the already proved actual kernel derivatives on the same original closed strip. Apply continuousRows_hasDerivWithinAt, whose Banach FTC proof upgrades these true pointwise identities to a genuine uniform-norm derivative. -/
theorem prefixKernelRows_hasDerivWithinAt {a : ℝ} (ha : -1<a) (t : HalfInterval) (ht : 0<(t:ℝ))
    {u : ℝ} (hu : u∈Icc (t:ℝ) (1/2)) :
    HasDerivWithinAt (prefixKernelRows a ha t ht) (prefixSlopeRows ha t ht u) (Icc (t:ℝ) (1/2)) u := by
  -- A fixed spatial prefix lies below every parameter in this actual physical strip, including its lower endpoint.
  apply continuousRows_hasDerivWithinAt (prefixKernelRows a ha t ht).continuous (prefixSlopeRows ha t ht).continuous hu
  intro x hx r
  rw [prefixSlopeRows_apply ha t ht hx]
  have hm : max (t:ℝ) (min (r:ℝ) (t:ℝ))=(t:ℝ) := max_eq_left (min_le_right _ _)
  have hd := kernel_hasDerivWithinAt ha ht
    (show x∈Icc (max (t:ℝ) (min (r:ℝ) (t:ℝ))) (1/2) by rw [hm]; exact hx)
    (le_min r.property.1 t.property.1)
  rw [hm] at hd
  exact hd.congr (fun y hy => prefixKernelRows_apply ha t ht hy r) (prefixKernelRows_apply ha t ht hx r)

end
end jacobi.GelfandLevitan
