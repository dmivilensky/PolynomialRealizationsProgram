import jacobi.GelfandLevitan.DiagonalSmoothness

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
On each fixed physical prefix, the actual original K row is
differentiable in its genuine uniform norm. This transfers the proved
actual pointwise derivative to bounded reference-solution integrals,
without differentiating the moving physical support projection.
Use: fixedTransformationRows_hasDerivWithinAt supplies their true uniform-norm derivative before the transformed-solution integral is differentiated.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformationKernel

/-- The actual original K rows on an independently fixed physical prefix, with their original real-parameter extension.
Use: fixedTransformationRows_hasDerivWithinAt supplies their true uniform-norm derivative before the transformed-solution integral is differentiated.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def fixedTransformationRows (a : ℝ) (ha : -1<a) (t : HalfInterval) : C(ℝ,C(Interval,ℝ)) :=
  ⟨fun x => ContinuousMap.compCLM ℝ ℝ (prefixClamp t)
      (transformationRows a ha (halfParameterClamp x)),
    (ContinuousMap.compCLM ℝ ℝ (prefixClamp t)).continuous.comp
      ((transformationRows a ha).continuous.comp halfParameterClamp.continuous)⟩

/-- The actual original t derivative rows on that same fixed physical prefix, extended only outside a chosen positive parameter strip.
Use: fixedTransformationRows_hasDerivWithinAt identifies this independently continuous uniform-norm curve with the derivative of the original K curve.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def fixedTransformationSlopeRows {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ))
    (t : HalfInterval) : C(ℝ,C(Interval,ℝ)) :=
  ⟨fun x => ContinuousMap.compCLM ℝ ℝ (prefixClamp t)
      (derivativeCandidateRows ha hd (positiveStripClamp hds (halfParameterClamp x))),
    (ContinuousMap.compCLM ℝ ℝ (prefixClamp t)).continuous.comp
      ((derivativeCandidateRows ha hd).continuous.comp
        ((positiveStripClamp hds).continuous.comp halfParameterClamp.continuous))⟩

/-- The actual original fixed-prefix K curve has its already identified original derivative in genuine spatial uniform norm.
Use: pairing with the original reference solution differentiates the actual fixed-prefix contribution to u, while the original moving tail is treated separately by its genuine shrinking average.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original K and actual derivative rows are independently continuous in uniform norm. At every spatial point of the fixed prefix the proved original t derivative applies throughout the entire parameter interval. The continuous-row Banach FTC gives the genuine row derivative. -/
theorem fixedTransformationRows_hasDerivWithinAt {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (t : HalfInterval) (hdt : d≤(t:ℝ)) {u : ℝ} (hu : u∈Icc (t:ℝ) (1/2)) :
    HasDerivWithinAt (fixedTransformationRows a ha t)
      (fixedTransformationSlopeRows ha hd (hdt.trans t.property.2) t u) (Icc (t:ℝ) (1/2)) u := by
  -- Spatial clipping fixes the original integration prefix and lies below every parameter in the interval where the actual pointwise K derivatives are used.
  have hds := hdt.trans t.property.2
  apply continuousRows_hasDerivWithinAt (fixedTransformationRows a ha t).continuous
    (fixedTransformationSlopeRows ha hd hds t).continuous hu
  intro x hx r
  let s := halfClamp (prefixClamp t r)
  have hs : (s:ℝ)≤(t:ℝ) := by
    change halfTime (prefixClamp t r)≤(t:ℝ)
    rw [prefixClamp_halfTime]
    exact min_le_right _ _
  have hp : x∈Icc (0:ℝ) (1/2) := ⟨(hd.trans_le (hdt.trans hx.1)).le,hx.2⟩
  have hcl : halfParameterClamp x=(⟨x,hp⟩:HalfInterval) := Set.projIcc_of_mem (by norm_num) hp
  have hdval : fixedTransformationSlopeRows ha hd hds t x r=
      derivativeCandidateRows ha hd ⟨x,⟨hdt.trans hx.1,hx.2⟩⟩ (halfInclusion s) := by
    change derivativeCandidateRows ha hd (positiveStripClamp hds (halfParameterClamp x)) (prefixClamp t r)=_
    rw [hcl,positiveStripClamp_of_mem hds ⟨x,hp⟩ (hdt.trans hx.1)]
    congr 1
    apply Subtype.ext
    change min (r:ℝ) (t:ℝ)=halfTime (prefixClamp t r)
    exact (prefixClamp_halfTime t r).symm
  rw [hdval]
  have h := transformationKernel_hasDerivWithinAt_first ha hd ⟨x,hp⟩ s (hdt.trans hx.1) (hs.trans hx.1)
  exact h.mono (Icc_subset_Icc (max_le hdt hs) le_rfl)

end
end jacobi.GelfandLevitan
