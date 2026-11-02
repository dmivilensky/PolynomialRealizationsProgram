import jacobi.GelfandLevitan.KernelFirstDerivative

/-!
Article: jacobi, Theorem 2.1.
The regularized original F-flat rows have their genuine derivatives
in spatial uniform norm on every closed positive strip. Pairing these
same actual rows with the true original inverse solution gives the
regularized part of the s derivative of K, without differentiating an
arbitrary L2 representative or assuming regularity of the Green kink.
Use: regularizedRows_hasDerivWithinAt identifies their true uniform-norm derivative, which can be paired with the original GL inverse rows in Differentiability of K (b).
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] regularizedKernel regularizedSlope

/-- The actual original F-flat rows on the physical half interval, continuously in their genuine uniform norm.
Use: regularizedRows_hasDerivWithinAt identifies their true uniform-norm derivative, which can be paired with the original GL inverse rows in Differentiability of K (b).
Article: jacobi, Theorem 2.1.
-/
def regularizedRows (a : ℝ) (ha : -1<a) : C(HalfInterval,C(Interval,ℝ)) :=
  (⟨fun p : HalfInterval × Interval => regularizedKernel a ha (p.1:ℝ) (halfTime p.2),
    (regularizedKernel_continuousOn ha).comp_continuous
      (g := fun p : ℝ × ℝ => regularizedKernel a ha p.1 p.2)
      (f := fun p : HalfInterval × Interval => ((p.1:ℝ),halfTime p.2))
      ((continuous_subtype_val.comp continuous_fst).prodMk (halfTime.continuous.comp continuous_snd))
      (fun p => ⟨p.1.property,halfTime_mem p.2⟩)⟩ : C(HalfInterval×Interval,ℝ)).curry

/-- The genuine original regularized derivative rows in their actual uniform function norm.
Use: the Banach FTC identifies these same independently continuous rows with the derivative of regularizedRows.
Article: jacobi, Theorem 2.1.
-/
def regularizedSlopeRows {a d : ℝ} (ha : -1<a) (hd : 0<d) : C(DerivativeStrip d,C(Interval,ℝ)) :=
  (⟨fun p : DerivativeStrip d × Interval => regularizedSlope a ha (p.1:ℝ) (halfTime p.2),
    (regularizedSlope_continuousOn ha hd).comp_continuous
      (g := fun p : ℝ × ℝ => regularizedSlope a ha p.1 p.2)
      (f := fun p : DerivativeStrip d × Interval => ((p.1:ℝ),halfTime p.2))
      ((continuous_subtype_val.comp continuous_fst).prodMk (halfTime.continuous.comp continuous_snd))
      (fun p => ⟨p.1.property,halfTime_mem p.2⟩)⟩ : C(DerivativeStrip d×Interval,ℝ)).curry

/-- The actual regularized row curve has the genuine uniformly convergent derivative row as its true Banach-space derivative on each entire required closed strip.
Use: differentiation after pairing with the original inverse GL row gives the regularized part of the genuine s derivative of K, including its midpoint left derivative.
Article: jacobi, Theorem 2.1.
Proof: use explicit constant extensions of both original curves from the closed strip. Their independently proved actual scalar derivatives agree with the original regularized derivative series at every spatial coordinate. The proved continuous-row Banach FTC identifies the uniform-norm derivative; the actual half-clamped row curve agrees with this extension on precisely the physical strip. -/
theorem regularizedRows_hasDerivWithinAt {a d s : ℝ} (ha : -1<a) (hd : 0<d)
    (hs : s∈Icc d (1/2)) :
    HasDerivWithinAt (fun x => regularizedRows a ha (halfParameterClamp x))
      (regularizedSlopeRows ha hd ⟨s,hs⟩) (Icc d (1/2)) s := by
  -- No original Green row is differentiated in uniform norm; this theorem concerns precisely the independently regularized kernel.
  have hds : d≤(1/2:ℝ) := hs.1.trans hs.2
  let P : C(ℝ,DerivativeStrip d) := ⟨Set.projIcc d (1/2) hds,continuous_projIcc⟩
  let f : C(ℝ,C(Interval,ℝ)) := (regularizedRows a ha).comp ((derivativeStripInclusion hd).comp P)
  let g : C(ℝ,C(Interval,ℝ)) := (regularizedSlopeRows ha hd).comp P
  have hf (x : ℝ) (hx : x∈Icc d (1/2)) (r : Interval) : f x r=regularizedKernel a ha x (halfTime r) := by
    change regularizedKernel a ha ((Set.projIcc d (1/2) hds x):ℝ) (halfTime r)=_
    rw [Set.projIcc_of_mem hds hx]
  have hg (x : ℝ) (hx : x∈Icc d (1/2)) (r : Interval) : g x r=regularizedSlope a ha x (halfTime r) := by
    change regularizedSlope a ha ((Set.projIcc d (1/2) hds x):ℝ) (halfTime r)=_
    rw [Set.projIcc_of_mem hds hx]
  have hder := continuousRows_hasDerivWithinAt f.continuous g.continuous hs (fun x hx r => by
    rw [hg x hx r]
    exact (regularizedKernel_hasDerivWithinAt ha hd hx (halfTime_mem r)).congr
      (fun y hy => hf y hy r) (hf x hx r))
  have hval : g s=regularizedSlopeRows ha hd ⟨s,hs⟩ := by
    change regularizedSlopeRows ha hd (Set.projIcc d (1/2) hds s)=_
    rw [Set.projIcc_of_mem hds hs]
  rw [hval] at hder
  apply hder.congr
  · intro x hx
    ext r
    rw [hf x hx r]
    change regularizedKernel a ha ((halfParameterClamp x):ℝ) (halfTime r)=_
    change regularizedKernel a ha ((Set.projIcc (0:ℝ) (1/2) (by norm_num) x):ℝ) (halfTime r)=_
    rw [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) ⟨(hd.trans_le hx.1).le,hx.2⟩]
  · ext r
    rw [hf s hs r]
    change regularizedKernel a ha ((Set.projIcc (0:ℝ) (1/2) (by norm_num) s):ℝ) (halfTime r)=_
    rw [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) ⟨(hd.trans_le hs.1).le,hs.2⟩]

/-- Pairing any actual original L2 input with a genuine continuous spatial row, as its true bounded linear functional.
Use: regularizedPairing_hasDerivWithinAt differentiates the original regularized K reconstruction integral through this actual fixed continuous linear map.
Article: jacobi, Proposition C.3.
Source: the community Hilbert inner-product continuous linear map and original continuous-function-to-L2 embedding. -/
def spatialRowPairing (v : Space) : C(Interval,ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ v) ∘L ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume

/-- The original continuous-row pairing is exactly the genuine spatial integral against its original L2 input.
Use: the derivative of the actual regularized GL row pairing is identified with the original differentiated spatial integral, without selecting pointwise values of an arbitrary L2 class.
Article: jacobi, Theorem 2.1.
Proof: the true L2 inner product is its original integral. Replace only the continuous row vector by its genuine almost-everywhere continuous representative and use real scalar commutativity. -/
theorem spatialRowPairing_apply (v : Space) (g : C(Interval,ℝ)) : spatialRowPairing v g=∫ r : Interval,v r*g r := by
  change inner ℝ v (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume g)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume g] with r hr
  rw [hr]
  change g r*v r=v r*g r
  ring

/-- The actual original regularized K reconstruction pairing has its genuine derivative on every required closed spatial strip.
Use: the Green action is treated separately with its correct diagonal branch, and adding the two original parts gives the actual s derivative in Differentiability of K (b).
Article: jacobi, Theorem 2.1.
Proof: compose the independently proved actual regularized uniform-row derivative with the true original continuous L2 pairing functional. -/
theorem regularizedPairing_hasDerivWithinAt {a d s : ℝ} (ha : -1<a) (hd : 0<d)
    (hs : s∈Icc d (1/2)) (v : Space) :
    HasDerivWithinAt (fun x => spatialRowPairing v (regularizedRows a ha (halfParameterClamp x)))
      (spatialRowPairing v (regularizedSlopeRows ha hd ⟨s,hs⟩)) (Icc d (1/2)) s :=
  (spatialRowPairing v).hasFDerivAt.comp_hasDerivWithinAt s (regularizedRows_hasDerivWithinAt ha hd hs)

end
end jacobi.GelfandLevitan
