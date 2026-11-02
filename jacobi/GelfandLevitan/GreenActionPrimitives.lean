import jacobi.GelfandLevitan.RegularizedRowsDerivative

/-!
Article: jacobi, Theorem 2.1.
The selected-solution Green action is differentiated through its two
actual physical primitives. Positive-strip clipping supplies continuous
extensions only outside the genuine integration intervals. The two
moving-boundary terms cancel exactly, retaining the original diagonal kink.
Use: the left original Green primitive has a globally continuous integrand, with every physical value including zero preserved exactly.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope transformationKernel

/-- The original zero-energy selected solution, continuously extended from its actual physical half interval.
Use: the left original Green primitive has a globally continuous integrand, with every physical value including zero preserved exactly.
Article: jacobi, Theorem 2.1.
-/
def leftZeroWeight (a : ℝ) (ha : -1<a) : C(ℝ,ℝ) :=
  (⟨fun r : HalfInterval => realSolution a (jacobi.Jacobi.endpointCorrection a) (r:ℝ),
    continuous_iff_continuousAt.mpr (fun r => (realSolution_continuousAt ha _ r.property).comp_of_eq
      continuous_subtype_val.continuousAt rfl)⟩ : C(HalfInterval,ℝ)).comp halfParameterClamp

/-- The original reflected selected solution on a positive half strip, with a continuous whole-real-line extension.
Use: the right original Green primitive never integrates through the opposite singular endpoint, and its actual spatial intervals retain their original selected-solution values.
Article: jacobi, Theorem 2.1.
-/
def rightZeroWeight (a : ℝ) (_ha : -1<a) {d : ℝ} (hd : 0<d) (hds : d≤(1/2:ℝ)) : C(ℝ,ℝ) :=
  let hhalf : d/2≤(1/2:ℝ) := by linarith
  let R : C(DerivativeStrip (d/2),ℝ) :=
    ⟨fun r => realSolution a (jacobi.Jacobi.endpointCorrection a) (1-(r:ℝ)),by
      apply continuous_iff_continuousAt.mpr
      intro r
      have hr : 1-(r:ℝ)∈Ioo (0:ℝ) 1 := ⟨by linarith [r.property.2],by linarith [r.property.1]⟩
      exact (realSolution_hasDerivAt a _ hr).continuousAt.comp_of_eq
        (continuousAt_const.sub continuous_subtype_val.continuousAt) rfl⟩
  R.comp ⟨Set.projIcc (d/2) (1/2) hhalf,continuous_projIcc⟩

/-- The extended left zero-energy weight retains precisely its original physical values.
Use: identifies the original physical left Green integral with its genuine continuous primitive.
Article: jacobi, Theorem 2.1.
Proof: real half-interval clipping fixes the original physical point. -/
theorem leftZeroWeight_value {a x : ℝ} (ha : -1<a) (hx : x∈Icc (0:ℝ) (1/2)) :
    leftZeroWeight a ha x=realSolution a (jacobi.Jacobi.endpointCorrection a) x := by
  change realSolution a _ ((Set.projIcc (0:ℝ) (1/2) (by norm_num) x):ℝ)=_
  rw [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) hx]

/-- The extended right zero-energy weight retains precisely its original values on the required positive physical strip.
Use: the right genuine Green integral is its continuous primitive with the original singular endpoint excluded analytically.
Article: jacobi, Theorem 2.1.
Proof: the continuous extension clips only below d/2 or above the midpoint, so every original x>=d is fixed. -/
theorem rightZeroWeight_value {a d x : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ))
    (hx : x∈Icc d (1/2)) : rightZeroWeight a ha hd hds x=realSolution a (jacobi.Jacobi.endpointCorrection a) (1-x) := by
  change realSolution a _ (1-((Set.projIcc (d/2) (1/2) (by linarith) x):ℝ))=_
  rw [Set.projIcc_of_mem (by linarith : d/2≤(1/2:ℝ)) ⟨by linarith [hx.1],hx.2⟩]

/-- The actual original K times a genuine continuous selected weight, in the original real integration coordinate.
Use: its two physical primitives give the exact original Green action and its genuine spatial derivative.
Article: jacobi, Theorem 2.1.
-/
def weightedKernelIntegrand (a : ℝ) (ha : -1<a) (w : C(ℝ,ℝ)) : C(HalfInterval×ℝ,ℝ) :=
  ⟨fun p => transformationKernel a ha p.1 (halfParameterClamp p.2)*w p.2,
    ((transformationKernel_continuous a ha).comp
      (continuous_fst.prodMk (halfParameterClamp.continuous.comp continuous_snd))).mul
      (w.continuous.comp continuous_snd)⟩

/-- The actual original weighted prefix integral with independently varying kernel parameter and physical integration endpoint.
Use: the selected left/right Green action formula has genuine jointly continuous primitive data; their actual first derivatives need only continuity of the original K.
Article: jacobi, Theorem 2.1.
-/
def weightedKernelPrimitive (a : ℝ) (ha : -1<a) (w : C(ℝ,ℝ)) : C(HalfInterval×ℝ,ℝ) :=
  ⟨fun p => ∫ r in (0:ℝ)..p.2,weightedKernelIntegrand a ha w (p.1,r),
    intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume)
      (f := fun t r => weightedKernelIntegrand a ha w (t,r)) (weightedKernelIntegrand a ha w).continuous⟩

/-- The actual weighted original K primitive has its genuine endpoint derivative throughout the real parameter extension.
Use: differentiating the true selected Green action cancels the original two moving-boundary terms exactly, without any derivative assumption on K.
Article: jacobi, Theorem 2.1.
Proof: the fixed genuine weighted original K integrand is globally continuous; apply the community endpoint FTC with its actual interval integrability and measurability. -/
theorem weightedKernelPrimitive_hasDerivAt (a : ℝ) (ha : -1<a) (w : C(ℝ,ℝ)) (t : HalfInterval) (s : ℝ) :
    HasDerivAt (fun x => weightedKernelPrimitive a ha w (t,x))
      (transformationKernel a ha t (halfParameterClamp s)*w s) s := by
  have hc : Continuous (fun r : ℝ => weightedKernelIntegrand a ha w (t,r)) :=
    (weightedKernelIntegrand a ha w).continuous.comp (continuous_const.prodMk continuous_id)
  change HasDerivAt (fun x => ∫ r in (0:ℝ)..x,weightedKernelIntegrand a ha w (t,r))
    (weightedKernelIntegrand a ha w (t,s)) s
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (μ := volume) (0:ℝ) s)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The original left physical Green primitive with its genuine continuous parameter dependence.
Use: greenActionFormula and greenActionSlope retain the exact original integral from zero to the moving spatial point.
Article: jacobi, Theorem 2.1.
-/
def leftGreenPrimitive (a : ℝ) (ha : -1<a) : C(HalfInterval×ℝ,ℝ) :=
  weightedKernelPrimitive a ha (leftZeroWeight a ha)

/-- The original right physical Green primitive, formed as the exact difference of its two continuous original prefixes.
Use: greenActionFormula and greenActionSlope use the same integral from s to t, with its correct negative lower-endpoint derivative.
Article: jacobi, Theorem 2.1.
-/
def rightGreenPrimitive (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) (hds : d≤(1/2:ℝ)) : C(HalfInterval×ℝ,ℝ) :=
  let P := weightedKernelPrimitive a ha (rightZeroWeight a ha hd hds)
  ⟨fun p => P (p.1,(p.1:ℝ))-P p,
    (P.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_fst))).sub P.continuous⟩

/-- The continuous right original Green primitive is exactly its genuine physical interval integral.
Use: Green-action identification splits the actual original Green integral at s, retaining both original endpoint contributions.
Article: jacobi, Theorem 2.1.
Proof: additivity of the genuine globally continuous weighted original interval integrand subtracts its two true prefix integrals. -/
theorem rightGreenPrimitive_integral (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) (hds : d≤(1/2:ℝ))
    (t : HalfInterval) (s : ℝ) :
    rightGreenPrimitive a ha hd hds (t,s)=
      ∫ r in s..(t:ℝ),weightedKernelIntegrand a ha (rightZeroWeight a ha hd hds) (t,r) := by
  have hc : Continuous (fun r : ℝ => weightedKernelIntegrand a ha (rightZeroWeight a ha hd hds) (t,r)) :=
    (weightedKernelIntegrand a ha _).continuous.comp (continuous_const.prodMk continuous_id)
  change (∫ r in (0:ℝ)..(t:ℝ),weightedKernelIntegrand a ha _ (t,r))-
    (∫ r in (0:ℝ)..s,weightedKernelIntegrand a ha _ (t,r))=_
  exact (eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (0:ℝ) s) (hc.intervalIntegrable (μ := volume) s (t:ℝ)))).symm

/-- The selected-solution formula for the original weighted Green action, with its independently fixed positive Wronskian.
Use: greenActionFormula_hasDerivAt gives its genuine spatial derivative, and the separate original integral identification proves this same expression is the actual Green contribution in K.
Article: jacobi, Theorem 2.1.
-/
def greenActionFormula (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) (hds : d≤(1/2:ℝ)) (t : HalfInterval) (s : ℝ) : ℝ :=
  (realSolution a (jacobi.Jacobi.endpointCorrection a) (1-s)*leftGreenPrimitive a ha (t,s)+
    realSolution a (jacobi.Jacobi.endpointCorrection a) s*rightGreenPrimitive a ha hd hds (t,s))/zeroGreenConstant a

/-- The exact selected-solution derivative formula for the actual weighted original Green action.
Use: provides the genuine Green contribution to the second-coordinate first derivative of the original K; its two moving-boundary contributions cancel and the original diagonal branch is retained.
Article: jacobi, Theorem 2.1.
-/
def greenActionSlope (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) (hds : d≤(1/2:ℝ)) (t : HalfInterval) (s : ℝ) : ℝ :=
  (-realSlope a (jacobi.Jacobi.endpointCorrection a) (1-s)*leftGreenPrimitive a ha (t,s)+
    realSlope a (jacobi.Jacobi.endpointCorrection a) s*rightGreenPrimitive a ha hd hds (t,s))/zeroGreenConstant a

/-- The original selected Green action formula has precisely its genuine displayed spatial derivative on every required positive physical strip.
Use: after the exact original Green-integral identification, combines with the genuine regularized row derivative to differentiate the original K reconstruction.
Article: jacobi, Theorem 2.1.
Proof: differentiate the true original selected solutions and the two genuine weighted primitives. Their endpoint terms are the same actual K(t,s)*chi(s)*check chi(s) with opposite signs, so they cancel exactly. -/
theorem greenActionFormula_hasDerivAt {a d s : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ))
    (t : HalfInterval) (hs : s∈Icc d (1/2)) :
    HasDerivAt (greenActionFormula a ha hd hds t) (greenActionSlope a ha hd hds t s) s := by
  -- All derivatives here are of independently constructed original functions; continuity of K suffices for the two primitive FTC steps.
  have hs' : s∈Ioo (0:ℝ) 1 := ⟨hd.trans_le hs.1,by linarith [hs.2]⟩
  have hr : 1-s∈Ioo (0:ℝ) 1 := ⟨by linarith [hs.2],by linarith [hs'.1]⟩
  have hchi := realSolution_hasDerivAt a (jacobi.Jacobi.endpointCorrection a) hs'
  have hcheck : HasDerivAt (fun x : ℝ => realSolution a (jacobi.Jacobi.endpointCorrection a) (1-x))
      (-realSlope a (jacobi.Jacobi.endpointCorrection a) (1-s)) s := by
    convert (realSolution_hasDerivAt a (jacobi.Jacobi.endpointCorrection a) hr).comp s ((hasDerivAt_id s).const_sub 1) using 1
    · rfl
    · ring
  have hA := weightedKernelPrimitive_hasDerivAt a ha (leftZeroWeight a ha) t s
  rw [leftZeroWeight_value ha ⟨hs'.1.le,hs.2⟩] at hA
  have hB := (weightedKernelPrimitive_hasDerivAt a ha (rightZeroWeight a ha hd hds) t s).const_sub
    (weightedKernelPrimitive a ha (rightZeroWeight a ha hd hds) (t,(t:ℝ)))
  rw [rightZeroWeight_value ha hd hds hs] at hB
  convert ((hcheck.mul hA).add (hchi.mul hB)).div_const (zeroGreenConstant a) using 1
  · rfl
  · unfold greenActionSlope leftGreenPrimitive rightGreenPrimitive
    dsimp only [ContinuousMap.coe_mk]
    ring

end
end jacobi.GelfandLevitan
