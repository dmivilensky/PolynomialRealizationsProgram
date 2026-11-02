import jacobi.GelfandLevitan.ForcedKernel
import jacobi.GelfandLevitan.KernelSpatialDerivative

/-!
Article: jacobi, Theorem 2.1.
The actual forcing dot F+w*F gives a continuous family of genuine
inhomogeneous GL solutions on every closed positive physical strip.
The actual diagonal w is continuous and tends to zero at the selected
endpoint. KernelRightDerivative and KernelFirstDerivative identify this
same forced family with the genuine partial_t K through actual original
GL difference quotients and the right-derivative fundamental theorem.
Use: this is the same w in the original derivative forcing dot F+w*F and in the potential q_alpha+2*w' of the subsequent differential equation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernel kernelSlope

/-- The actual original diagonal of the already constructed continuous GL transformation kernel.
Use: this is the same w in the original derivative forcing dot F+w*F and in the potential q_alpha+2*w' of the subsequent differential equation.
Article: jacobi, Theorem 2.1.
-/
def kernelDiagonal (a : ℝ) (ha : -1<a) : C(HalfInterval,ℝ) :=
  ⟨fun t => transformationKernel a ha t t,
    (transformationKernel_continuous a ha).comp (continuous_id.prodMk continuous_id)⟩

/-- The actual original GL diagonal vanishes at its genuine singular endpoint.
Use: kernelDiagonal_tendsto_zero proves the original endpoint assertion in Differentiability of K (c), independently of the later diagonal differentiability argument.
Article: jacobi, Theorem 2.1.
Proof: the already constructed actual transformation kernel vanishes on its entire original left endpoint row. -/
theorem kernelDiagonal_zero (a : ℝ) (ha : -1<a) : kernelDiagonal a ha halfZero=0 :=
  transformationKernel_zero a ha halfZero

/-- The actual original GL diagonal tends to zero along its physical half interval at the singular endpoint.
Use: fixes the original w(0+) boundary value before constructing q_alpha+2*w' and the selected transformed branch.
Article: jacobi, Theorem 2.1.
Proof: the true original diagonal is continuous on the physical closed interval and has independently proved value zero at its genuine left endpoint. -/
theorem kernelDiagonal_tendsto_zero (a : ℝ) (ha : -1<a) :
    Tendsto (kernelDiagonal a ha) (𝓝 halfZero) (𝓝 (0:ℝ)) := by
  simpa only [kernelDiagonal_zero] using (kernelDiagonal a ha).continuous.continuousAt.tendsto (x := halfZero)

/-- A closed nonsingular physical parameter strip for the original K derivative argument.
Use: derivativeForcingRows and derivativeCandidateRows are continuous in their genuine uniform function norms on every such original strip.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
abbrev DerivativeStrip (d : ℝ) := {t : ℝ // t∈Icc d (1/2)}

/-- The continuous unaltered physical inclusion of a positive closed strip into the original half interval.
Use: the existing actual K diagonal, source rows and original compressed inverse are reused at precisely the same physical coordinate.
Article: jacobi, Theorem 2.1.
-/
def derivativeStripInclusion {d : ℝ} (hd : 0<d) : C(DerivativeStrip d,HalfInterval) :=
  ⟨fun t => ⟨t,⟨hd.le.trans t.property.1,t.property.2⟩⟩,continuous_subtype_val.subtype_mk _⟩

/-- The actual original dot F rows form a continuous family in their genuine spatial uniform norm.
Use: derivativeForcingRows combines these exact rows with the original w*F, so the actual inhomogeneous derivative problem has continuously varying forcing.
Article: jacobi, Theorem 2.1.
Proof: the independently proved original dot F is jointly continuous on the full closed positive strip. Pull back its spatial coordinate by the existing physical half clamp, then use the community compact-domain currying theorem. -/
def kernelSlopeRows {a d : ℝ} (ha : -1<a) (hd : 0<d) : C(DerivativeStrip d,C(Interval,ℝ)) :=
  (⟨fun p : DerivativeStrip d × Interval => kernelSlope a ha (p.1:ℝ) (halfTime p.2),
    (kernelSlope_continuousOn ha hd).comp_continuous
      (g := fun p : ℝ × ℝ => kernelSlope a ha p.1 p.2)
      (f := fun p : DerivativeStrip d × Interval => ((p.1:ℝ),halfTime p.2))
      ((continuous_subtype_val.comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_snd).min continuous_const))
      (fun p => ⟨p.1.property,halfTime_mem p.2⟩)⟩ : C(DerivativeStrip d × Interval,ℝ)).curry

/-- The literal original differentiated GL forcing dot F(t,.)+w(t)*F(t,.) as a continuous family in spatial uniform norm.
Use: derivativeCandidateRows applies the already proved genuine inhomogeneous original inverse to these exact data; no derivative of K is assumed in constructing the forcing.
Article: jacobi, Theorem 2.1.
-/
def derivativeForcingRows {a d : ℝ} (ha : -1<a) (hd : 0<d) : C(DerivativeStrip d,C(Interval,ℝ)) :=
  ⟨fun t => kernelSlopeRows ha hd t+
    kernelDiagonal a ha (derivativeStripInclusion hd t) • kernelRows a ha (derivativeStripInclusion hd t),
    (kernelSlopeRows ha hd).continuous.add
      (((kernelDiagonal a ha).continuous.comp (derivativeStripInclusion hd).continuous).smul
        ((kernelRows a ha).continuous.comp (derivativeStripInclusion hd).continuous))⟩

/-- The genuine continuous differentiated forcing evaluates to precisely the original dot F+w*F.
Use: the actual difference-quotient limit and the original derivative equation use this same forcing at unchanged physical coordinates.
Article: jacobi, Theorem 2.1.
Proof: evaluate the existing uniform-norm rows and the original unchanged physical source-kernel row. -/
theorem derivativeForcingRows_apply {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (t : DerivativeStrip d) (s : Interval) :
    derivativeForcingRows ha hd t s=kernelSlope a ha (t:ℝ) (halfTime s)+
      kernelDiagonal a ha (derivativeStripInclusion hd t)*kernel a ha (t:ℝ) (halfTime s) := by
  change kernelSlope a ha (t:ℝ) (halfTime s)+kernelDiagonal a ha (derivativeStripInclusion hd t)*
    kernelRows a ha (derivativeStripInclusion hd t) s=_
  rw [kernelRows_apply]
  rfl

/-- The actual inhomogeneous original GL solutions for the original differentiated forcing, continuously in uniform norm.
Use: KernelRightDerivative and KernelFirstDerivative identify these independently constructed true solutions with the genuine partial_t K by exact original quotients and the actual inverse continuity; this construction supplies their equation and continuity independently of that identification.
Article: jacobi, Theorem 2.1.
-/
def derivativeCandidateRows {a d : ℝ} (ha : -1<a) (hd : 0<d) : C(DerivativeStrip d,C(Interval,ℝ)) :=
  ⟨fun t => forcedKernel a ha (derivativeStripInclusion hd t) (derivativeForcingRows ha hd t),
    (forcedKernel_joint_continuous a ha).comp
      ((derivativeStripInclusion hd).continuous.prodMk (derivativeForcingRows ha hd).continuous)⟩

/-- The actual continuous original derivative-forcing solutions satisfy the exact printed differentiated GL equation.
Use: original GL difference quotients have the same limiting inhomogeneous equation; the independently proved forced inverse and uniform reconstruction continuity supply its fixed genuine limit.
Article: jacobi, Theorem 2.1.
Proof: apply the proved original forced GL equation to the actual forcing dot F+w*F and evaluate the already constructed source rows at their unchanged genuine physical coordinates. No derivative identity for K is used or asserted here. -/
theorem derivativeCandidateRows_GL {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (t : DerivativeStrip d) (s : Interval) :
    derivativeCandidateRows ha hd t s+
      (kernelSlope a ha (t:ℝ) (halfTime s)+kernelDiagonal a ha (derivativeStripInclusion hd t)*
        kernel a ha (t:ℝ) (halfTime s))+
      (∫ r : Interval in prefixSet (t:ℝ),derivativeCandidateRows ha hd t r*
        kernel a ha (halfTime s) (halfTime r))=0 := by
  -- Evaluate the actual forcing only in its scalar occurrence, retaining the same fixed continuous inverse row under the integral.
  have hf : derivativeForcingRows ha hd t s=
      kernelSlope a ha (t:ℝ) (halfTime s)+kernelDiagonal a ha (derivativeStripInclusion hd t)*
        kernel a ha (t:ℝ) (halfTime s) := by
    exact derivativeForcingRows_apply ha hd t s
  have hh := forcedKernel_GL a ha (derivativeStripInclusion hd t) (derivativeForcingRows ha hd t) s
  change derivativeCandidateRows ha hd t s+derivativeForcingRows ha hd t s+
    (∫ r : Interval in prefixSet (t:ℝ),derivativeCandidateRows ha hd t r*kernel a ha (halfTime s) (halfTime r))=0 at hh
  rw [hf] at hh
  exact hh

end
end jacobi.GelfandLevitan
