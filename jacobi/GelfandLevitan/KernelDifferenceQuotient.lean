import jacobi.GelfandLevitan.KernelRowEquation
import jacobi.GelfandLevitan.PrefixKernelDerivative
import jacobi.GelfandLevitan.ForcedUniqueness

/-!
Article: jacobi, Theorem 2.1.
Actual difference quotients of the already constructed original K
satisfy the exact original forced GL equation on a fixed prefix.
Their forcing is the genuine F difference quotient plus the actual
normalized moving tail. The independently proved inverse uniqueness
identifies these true quotients with the original forced reconstruction.
Use: its exact forced GL equation and inverse identification are proved before any derivative limit is invoked.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel transformationKernel

/-- The literal original K difference quotient as a genuine continuous spatial row.
Use: its exact forced GL equation and inverse identification are proved before any derivative limit is invoked.
Article: jacobi, Theorem 2.1.
-/
def kernelDifferenceQuotient (a : ℝ) (ha : -1<a) (t u : HalfInterval) : C(Interval,ℝ) :=
  ((u:ℝ)-(t:ℝ))⁻¹ • (transformationRows a ha u-transformationRows a ha t)

/-- Evaluation of the true K row difference quotient gives precisely the original scalar difference quotient.
Use: its eventual uniform-norm limit is therefore the actual derivative of the original constructed K.
Article: jacobi, Theorem 2.1.
Proof: evaluate the genuine scalar action and original continuous K rows. -/
theorem kernelDifferenceQuotient_apply (a : ℝ) (ha : -1<a) (t u : HalfInterval) (r : Interval) :
    kernelDifferenceQuotient a ha t u r=((u:ℝ)-(t:ℝ))⁻¹*
      (transformationKernel a ha u (halfClamp r)-transformationKernel a ha t (halfClamp r)) := rfl

/-- The exact original difference-quotient forcing before restricting to the fixed physical prefix.
Use: kernelDifferenceQuotient_GL derives its genuine equation directly from two original GL equations; clipping its unused tail supplies uniform convergence in the existing continuous function space.
Article: jacobi, Theorem 2.1.
-/
def kernelQuotientForcing (a : ℝ) (ha : -1<a) (t u : HalfInterval) : C(Interval,ℝ) :=
  ((u:ℝ)-(t:ℝ))⁻¹ • (kernelRows a ha u-kernelRows a ha t)+affineAverage (glTailIntegrand a ha) t u

/-- The independently constructed actual original row equations yield the exact difference-quotient row identity.
Use: kernelDifferenceQuotient_GL converts its evaluated prefix term to the literal forced physical-prefix equation, to which the proved genuine inverse applies.
Article: jacobi, Theorem 2.1.
Proof: the normalized moving tail is its exact difference of genuine original prefix integrals. Subtract the two already proved original Banach-row GL identities and scale by the actual endpoint difference inverse. -/
theorem kernelDifferenceQuotient_equation (a : ℝ) (ha : -1<a) (t u : HalfInterval) (htu : u≠t) :
    kernelDifferenceQuotient a ha t u+kernelQuotientForcing a ha t u+
      ((u:ℝ)-(t:ℝ))⁻¹ • (glPrefixIntegral a ha u (t:ℝ)-glPrefixIntegral a ha t (t:ℝ))=0 := by
  -- Subtraction takes place in the actual common Banach space of continuous original spatial rows.
  rw [kernelDifferenceQuotient,kernelQuotientForcing,glTailAverage_prefix a ha t u htu]
  ext s
  have hu := congrArg (fun g : C(Interval,ℝ) => g s) (transformationRows_GL a ha u)
  have ht := congrArg (fun g : C(Interval,ℝ) => g s) (transformationRows_GL a ha t)
  change transformationRows a ha u s+kernelRows a ha u s+glPrefixIntegral a ha u (u:ℝ) s=0 at hu
  change transformationRows a ha t s+kernelRows a ha t s+glPrefixIntegral a ha t (t:ℝ) s=0 at ht
  change ((u:ℝ)-(t:ℝ))⁻¹*(transformationRows a ha u s-transformationRows a ha t s)+
    (((u:ℝ)-(t:ℝ))⁻¹*(kernelRows a ha u s-kernelRows a ha t s)+
      ((u:ℝ)-(t:ℝ))⁻¹*(glPrefixIntegral a ha u (u:ℝ) s-glPrefixIntegral a ha u (t:ℝ) s))+
    ((u:ℝ)-(t:ℝ))⁻¹*(glPrefixIntegral a ha u (t:ℝ) s-glPrefixIntegral a ha t (t:ℝ) s)=0
  linear_combination ((u:ℝ)-(t:ℝ))⁻¹*(hu-ht)

/-- The genuine prefix integral of the actual K difference quotient is precisely the original scaled prefix-integral difference.
Use: kernelDifferenceQuotient_GL identifies the true quotient equation with the exact original forced kernel equation, before any limiting argument.
Article: jacobi, Theorem 2.1.
Proof: original kernel symmetry puts the scalar integrand in the original row order. Expand the literal genuine difference quotient, and use integrability, linearity and the proved original prefix-integral representatives. -/
theorem kernelDifferenceQuotient_integral (a : ℝ) (ha : -1<a) (t u : HalfInterval) (s : Interval) :
    (∫ r : Interval in prefixSet (t:ℝ),kernelDifferenceQuotient a ha t u r*
      kernel a ha (halfTime s) (halfTime r))=
      ((u:ℝ)-(t:ℝ))⁻¹*(glPrefixIntegral a ha u (t:ℝ) s-glPrefixIntegral a ha t (t:ℝ) s) := by
  -- Every term is an actual integrable original continuous scalar row; no quotient representative is differentiated.
  have hf : (fun r : Interval => kernelDifferenceQuotient a ha t u r*kernel a ha (halfTime s) (halfTime r))=
      (fun r : Interval => ((u:ℝ)-(t:ℝ))⁻¹*(transformationKernel a ha u (halfClamp r)*kernel a ha (halfTime r) (halfTime s)-
        transformationKernel a ha t (halfClamp r)*kernel a ha (halfTime r) (halfTime s))) := by
    funext r
    rw [kernelDifferenceQuotient_apply,kernel_symmetric a ha (halfTime s) (halfTime r)]
    ring
  rw [hf,integral_const_mul,integral_sub (glTailPrefix_integrable a ha u t s) (glTailPrefix_integrable a ha t t s),
    ← glPrefixIntegral_apply a ha u t s,← glPrefixIntegral_apply a ha t t s]

/-- The actual original K difference quotient satisfies the literal original inhomogeneous physical-prefix GL equation.
Use: kernelDifferenceQuotient_forced applies the independently proved original inverse uniqueness to these exact true quotients.
Article: jacobi, Theorem 2.1.
Proof: evaluate the already proved original Banach-row difference equation and substitute the independently proved exact physical-prefix quotient integral. -/
theorem kernelDifferenceQuotient_GL (a : ℝ) (ha : -1<a) (t u : HalfInterval) (htu : u≠t) (s : Interval) :
    kernelDifferenceQuotient a ha t u s+kernelQuotientForcing a ha t u s+
      (∫ r : Interval in prefixSet (t:ℝ),kernelDifferenceQuotient a ha t u r*kernel a ha (halfTime s) (halfTime r))=0 := by
  rw [kernelDifferenceQuotient_integral]
  exact congrArg (fun g : C(Interval,ℝ) => g s) (kernelDifferenceQuotient_equation a ha t u htu)

/-- Every true original K difference quotient equals the independently constructed genuine forced inverse reconstruction at each original prefix point.
Use: the actual uniform forcing limit and proved reconstruction continuity give the genuine derivative of the original K, without a derivative-identification premise.
Article: jacobi, Theorem 2.1.
Proof: the literal true quotient satisfies the exact original forced physical equation; invoke the previously proved genuine continuous forced uniqueness theorem. -/
theorem kernelDifferenceQuotient_forced (a : ℝ) (ha : -1<a) (t u : HalfInterval) (htu : u≠t)
    (s : Interval) (hs : (s:ℝ)≤(t:ℝ)) :
    kernelDifferenceQuotient a ha t u s=forcedKernel a ha t (kernelQuotientForcing a ha t u) s :=
  continuous_forced_unique a ha t _ _ (fun r _ => kernelDifferenceQuotient_GL a ha t u htu r) s hs

/-- The actual forced reconstruction on its physical prefix depends only on the original forcing on that prefix.
Use: the independently proved uniform forcing limit is represented by spatial clipping, while the actual differentiated GL forcing remains the original unclipped dot F+w*F.
Article: jacobi, Theorem 2.1.
Proof: fixed-prefix clipping fixes every point of the original equation domain. The genuine clipped forced solution therefore solves the same original equation there; true continuous forced uniqueness identifies its actual physical values. -/
theorem forcedKernel_prefixClamp (a : ℝ) (ha : -1<a) (t : HalfInterval)
    (b : C(Interval,ℝ)) (s : Interval) (hs : (s:ℝ)≤(t:ℝ)) :
    forcedKernel a ha t (b.comp (prefixClamp t)) s=forcedKernel a ha t b s := by
  apply continuous_forced_unique a ha t _ b _ s hs
  intro r hr
  have h := forcedKernel_GL a ha t (b.comp (prefixClamp t)) r
  simpa only [ContinuousMap.comp_apply,prefixClamp_fix t r hr] using h

/-- Actual K difference quotients equal the genuine forced inverse applied to the continuous clipped original forcing.
Use: the proved uniform limit on the fixed original prefix now passes directly through the independently proved uniform-norm continuity of forcedKernel.
Article: jacobi, Theorem 2.1.
Proof: spatial clipping preserves every original forcing value in its own physical prefix equation, so true continuous forced uniqueness applies to the original actual quotient. -/
theorem kernelDifferenceQuotient_clipped_forced (a : ℝ) (ha : -1<a) (t u : HalfInterval) (htu : u≠t)
    (s : Interval) (hs : (s:ℝ)≤(t:ℝ)) :
    kernelDifferenceQuotient a ha t u s=
      forcedKernel a ha t ((kernelQuotientForcing a ha t u).comp (prefixClamp t)) s := by
  apply continuous_forced_unique a ha t _ _ _ s hs
  intro r hr
  simpa only [ContinuousMap.comp_apply,prefixClamp_fix t r hr] using kernelDifferenceQuotient_GL a ha t u htu r

end
end jacobi.GelfandLevitan
