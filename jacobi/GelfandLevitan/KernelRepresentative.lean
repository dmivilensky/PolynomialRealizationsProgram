import jacobi.GelfandLevitan.KernelAction
import jacobi.GelfandLevitan.HalfProjection
import jacobi.GelfandLevitan.SolutionRows

/-!
Article: jacobi, Proposition C.2.
The source F operator has the continuous original integral representative
on the physical half interval and vanishes on its zero-extension tail.
Consequently the true inverse solution equation is the original
spatial equation almost everywhere on its physical prefix.
Use: identifies the original inverse row equation with its literal source right-hand side F(t,s).
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The original kernel row has its exact continuous physical representative on the actual half domain, with zero extension outside.
Use: identifies the original inverse row equation with its literal source right-hand side F(t,s).
Article: jacobi, Proposition C.2.
Proof: apply the actual continuous-function half-projection representative theorem to the original source row. -/
theorem kernelRowVector_ae (a : ℝ) (ha : -1<a) (t : HalfInterval) :
    (kernelRowVector a ha t:Space)=ᵐ[volume]
      (prefixSet (1/2)).indicator (kernelRows a ha t) :=
  halfProjection_toLp_ae (kernelRows a ha t)

/-- The actual compact GL operator is represented by the true continuous source kernel integral on the original half domain.
Use: rewrites its genuine Hilbert inverse equation as the original spatial GL equation almost everywhere on every physical prefix.
Article: jacobi, Proposition C.2.
Proof: the proved original spectral norm sum equals the actual integral
kernel operator. The genuine continuous-function L2 inclusion and
half-space projection therefore have the exact original physical
indicator representative already established independently. -/
theorem kernelOperator_ae (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    (kernelOperator a ha v:Space)=ᵐ[volume]
      (prefixSet (1/2)).indicator (kernelActionMap a ha v) := by
  rw [← integralKernelOperator_eq]
  exact halfProjection_toLp_ae (kernelActionMap a ha v)

/-- The actual inverse GL row obeys the original spatial integral equation almost everywhere on its true physical interval.
Use: the reconstructed continuous kernel agrees there with this same original row, and substituting it proves the genuine pointwise GL equation.
Article: jacobi, Proposition C.2.
Proof: remove the inner projection using the actual support of k_t.
Evaluate the resulting genuine Hilbert equality only almost everywhere,
using the true source representatives of addition, negation, the actual
cutoff, source rows and integral kernel action. Both physical indicators
equal one on the original prefix, giving precisely the source equation. -/
theorem solutionRow_spatial_equation (a : ℝ) (ha : -1<a) (t : HalfInterval) :
    ∀ᵐ s:Interval,(s:ℝ)≤(t:ℝ) →
      (solutionRow a ha t:Space) s+kernelActionMap a ha (solutionRow a ha t) s=
        -kernelRows a ha t s := by
  -- The original quotient-space equation is evaluated only outside the union of its actual representative null sets.
  have he := solutionRow_equation a ha t
  change solutionRow a ha t+
    cutoffProjection (t:ℝ) (kernelOperator a ha (cutoffProjection (t:ℝ) (solutionRow a ha t)))=
      -(cutoffProjection (t:ℝ) (kernelRowVector a ha t)) at he
  rw [solutionRow_projected] at he
  have heLp := congrArg (fun v:halfSubspace => (v:Space)) he
  change (solutionRow a ha t:Space)+
    (cutoffProjection (t:ℝ) (kernelOperator a ha (solutionRow a ha t)):Space)=
      -(cutoffProjection (t:ℝ) (kernelRowVector a ha t):Space) at heLp
  have hea := Eventually.of_forall (f := ae (volume : Measure Interval))
    (fun s:Interval => congrArg (fun v:Space => v s) heLp)
  filter_upwards [hea,
    Lp.coeFn_add (solutionRow a ha t:Space)
      (cutoffProjection (t:ℝ) (kernelOperator a ha (solutionRow a ha t)):Space),
    Lp.coeFn_neg (cutoffProjection (t:ℝ) (kernelRowVector a ha t):Space),
    cutoffProjection_ae (t:ℝ) (kernelOperator a ha (solutionRow a ha t)),
    cutoffProjection_ae (t:ℝ) (kernelRowVector a ha t),
    kernelOperator_ae a ha (solutionRow a ha t),kernelRowVector_ae a ha t]
    with s he hs hn hp hq hF hR
  intro hst
  have hprefix : s∈prefixSet (t:ℝ) := hst
  have hhalf : s∈prefixSet (1/2) := hst.trans t.property.2
  rw [hs,hn] at he
  change (solutionRow a ha t:Space) s+
    (cutoffProjection (t:ℝ) (kernelOperator a ha (solutionRow a ha t)):Space) s=
      -(cutoffProjection (t:ℝ) (kernelRowVector a ha t):Space) s at he
  rw [hp,hq,indicator_of_mem hprefix,indicator_of_mem hprefix,hF,hR,
    indicator_of_mem hhalf,indicator_of_mem hhalf] at he
  exact he

end
end jacobi.GelfandLevitan
