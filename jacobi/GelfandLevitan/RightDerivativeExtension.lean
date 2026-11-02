import jacobi.GelfandLevitan.ContinuousRowsDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: jacobi, Theorem 2.1.
A continuous function with a continuous original right derivative
has that actual derivative throughout a closed physical interval,
with the appropriate one-sided derivatives at its endpoints.
Source: the fundamental theorem of calculus for right derivatives.
Use: transformationKernel_hasDerivWithinAt_first converts the independently proved original K right derivative into the complete first-coordinate derivative assertion of Differentiability of K (a).
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Continuous original right derivatives extend to genuine derivatives within the entire closed interval, including its upper endpoint.
Use: transformationKernel_hasDerivWithinAt_first converts the independently proved original K right derivative into the complete first-coordinate derivative assertion of Differentiability of K (a).
Article: jacobi, Theorem 2.1.
Source: mathlib's fundamental theorem of calculus for continuous functions with right derivatives, integral_eq_sub_of_hasDeriv_right_of_le.
Proof: integrate the independently given continuous right derivative on each initial subinterval. The right-derivative FTC identifies that actual integral with the original function increment. The usual Banach-space FTC differentiates this same original function within the closed interval, including both endpoints. -/
theorem continuous_hasDerivWithinAt_of_right {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g)
    {a b t : ℝ} (ht : t∈Icc a b)
    (hderiv : ∀ x∈Ico a b,HasDerivWithinAt f (g x) (Ici x) x) :
    HasDerivWithinAt f (g t) (Icc a b) t := by
  -- The FTC is applied to the independently proved actual right derivatives, rather than to a separately named derivative candidate.
  have hFTC (x : ℝ) (hx : x∈Icc a b) : (∫ u in a..x,g u)=f x-f a :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx.1 hf.continuousOn
      (fun u hu => (hderiv u ⟨hu.1.le,hu.2.trans_le hx.2⟩).Ioi_of_Ici)
      (hg.intervalIntegrable (μ := volume) a x)
  have hH : HasDerivAt (fun x => f a+∫ u in a..x,g u) (g t) t := by
    simpa only [zero_add] using
      (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable (μ := volume) a t)
        hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add (f a)
  apply hH.hasDerivWithinAt.congr
  · intro x hx
    rw [hFTC x hx]
    abel
  · rw [hFTC t ht]
    abel

end
end jacobi.GelfandLevitan
