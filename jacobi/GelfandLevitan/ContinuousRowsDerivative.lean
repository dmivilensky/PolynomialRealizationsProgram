import jacobi.GelfandLevitan.DerivativeForcing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: jacobi, Theorem 2.1.
Continuous pointwise derivatives on a compact spatial domain are
genuine derivatives in the uniform function norm. This supplies the
uniform limit of the original F difference quotients on a fixed
physical prefix; no operator-norm derivative of a moving cutoff is used.
Source: the fundamental theorem of calculus and continuous point evaluation.
Use: prefixKernelRows_hasDerivWithinAt applies this to the original reference kernel on a fixed spatial prefix, proving the uniform difference-quotient limit required for the actual t derivative of K.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Pointwise derivatives of continuous rows, themselves continuous in the uniform norm, give the actual uniform-norm derivative on the same closed interval.
Use: prefixKernelRows_hasDerivWithinAt applies this to the original reference kernel on a fixed spatial prefix, proving the uniform difference-quotient limit required for the actual t derivative of K.
Article: jacobi, Theorem 2.1.
Source: the classical fundamental theorem of calculus, mathlib MeasureTheory.Integral.IntervalIntegral.FundThmCalculus.
Proof: integrate the genuine continuous derivative in the Banach space of continuous rows. Continuous evaluation commutes with that integral; scalar-coordinate FTC identifies it with the original row increment. The Banach-space FTC then differentiates that same original row, including the interval endpoints. -/
theorem continuousRows_hasDerivWithinAt {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ → C(X,E)} (hf : Continuous f) (hg : Continuous g) {a b t : ℝ}
    (ht : t∈Icc a b)
    (hderiv : ∀ x∈Icc a b,∀ y : X,HasDerivWithinAt (fun u => f u y) (g x y) (Icc a b) x) :
    HasDerivWithinAt f (g t) (Icc a b) t := by
  -- Integrate the independently given actual derivative rows before identifying them with the original row increments.
  have hFTC (x : ℝ) (hx : x∈Icc a b) : (∫ u in a..x,g u)=f x-f a := by
    ext y
    have hint := hg.intervalIntegrable (μ := volume) a x
    have hEval := (ContinuousMap.evalCLM ℝ y).intervalIntegral_comp_comm hint
    change (∫ u in a..x,g u y)=(∫ u in a..x,g u) y at hEval
    rw [← hEval]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (((ContinuousMap.evalCLM ℝ y).continuous.comp hf).continuousOn)
      (fun u hu => (hderiv u ⟨hu.1.le,hu.2.le.trans hx.2⟩ y).hasDerivAt
        (Icc_mem_nhds hu.1 (hu.2.trans_le hx.2)))
      (((ContinuousMap.evalCLM ℝ y).continuous.comp hg).intervalIntegrable (μ := volume) a x)
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
