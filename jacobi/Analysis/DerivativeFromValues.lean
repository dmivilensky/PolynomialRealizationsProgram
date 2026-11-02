import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
Article: jacobi, Lemma E.1.
Applied to the actual Bessel Hankel error and its forced ODE, this
preserves the cubic real-ray remainder for the initial Cauchy slope
before propagation into bounded complex-frequency strips.
Source: the fundamental theorem of calculus and the mean-value bound.
Use: the original Bessel Hankel error has a cubic initial slope bound from its proved cubic value bound and actual forced ODE, with no assumed differentiated asymptotic expansion.
-/
namespace jacobi.Analysis
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- The actual starting slope of a genuine complex-valued C2 function is controlled by its true values and true curvature on a unit interval.
Use: the original Bessel Hankel error has a cubic initial slope bound from its proved cubic value bound and actual forced ODE, with no assumed differentiated asymptotic expansion.
Article: jacobi, Lemma E.1.
Proof: the mean-value inequality bounds g(t)-g(x) by N on the original unit interval. Integrate the genuine derivative f'=g, subtract the constant starting slope, and bound its integral by N and its true endpoint difference by 2*M. -/
theorem slope_bound_from_values {f g h : ℝ → ℂ} {x M N : ℝ} (hN : 0≤N)
    (hf : ∀ t∈Icc x (x+1),HasDerivAt f (g t) t)
    (hg : ∀ t∈Icc x (x+1),HasDerivAt g (h t) t)
    (hv : ∀ t∈Icc x (x+1),‖f t‖≤M)
    (hh : ∀ t∈Icc x (x+1),‖h t‖≤N) : ‖g x‖≤2*M+N := by
  -- Integrate the original derivative only after its actual continuity is supplied by the second derivative.
  have hxi : x∈Icc x (x+1) := ⟨le_rfl,by linarith⟩
  have hright : x+1∈Icc x (x+1) := ⟨by linarith,le_rfl⟩
  have hc : ContinuousOn g (Icc x (x+1)) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable g volume x (x+1) := hc.intervalIntegrable_of_Icc (by linarith)
  have hb (t : ℝ) (ht : t∈Icc x (x+1)) : ‖g t-g x‖≤N := by
    have he := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => (hg s hs).hasDerivWithinAt) (fun s hs => hh s ⟨hs.1,hs.2.le⟩) t ht
    have htx : t-x≤1 := by linarith [ht.2]
    exact he.trans (by nlinarith)
  have he : (∫ t in x..(x+1),g t)=f (x+1)-f x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hf t
      (by simpa only [uIcc_of_le (by linarith : x≤x+1)] using ht)) hi
  have hsmall : ‖(∫ t in x..(x+1),g t)-g x‖≤N := by
    have hb' := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x) (b := x+1) (f := fun t => g t-g x) (C := N) (fun t ht => by
        rw [uIoc_of_le (by linarith : x≤x+1)] at ht
        exact hb t ⟨ht.1.le,ht.2⟩)
    rw [intervalIntegral.integral_sub hi (intervalIntegrable_const),intervalIntegral.integral_const] at hb'
    simpa only [add_sub_cancel_left,one_smul,abs_one,mul_one] using hb'
  calc
    ‖g x‖ = ‖(f (x+1)-f x)-((∫ t in x..(x+1),g t)-g x)‖ := by rw [he]; congr 1; abel
    _ ≤ ‖f (x+1)-f x‖+‖(∫ t in x..(x+1),g t)-g x‖ := norm_sub_le _ _
    _ ≤ (‖f (x+1)‖+‖f x‖)+N := add_le_add (norm_sub_le _ _) hsmall
    _ ≤ 2*M+N := by linarith [hv x hxi,hv (x+1) hright]

end
end jacobi.Analysis
