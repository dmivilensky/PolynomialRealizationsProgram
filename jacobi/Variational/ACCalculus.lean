import jacobi.Young.H1Scaling

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Elementary absolutely continuous calculus for measurable coefficients: reflection,
constancy from an a.e. zero derivative, and order from an a.e. derivative sign.
These tools let the ground-state argument retain the article's full L1 domain.
Source: the absolutely continuous fundamental theorem of calculus.
Use: reflects the ground-state slope without assuming a continuous density.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Set Filter Real chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false

/-- Reflection preserves local absolute continuity and reverses the derivative.
Use: reflects the ground-state slope without assuming a continuous density.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: change variables in the absolutely continuous FTC, then represent the
reflected function as an integral of the reflected derivative. -/
theorem locallyAC_reflect {f d : ℝ → ℝ}
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, HasDerivAt f (d x) x) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => f (-x)) a b := by
  -- The reflected FTC proves absolute continuity directly, including at null sets.
  have hi : IntervalIntegrable d volume (-b) (-a) :=
    (hac (-b) (-a)).intervalIntegrable_deriv.congr_ae
      (ae_restrict_of_ae (hd.mono fun _ h => h.deriv))
  have hr0 : IntervalIntegrable (fun x => d (-x)) volume a b := by
    simpa only [neg_neg] using (IntervalIntegrable.iff_comp_neg (f := d)).mp hi.symm
  have hr := hr0.neg
  have hp := hr.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : a ∈ uIcc a b)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f (-a)) a b :=
    (show ContDiff ℝ 1 (fun _ : ℝ => f (-a)) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  apply (hc.add hp).congr
  intro x _
  change f (-a)+(∫ y in a..x, -d (-y))=f (-x)
  rw [intervalIntegral.integral_neg,intervalIntegral.integral_comp_neg,
    locallyAC_integral_eq_sub hac hd]
  ring

/-- A locally absolutely continuous function with a.e. zero derivative is constant.
Use: identifies the ground-state Wronskian before using its integrability.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: apply the absolutely continuous zero-derivative theorem on each interval. -/
theorem locallyAC_const {f : ℝ → ℝ}
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, HasDerivAt f 0 x) (x y : ℝ) : f x=f y := by
  obtain ⟨c,hc⟩ := (hac x y).const_of_ae_hasDerivAt_zero
    (hd.mono fun _ h _ => h)
  exact (hc x left_mem_uIcc).trans (hc y right_mem_uIcc).symm

/-- A nonnegative a.e. derivative orders the endpoints of an absolutely continuous function.
Use: controls the ground-state slope on either side of the coefficient's sign change.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: integrate the derivative sign and use the absolutely continuous FTC. -/
theorem locallyAC_le_of_derivative_nonneg {f d : ℝ → ℝ}
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, HasDerivAt f (d x) x) {a b : ℝ} (hab : a≤b)
    (hn : ∀ᵐ x, x∈Icc a b → 0≤d x) : f a≤f b := by
  have h := intervalIntegral.integral_nonneg_of_ae_restrict hab
    ((ae_restrict_iff' measurableSet_Icc).mpr hn)
  rw [locallyAC_integral_eq_sub hac hd] at h
  linarith

end
end jacobi.Variational
