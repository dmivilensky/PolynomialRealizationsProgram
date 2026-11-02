import jacobi.GelfandLevitan.StripPrimitive

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The positive real integrating factors for the finite quasi-derivative
system depend continuously on the original diagonal in the uniform
norm. Their true derivatives and reciprocal identity give a direct
route to the derivative limit from actual finite solution values.
Use: stripGauge_hasDerivWithinAt gives its genuine derivative and stripGauge_continuous permits the finite-to-infinite quasi-derivative passage in the uniform norm.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The positive integrating factor formed from the actual physical-strip primitive.
Use: stripGauge_hasDerivWithinAt gives its genuine derivative and stripGauge_continuous permits the finite-to-infinite quasi-derivative passage in the uniform norm.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the standard integrating-factor method for a scalar first-order linear ODE. -/
def stripGauge {p q : ℝ} (hpq : p≤q) (c : ℝ) (w : C(ClosedStrip p q,ℝ)) : C(ClosedStrip p q,ℝ) :=
  ⟨fun t => Real.exp (c*stripPrimitive hpq w t),
    Real.continuous_exp.comp (continuous_const.mul (stripPrimitive hpq w).continuous)⟩

/-- The integrating factor is continuous in the original diagonal in the actual uniform function norm.
Use: the actual finite diagonals already converge in this norm, so both positive and negative integrating factors converge without a diagonal-derivative convergence hypothesis.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: continuity of postcomposition on continuous maps from a compact domain.
Proof: compose the bounded genuine strip primitive and scalar multiplication with the community continuous postcomposition by the real exponential. -/
theorem stripGauge_continuous {p q : ℝ} (hpq : p≤q) (c : ℝ) :
    Continuous (stripGauge hpq c) := by
  change Continuous (fun w : C(ClosedStrip p q,ℝ) =>
    (⟨Real.exp,Real.continuous_exp⟩:C(ℝ,ℝ)).comp (c • stripPrimitive hpq w))
  exact (ContinuousMap.continuous_postcomp ⟨Real.exp,Real.continuous_exp⟩).comp
    ((stripPrimitive hpq).continuous.const_smul c)

/-- The genuine integrating factor equals one at the original left physical endpoint.
Use: the actual quasi-derivative gauge integration constants retain their original endpoint values.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: its actual physical primitive is zero at that endpoint, so its exponential is one. -/
theorem stripGauge_left {p q : ℝ} (hpq : p≤q) (c : ℝ) (w : C(ClosedStrip p q,ℝ)) :
    stripGauge hpq c w ⟨p,⟨le_rfl,hpq⟩⟩=1 := by
  change Real.exp (c*stripPrimitive hpq w ⟨p,⟨le_rfl,hpq⟩⟩)=1
  rw [stripPrimitive_left,mul_zero,Real.exp_zero]

/-- The original positive and negative integrating factors are actual pointwise reciprocals.
Use: the finite quasi-derivative is recovered from its integrated gauge expression using this genuine identity.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: their exponential arguments sum to zero. -/
theorem stripGauge_reciprocal {p q : ℝ} (hpq : p≤q) (c : ℝ) (w : C(ClosedStrip p q,ℝ))
    (t : ClosedStrip p q) : stripGauge hpq c w t*stripGauge hpq (-c) w t=1 := by
  change Real.exp (c*stripPrimitive hpq w t)*Real.exp (-c*stripPrimitive hpq w t)=1
  rw [← Real.exp_add,show c*stripPrimitive hpq w t+-c*stripPrimitive hpq w t=0 by ring,Real.exp_zero]

/-- The actual positive integrating factor has its genuine physical derivative on the whole original strip.
Use: differentiating the true gauged finite quasi-derivative cancels its original first-order drift term.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the endpoint FTC and the ordinary exponential chain rule.
Proof: the independently proved physical-strip primitive has actual derivative w(t). Compose its true derivative with scalar multiplication and the real exponential, keeping the original physical endpoint value. -/
theorem stripGauge_hasDerivWithinAt {p q : ℝ} (hpq : p≤q) (c : ℝ)
    (w : C(ClosedStrip p q,ℝ)) (t : ClosedStrip p q) :
    HasDerivWithinAt (stripExtension hpq (stripGauge hpq c w))
      (c*w t*stripGauge hpq c w t) (Icc p q) (t:ℝ) := by
  have hP := (stripPrimitive_hasDerivWithinAt hpq w t).const_mul c
  have h := (Real.hasDerivAt_exp (c*stripExtension hpq (stripPrimitive hpq w) t)).comp_hasDerivWithinAt (t:ℝ) hP
  rw [stripExtension_value] at h
  convert h using 1
  · rfl
  · change c*w t*Real.exp (c*stripPrimitive hpq w t)=Real.exp (c*stripPrimitive hpq w t)*(c*w t)
    ring

end
end jacobi.GelfandLevitan
