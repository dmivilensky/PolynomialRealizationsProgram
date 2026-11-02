import jacobi.Young.PotentialRegularity

/-!
Article: jacobi, Appendix D.5 (compact root-mass profile).
The optimizing density jumps at its free boundary, so global continuity is
not imposed. At every actual continuity point of a measurable L1 density,
the original Green slope has its classical derivative. This follows from
the genuine left/right exponential primitives and the pointwise FTC.
Source: the existing convolution primitives in chebyshev2 and the real FTC.
Use: the compact optimizer needs a classical Green equation inside and outside its jump, not across the boundary.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open chebyshev2.GroundState chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false

/-- A genuine exponential primitive satisfies its classical equation at every continuity point of its measurable forcing.
Use: the compact optimizer needs a classical Green equation inside and outside its jump, not across the boundary.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the weighted original forcing is interval integrable and measurable.
At the stated point it is continuous, so the actual FTC and the exponential product rule apply. -/
theorem exponentialPrimitive_hasDerivAt_at {j : ℝ → ℝ} (hj : Integrable j) (hjm : Measurable j)
    {x : ℝ} (hc : ContinuousAt j x) (c C : ℝ) :
    HasDerivAt (exponentialPrimitive c j C) (c*exponentialPrimitive c j C x+j x) x := by
  -- Local continuity at this point suffices; jumps elsewhere do not enter the FTC hypothesis.
  have hi : IntervalIntegrable (fun t => exp (-c*t)*j t) volume 0 x := by
    apply intervalIntegrable_iff.mpr
    exact ((exponentialForcing_locallyIntegrable hj.locallyIntegrable c).integrableOn_isCompact isCompact_uIcc).mono_set
      uIoc_subset_uIcc
  have hmeas : StronglyMeasurable (fun t => exp (-c*t)*j t) :=
    ((by fun_prop : Measurable (fun t : ℝ => exp (-c*t))).mul hjm).stronglyMeasurable
  have hcont : ContinuousAt (fun t => exp (-c*t)*j t) x := (by fun_prop : ContinuousAt (fun t : ℝ => exp (-c*t)) x).mul hc
  have hp := intervalIntegral.integral_hasDerivAt_right hi hmeas.stronglyMeasurableAtFilter hcont
  convert ((((hasDerivAt_id x).const_mul c).exp).mul ((hasDerivAt_const x C).add hp)) using 1
  · rfl
  · dsimp only [exponentialPrimitive,id_eq,Pi.add_apply]
    have he : exp (c*x)*exp (-c*x)=1 := by rw [← exp_add]; ring_nf; exact exp_zero
    nlinarith [congrArg (fun r : ℝ => r*j x) he]

/-- The actual exponent-one Green slope has its classical derivative at every continuity point of a measurable L1 density.
Use: supplies the local piecewise classical equation without a false global smoothness premise at the optimizer's jump.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: use the genuine left and right exponential primitive representations,
differentiate each at the actual continuity point, and combine their derivative difference. -/
theorem convolutionSlope_hasDerivAt_at {j : ℝ → ℝ} (hj : Integrable j) (hjm : Measurable j)
    {x : ℝ} (hc : ContinuousAt j x) :
    HasDerivAt (convolutionSlope j) (H1.rep (convolution j) x-2*j x) x := by
  -- Both half-convolutions are the original weighted primitives, not auxiliary solutions.
  have hL : HasDerivAt (leftGreen j) (-leftGreen j x+j x) x := by
    rw [leftGreen_primitive hj]
    simpa only [neg_one_mul] using exponentialPrimitive_hasDerivAt_at hj hjm hc (-1) _
  have hR : HasDerivAt (rightGreen j) (rightGreen j x-j x) x := by
    rw [rightGreen_primitive hj]
    convert exponentialPrimitive_hasDerivAt_at hj.neg hjm.neg hc.neg 1 _ using 1
    simp only [one_mul,Pi.neg_apply,sub_eq_add_neg]
    unfold exponentialPrimitive
    simp only [Pi.neg_apply]
  convert hR.sub hL using 1
  · rfl
  · rw [convolution_halves hj]
    ring

/-- The actual exponent-two Green potential obeys its classical second equation at every actual continuity point of the density.
Use: the inner optimizer's compact positive branch has a real classical ODE while its jump boundary retains only C1 matching.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: apply the proved local exponent-one Green derivative to the original
rescaled source, then compose with x to 2*x and simplify the exact normalization. -/
theorem potential_second_derivative_at (m : Density) {x : ℝ} (hm : ContinuousAt m.value x) :
    HasDerivAt (potentialSlope m) (4*potential m x-4*m.value x) x := by
  -- The rescaling is applied only after the local classical equation has been proved for the true source.
  have hs : Measurable (source m) := m.measurable.comp (measurable_id.div_const 2)
  have hm' : ContinuousAt m.value ((2*x)/2) := by simpa only [mul_div_cancel_left₀ x (by norm_num : (2:ℝ)≠0)] using hm
  have hc : ContinuousAt (source m) (2*x) := by
    exact hm'.comp (f := fun t : ℝ => t/2) (continuousAt_id.div_const 2)
  have hd := convolutionSlope_hasDerivAt_at (source_integrable m) hs hc
  convert hd.comp x ((hasDerivAt_id x).const_mul 2) using 1
  · rfl
  · dsimp only [potential,source]
    rw [show (2*x)/2=x by ring]
    ring

end
end jacobi.RootMass
