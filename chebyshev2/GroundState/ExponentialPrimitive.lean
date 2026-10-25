import chebyshev2.Sobolev.Energy

/-!
Article: chebyshev2, Theorem 5.1.
Integrating-factor primitive for arbitrary locally integrable forcing.
Use: `chebyshev2.GroundState.exponentialPrimitive_derivative_ae` feeds
`chebyshev2.PrescribedSpeed.SpeedData.X_derivative_ae` (X derivative ae).
Proof chain: `chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae` — chebyshev2, Theorem 5.1;
General measurable speed gives a density with the prescribed ground parameter.
-/
namespace chebyshev2.GroundState
noncomputable section
open chebyshev2.Sobolev Set MeasureTheory Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Continuity of the displayed function: `Continuous f`.

Use: `chebyshev2.Calibration.Data.J_composition_integrable` uses this continuity result to
establish integrability of the displayed function: `Integrable (fun x => C.Jprime
(C.calibrationState G x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn
x)^2-2*C.calibrationState G x))`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem locallyAC_continuous {f : ℝ → ℝ}
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc := (hac (x-1) (x+1)).continuousOn
  rw [uIcc_of_le (by linarith : x-1 ≤ x+1)] at hc
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/--
A continuous AE derivative of a locally AC function is its derivative at every point. This
removes the cancellation singularity in the convolution.

The actual derivative at the stated point: `HasDerivAt f (d x) x`.

Use: `chebyshev2.Calibration.Data.comparisonCoordinate_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (C.comparisonSpeed
hκ).q (κ*C.comparisonDensity hκ x-chebyshev2.Calibration.Q ((C.comparisonSpeed hκ).q x))
x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem locallyAC_hasDerivAt_of_continuous {f d : ℝ → ℝ}
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, HasDerivAt f (d x) x) (hc : Continuous d) (x : ℝ) : HasDerivAt f (d x) x := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : (fun x => f 0+∫ t in (0:ℝ)..x, d t)=f := by
    funext x
    rw [locallyAC_integral_eq_sub hac hd]
    ring
  have h := (hasDerivAt_const x (f 0)).add hi
  change HasDerivAt (fun x => f 0+∫ t in (0:ℝ)..x, d t) (0+d x) x at h
  simpa only [he,zero_add] using h

/--
Integrating-factor primitive for arbitrary locally integrable forcing.

Use: `chebyshev2.GroundState.exponentialPrimitive_derivative_ae` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(exponentialPrimitive c j C) (c*exponentialPrimitive c j C x+j x) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.
-/
def exponentialPrimitive (c : ℝ) (j : ℝ → ℝ) (C : ℝ) (x : ℝ) : ℝ :=
  exp (c*x)*(C+∫ t in (0:ℝ)..x, exp (-c*t)*j t)

/--
The stated quantitative bound `LocallyIntegrable (fun t => exp (-c*t)*j t) volume`.

Use: `chebyshev2.GroundState.exponentialPrimitive_derivative_ae` uses this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(exponentialPrimitive c j C) (c*exponentialPrimitive c j C x+j x) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem exponentialForcing_locallyIntegrable {j : ℝ → ℝ} (hj : LocallyIntegrable j volume) (c : ℝ) :
    LocallyIntegrable (fun t => exp (-c*t)*j t) volume :=
  hj.continuous_mul (continuous_exp.comp (continuous_const.mul continuous_id))

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(exponentialPrimitive c j C) a b`.

Use: `chebyshev2.Filters.causal_locallyAC` uses this assertion to establish absolute
continuity on the specified interval: `AbsolutelyContinuousOnInterval (causal c j) a b`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.square_trace_cubic`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.exponentialForcing_locallyIntegrable` with the arguments shown in
the proof.
-/
theorem exponentialPrimitive_locallyAC {j : ℝ → ℝ} (hj : LocallyIntegrable j volume)
    (c C a b : ℝ) : AbsolutelyContinuousOnInterval (exponentialPrimitive c j C) a b := by
  -- Use the identities/estimates
  -- `chebyshev2.GroundState.exponentialForcing_locallyIntegrable` with the arguments shown
  -- in the proof.
  have hi : IntervalIntegrable (fun t => exp (-c*t)*j t) volume a b := by
    apply intervalIntegrable_iff.mpr
    exact ((exponentialForcing_locallyIntegrable hj c).integrableOn_isCompact isCompact_uIcc).mono_set
      uIoc_subset_uIcc
  have hi0 : IntervalIntegrable (fun t => exp (-c*t)*j t) volume 0 a := by
    apply intervalIntegrable_iff.mpr
    exact ((exponentialForcing_locallyIntegrable hj c).integrableOn_isCompact isCompact_uIcc).mono_set
      uIoc_subset_uIcc
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : a ∈ uIcc a b)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => C+∫ t in (0:ℝ)..a, exp (-c*t)*j t) a b :=
    (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => C+∫ t in (0:ℝ)..a, exp (-c*t)*j t)
      (uIcc a b)).absolutelyContinuousOnInterval
  have he : AbsolutelyContinuousOnInterval (fun x : ℝ => exp (c*x)) a b :=
    ((contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn :
      ContDiffOn ℝ 1 (fun x : ℝ => exp (c*x)) (uIcc a b)).absolutelyContinuousOnInterval
  apply (he.mul (hconst.add hp)).congr
  intro x _
  have hix : IntervalIntegrable (fun t => exp (-c*t)*j t) volume a x := by
    apply intervalIntegrable_iff.mpr
    exact ((exponentialForcing_locallyIntegrable hj c).integrableOn_isCompact isCompact_uIcc).mono_set
      uIoc_subset_uIcc
  change exp (c*x)*((C+∫ t in (0:ℝ)..a, exp (-c*t)*j t)+∫ t in a..x, exp (-c*t)*j t)=_
  rw [add_assoc, intervalIntegral.integral_add_adjacent_intervals hi0 hix]
  rfl

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(exponentialPrimitive c j C) (c*exponentialPrimitive c j C x+j x) x`.

Use: `chebyshev2.Filters.causal_derivative_ae` uses this assertion to establish establishes
the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (causal c j) (j x-c*causal
c j x) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem exponentialPrimitive_derivative_ae {j : ℝ → ℝ} (hj : LocallyIntegrable j volume)
    (c C : ℝ) : ∀ᵐ x, HasDerivAt (exponentialPrimitive c j C)
      (c*exponentialPrimitive c j C x+j x) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral (exponentialForcing_locallyIntegrable hj c)] with x hx
  have he := (hasDerivAt_exp (c*x)).comp x ((hasDerivAt_id x).const_mul c)
  have hp := (hasDerivAt_const x C).add (hx 0)
  have hd := he.mul hp
  change HasDerivAt (exponentialPrimitive c j C)
    ((exp (c*x)*(c*1))*(C+∫ t in (0:ℝ)..x, exp (-c*t)*j t)+exp (c*x)*(0+exp (-c*x)*j x)) x at hd
  convert hd using 1
  have he' : exp (c*x)*exp (-c*x)=1 := by rw [← exp_add]; simp
  dsimp [exponentialPrimitive]
  linear_combination -(j x)*he'

end
end chebyshev2.GroundState
