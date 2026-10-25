import chebyshev2.HalfLine.BoundaryResolvent
import chebyshev2.HalfLine.GreenCancellation

/-!
Article: chebyshev2, Theorem 3.3.
The missing analytic identification in Theorem 3.3: q is the actual negative-scale resolvent
quadratic form, not a newly defined coordinate.
Use: `chebyshev2.HalfLine.groundQuadratic_eq_coordinate` feeds
`chebyshev2.HalfLine.commonMeasure_filter` (Theorem 3.3, with one actual measure for every
positive scale).
Proof chain: `chebyshev2.HalfLine.commonMeasure_ode_probability` — chebyshev2, Theorem 3.3; A
common compact probability measure for all scales.
-/
namespace chebyshev2.HalfLine
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.Sobolev chebyshev2.GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `greenSolution x (fun z => leftDensity m x z*y z) t=greenSolution x (fun z => m
z*y z) t`.

Use: `chebyshev2.HalfLine.groundResolvent_vector` rewrites with this identity to establish
exact identity `groundResolvent G x (vector hm hn x)=groundVector G x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Separate `z < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem greenSolution_left_forcing {m y : ℝ → ℝ} (hj : Integrable (fun t => m t*y t)) (x t : ℝ) :
    greenSolution x (fun z => leftDensity m x z*y z) t=greenSolution x (fun z => m z*y z) t := by
  -- Separate `z < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have he : (fun z => leftDensity m x z*y z)=leftDensity (fun z => m z*y z) x := by
    funext z
    by_cases hz : z < x <;> simp [leftDensity,hz]
  rw [he, greenSolution_integral (leftDensity_integrable hj x), greenSolution_integral hj]
  apply setIntegral_congr_fun measurableSet_Iio
  intro z hz
  change green x t z*leftDensity (fun z => m z*y z) x z=green x t z*(m z*y z)
  rw [leftDensity,indicator_of_mem hz]

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t} (G : GroundWitness hm hn)

/--
Defines `groundProfile` of type `ℝ` by `H1.rep G.u t/H1.rep G.u x`.

Use: `chebyshev2.HalfLine.groundProfile_bound` rewrites with this definition to establish
the stated quantitative bound `‖groundProfile G x t‖ ≤ (‖G.u‖/sqrt 2)/H1.rep G.u x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.groundProfile_boundary`.
-/
def groundProfile (x t : ℝ) : ℝ := H1.rep G.u t/H1.rep G.u x

/--
Continuity of the displayed function: `Continuous (groundProfile G x)`.

Use: `chebyshev2.HalfLine.groundResolvent_vector` uses this continuity result to establish
exact identity `groundResolvent G x (vector hm hn x)=groundVector G x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `chebyshev2.Sobolev.H1.continuous_rep` with the
arguments shown in the proof.
-/
theorem groundProfile_continuous (x : ℝ) : Continuous (groundProfile G x) :=
  (H1.continuous_rep G.u).div_const _

/--
The stated quantitative bound `‖groundProfile G x t‖ ≤ (‖G.u‖/sqrt 2)/H1.rep G.u x`.

Use: `chebyshev2.HalfLine.groundResolvent_vector` uses this bound to establish exact
identity `groundResolvent G x (vector hm hn x)=groundVector G x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `chebyshev2.Sobolev.H1.evaluation_bound` with the
arguments shown in the proof.
-/
theorem groundProfile_bound (x t : ℝ) : ‖groundProfile G x t‖ ≤ (‖G.u‖/sqrt 2)/H1.rep G.u x := by
  simp only [groundProfile, norm_div, Real.norm_eq_abs, abs_of_pos (G.positive x)]
  exact div_le_div_of_nonneg_right (H1.evaluation_bound G.u t) (G.positive x).le

/--
Defines `groundVector` of type `FeatureSpace` by `weightedVector hm hn x
(groundProfile_continuous G x).aestronglyMeasurable (fun t _ => groundProfile_bound G x t)`.

Use: `chebyshev2.HalfLine.groundQuadratic_eq_coordinate` uses this definition to establish
exact identity `groundQuadratic G x=G.q x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.
-/
def groundVector (x : ℝ) : FeatureSpace := weightedVector hm hn x
  (groundProfile_continuous G x).aestronglyMeasurable (fun t _ => groundProfile_bound G x t)

/--
Exact identity `groundResolvent G x (vector hm hn x)=groundVector G x`.

Use: `chebyshev2.HalfLine.groundQuadratic_eq_coordinate` rewrites with this identity to
establish exact identity `groundQuadratic G x=G.q x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.inverseOfUnit_apply_of_eq`,
`chebyshev2.HalfLine.pencil_of_green_equation`,
`chebyshev2.HalfLine.groundProfile_continuous` with the arguments shown in the proof.
-/
theorem groundResolvent_vector (x : ℝ) : groundResolvent G x (vector hm hn x)=groundVector G x := by
  -- Use the identities/estimates `chebyshev2.HalfLine.inverseOfUnit_apply_of_eq`,
  -- `chebyshev2.HalfLine.pencil_of_green_equation`,
  -- `chebyshev2.HalfLine.groundProfile_continuous` with the arguments shown in the proof.
  apply inverseOfUnit_apply_of_eq
  apply pencil_of_green_equation hm hn x
    (groundProfile_continuous G x).aestronglyMeasurable (fun t _ => groundProfile_bound G x t)
  intro t ht
  -- Establish hj as the integrability justification for the later integral estimates or
  -- changes of order.
  have hj : Integrable (fun t => m t*groundProfile G x t) := by
    apply Filters.bounded_forcing_integrable hm (groundProfile_continuous G x).aestronglyMeasurable
    exact groundProfile_bound G x
  rw [greenSolution_left_forcing hj]
  have he := ground_green_equation G ht.le
  change H1.rep G.u t/H1.rep G.u x+ -groundParameter hm hn*
    greenSolution x (fun y => m y*(H1.rep G.u y/H1.rep G.u x)) t=exp (t-x)
  linarith

/--
The missing analytic identification in Theorem 3.3: q is the actual negative-scale resolvent
quadratic form, not a newly defined coordinate.

Exact identity `groundQuadratic G x=G.q x`.

Use: `chebyshev2.HalfLine.commonMeasure_defect` rewrites with this identity to establish
exact identity `Filters.defect G x/G.q x=∫ z, z ∂commonMeasure G x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem groundQuadratic_eq_coordinate (x : ℝ) : groundQuadratic G x=G.q x := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  rw [groundQuadratic, groundResolvent_vector G x]
  unfold groundVector
  rw [vector_weighted_inner, ground_boundary_flux G x]
  have he : (fun t => exp (t-x)*(m t*groundProfile G x t))=
      (fun t => exp (t-x)*(m t*H1.rep G.u t)/H1.rep G.u x) := by
    funext t
    dsimp only [groundProfile]
    ring
  rw [he, integral_div, leftGreen, ← integral_const_mul, integral_Iic_eq_integral_Iio]
  have he' : (fun t => exp (-x)*(exp t*(m t*H1.rep G.u t)))=
      (fun t => exp (t-x)*(m t*H1.rep G.u t)) := by
    funext t
    rw [← mul_assoc (exp (-x)), ← exp_add]
    congr 2
    ring
  rw [he']
  ring

end
end chebyshev2.HalfLine
