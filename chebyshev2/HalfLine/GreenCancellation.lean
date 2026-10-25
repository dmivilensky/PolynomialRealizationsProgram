import chebyshev2.HalfLine.GroundConvolution

/-!
Article: chebyshev2, Theorem 3.3.
On the left half-line the right tail of the full convolution cancels against its boundary
exponential.
Use: `chebyshev2.HalfLine.ground_green_equation` feeds
`chebyshev2.HalfLine.groundResolvent_vector` (ground Resolvent vector).
Proof chain: `chebyshev2.HalfLine.commonMeasure_ode_probability` — chebyshev2, Theorem 3.3; A
common compact probability measure for all scales.
-/
namespace chebyshev2.HalfLine
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.Sobolev chebyshev2.GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
On the left half-line the right tail of the full convolution cancels against its boundary
exponential. This uses no moment assumption on j.

The precise assertion is `greenSolution x j t= (H1.rep (convolution j) t-exp (t-x)*H1.rep
(convolution j) x)/2`.

Use: `chebyshev2.HalfLine.ground_green_equation` rewrites with this identity to establish
exact identity `H1.rep G.u t/H1.rep G.u x=exp (t-x)+groundParameter hm hn* greenSolution x (fun
y => m y*(H1.rep G.u y/H1.rep G.u x)) t`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Separate `y < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral.
-/
theorem greenSolution_full_convolution {j : ℝ → ℝ} (hj : Integrable j)
    {x t : ℝ} (ht : t ≤ x) : greenSolution x j t=
      (H1.rep (convolution j) t-exp (t-x)*H1.rep (convolution j) x)/2 := by
  -- Separate `y < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [greenSolution_integral hj, convolution_rep hj, convolution_rep hj,
    ← integral_const_mul, ← integral_sub (convolution_kernel_integrable hj t)
      ((convolution_kernel_integrable hj x).const_mul _), ← integral_div,
    ← integral_indicator measurableSet_Iio]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    change (Iio x).indicator (fun y => green x t y*j y) y=
      (exp (-|t-y|)*j y-exp (t-x)*(exp (-|x-y|)*j y))/2
    by_cases hy : y < x
    · rw [indicator_of_mem (show y ∈ Iio x from hy),abs_of_nonneg (sub_nonneg.mpr hy.le)]
      dsimp only [green]
      rw [← mul_assoc (exp (t-x)), ← exp_add]
      have he : t-x+-(x-y)=t+y-2*x := by ring
      rw [he]
      ring
    · have hxy : x ≤ y := le_of_not_gt hy
      rw [indicator_of_notMem (show y ∉ Iio x from hy),
        abs_of_nonpos (sub_nonpos.mpr (ht.trans hxy)), abs_of_nonpos (sub_nonpos.mpr hxy),
        ← mul_assoc (exp (t-x)), ← exp_add]
      have he : t-x+ -(-(x-y))= -(-(t-y)) := by ring
      rw [he]
      ring)

/--
Exact identity `greenSolution x (fun y => j y*c) t=greenSolution x j t*c`.

Use: `chebyshev2.HalfLine.ground_green_equation` rewrites with this identity to establish
exact identity `H1.rep G.u t/H1.rep G.u x=exp (t-x)+groundParameter hm hn* greenSolution x (fun
y => m y*(H1.rep G.u y/H1.rep G.u x)) t`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.greenSolution_integral` with the
arguments shown in the proof.
-/
theorem greenSolution_mul_const {j : ℝ → ℝ} (hj : Integrable j) (c x t : ℝ) :
    greenSolution x (fun y => j y*c) t=greenSolution x j t*c := by
  rw [greenSolution_integral (hj.mul_const c), greenSolution_integral hj, ← integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Iio
  intro y _
  change green x t y*(j y*c)=(green x t y*j y)*c
  ring

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t} (G : GroundWitness hm hn)
include G

/--
Exact identity `H1.rep G.u t/H1.rep G.u x=exp (t-x)+groundParameter hm hn* greenSolution x (fun
y => m y*(H1.rep G.u y/H1.rep G.u x)) t`.

Use: `chebyshev2.HalfLine.groundResolvent_vector` uses this identity to establish exact
identity `groundResolvent G x (vector hm hn x)=groundVector G x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem ground_green_equation {x t : ℝ} (ht : t ≤ x) :
    H1.rep G.u t/H1.rep G.u x=exp (t-x)+groundParameter hm hn*
      greenSolution x (fun y => m y*(H1.rep G.u y/H1.rep G.u x)) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have he : (fun y => m y*(H1.rep G.u y/H1.rep G.u x))=
      (fun y => (m y*H1.rep G.u y)*(H1.rep G.u x)⁻¹) := by funext y; ring
  rw [he, greenSolution_mul_const (density_rep_forcing_integrable hm G.u),
    greenSolution_full_convolution (density_rep_forcing_integrable hm G.u) ht]
  have h1 := ground_convolution G t
  have h2 := ground_convolution G x
  field_simp [(G.positive x).ne']
  linear_combination 2*h1-2*exp (t-x)*h2

end
end chebyshev2.HalfLine
