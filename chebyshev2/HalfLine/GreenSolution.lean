import chebyshev2.HalfLine.Kernel
import chebyshev2.GroundState.ConvolutionRegularity

/-!
Article: chebyshev2, Theorem 3.3.
The solution is the literal integral against the Dirichlet Green kernel.
Use: `chebyshev2.HalfLine.greenSolution_integral` feeds
`chebyshev2.HalfLine.jost_green_equation` (jost green equation).
Proof chain: `chebyshev2.HalfLine.commonMeasure_ode_probability` — chebyshev2, Theorem 3.3; A
common compact probability measure for all scales.
-/
namespace chebyshev2.HalfLine
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.Sobolev chebyshev2.GroundState
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
The C.1 Dirichlet Green solution, with a smooth extension past the endpoint.

Use: `chebyshev2.HalfLine.greenSolution_boundary` rewrites with this definition to
establish exact identity `greenSolution x j x=0`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.
-/
def greenSolution (x : ℝ) (j : ℝ → ℝ) (t : ℝ) : ℝ :=
  (H1.rep (convolution (leftDensity j x)) t-
    exp (t-x)*H1.rep (convolution (leftDensity j x)) x)/2

/--
Defines `greenSlope` of type `ℝ` by `(convolutionSlope (leftDensity j x) t- exp (t-x)*H1.rep
(convolution (leftDensity j x)) x)/2`.

Use: `chebyshev2.HalfLine.greenSlope_boundary` rewrites with this definition to establish
the precise assertion is `greenSlope x j x= -(∫ t in Iio x, exp (t-x)*j t)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.
-/
def greenSlope (x : ℝ) (j : ℝ → ℝ) (t : ℝ) : ℝ :=
  (convolutionSlope (leftDensity j x) t-
    exp (t-x)*H1.rep (convolution (leftDensity j x)) x)/2

/--
Exact identity `greenSolution x j x=0`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.3.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem greenSolution_boundary (x : ℝ) (j : ℝ → ℝ) : greenSolution x j x=0 := by simp [greenSolution]

/--
The actual derivative at the stated point: `HasDerivAt (greenSolution x j) (greenSlope x j t)
t`.

Use: `chebyshev2.HalfLine.greenElement_slope` uses this derivative formula to establish
exact identity `H1.slope (greenElement x j)=ᵐ[volume] (Iio x).indicator (greenSlope x j)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Proof: Use the identities/estimates `chebyshev2.GroundState.convolution_hasDerivAt`,
`chebyshev2.HalfLine.leftDensity_integrable` with the arguments shown in the proof.
-/
theorem greenSolution_hasDerivAt {j : ℝ → ℝ} (hj : Integrable j) (x t : ℝ) :
    HasDerivAt (greenSolution x j) (greenSlope x j t) t := by
  have he : HasDerivAt (fun t : ℝ => exp (t-x)) (exp (t-x)) t := by
    simpa only [id_eq, sub_zero, mul_one] using ((hasDerivAt_id t).sub_const x).exp
  exact ((convolution_hasDerivAt (leftDensity_integrable hj x) t).sub
    (he.mul_const _)).div_const 2

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (greenSlope x j)
a b`.

Use: `chebyshev2.HalfLine.greenSolution_c1` uses this assertion to establish smoothness to
the stated order: `ContDiff ℝ 1 (greenSolution x j)`.

Article: chebyshev2, Theorem 3.3.

Proof: Use the identities/estimates `chebyshev2.GroundState.convolutionSlope_locallyAC`,
`chebyshev2.HalfLine.leftDensity_integrable` with the arguments shown in the proof.
-/
theorem greenSlope_locallyAC {j : ℝ → ℝ} (hj : Integrable j) (x a b : ℝ) :
    AbsolutelyContinuousOnInterval (greenSlope x j) a b := by
  -- Use the identities/estimates `chebyshev2.GroundState.convolutionSlope_locallyAC`,
  -- `chebyshev2.HalfLine.leftDensity_integrable` with the arguments shown in the proof.
  have he : ContDiff ℝ 1 (fun t : ℝ => exp (t-x)*H1.rep (convolution (leftDensity j x)) x) := by
    fun_prop
  apply (((convolutionSlope_locallyAC (leftDensity_integrable hj x) a b).sub
    he.contDiffOn.absolutelyContinuousOnInterval).const_mul (1/2:ℝ)).congr
  intro t _
  change (1/2:ℝ)*(convolutionSlope (leftDensity j x) t-
    exp (t-x)*H1.rep (convolution (leftDensity j x)) x)=greenSlope x j t
  dsimp only [greenSlope]
  ring

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ t, HasDerivAt (greenSlope x
j) (greenSolution x j t-leftDensity j x t) t`.

Use: `chebyshev2.HalfLine.greenSolution_ode_of_integrableOn` uses this assertion to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ t ∂volume.restrict
(Iio x), HasDerivAt (greenSlope x j) (greenSolution x j t-j t) t`.

Article: chebyshev2, Theorem 3.3.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem greenSolution_second_derivative {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    ∀ᵐ t, HasDerivAt (greenSlope x j) (greenSolution x j t-leftDensity j x t) t := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [convolution_second_derivative_ae (leftDensity_integrable hj x)] with t ht
  have he : HasDerivAt (fun t : ℝ => exp (t-x)) (exp (t-x)) t := by
    simpa only [id_eq, sub_zero, mul_one] using ((hasDerivAt_id t).sub_const x).exp
  convert (ht.sub (he.mul_const (H1.rep (convolution (leftDensity j x)) x))).div_const 2 using 1
  · rfl
  · dsimp only [greenSolution]
    ring

/--
Exact identity `rightGreen (leftDensity j x) x=0`.

Use: `chebyshev2.HalfLine.greenSlope_boundary` rewrites with this identity to establish the
precise assertion is `greenSlope x j x= -(∫ t in Iio x, exp (t-x)*j t)`.

Article: chebyshev2, Theorem 3.3.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem rightGreen_leftDensity (x : ℝ) (j : ℝ → ℝ) : rightGreen (leftDensity j x) x=0 := by
  unfold rightGreen
  have he : (fun t => exp (-t)*leftDensity j x t)=ᵐ[volume.restrict (Ioi x)] (fun _ => (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change x < t at ht
    simp [leftDensity, not_lt.mpr ht.le]
  rw [integral_congr_ae he, integral_zero, mul_zero]

/--
The one-sided endpoint derivative in C.1, for arbitrary signed L1 data.

The precise assertion is `greenSlope x j x= -(∫ t in Iio x, exp (t-x)*j t)`.

Use: `chebyshev2.HalfLine.greenSlope_boundary_of_integrableOn` rewrites with this identity
to establish `greenSlope x j x= -(∫ t in Iio x, exp (t-x)*j t)`.

Article: chebyshev2, Theorem 3.3.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem greenSlope_boundary {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    greenSlope x j x= -(∫ t in Iio x, exp (t-x)*j t) := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [greenSlope, convolutionSlope, convolution_halves (leftDensity_integrable hj x),
    rightGreen_leftDensity]
  simp only [sub_self, exp_zero, one_mul, zero_sub, add_zero]
  have he : leftGreen (leftDensity j x) x=∫ t in Iio x, exp (t-x)*j t := by
    rw [leftGreen, ← integral_const_mul]
    have hi : (fun t => exp (-x)*(exp t*leftDensity j x t))=
        (Iio x).indicator (fun t => exp (t-x)*j t) := by
      funext t
      by_cases ht : t < x
      · simp only [leftDensity, indicator_of_mem (show t ∈ Iio x from ht)]
        rw [← mul_assoc, ← exp_add]
        congr 2
        ring
      · simp [leftDensity, ht]
    rw [hi, integral_indicator measurableSet_Iio]
    rw [Measure.restrict_restrict measurableSet_Iio, inter_eq_left.mpr Iio_subset_Iic_self]
  rw [he]
  ring

/--
The solution is the literal integral against the Dirichlet Green kernel.

Exact identity `greenSolution x j t=∫ y in Iio x, green x t y*j y`.

Use: `chebyshev2.HalfLine.greenSolution_full_convolution` rewrites with this identity to
establish the precise assertion is `greenSolution x j t= (H1.rep (convolution j) t-exp
(t-x)*H1.rep (convolution j) x)/2`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Separate `y < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral.
-/
theorem greenSolution_integral {j : ℝ → ℝ} (hj : Integrable j) (x t : ℝ) :
    greenSolution x j t=∫ y in Iio x, green x t y*j y := by
  -- Separate `y < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [greenSolution, convolution_rep (leftDensity_integrable hj x),
    convolution_rep (leftDensity_integrable hj x), ← integral_const_mul,
    ← integral_sub (convolution_kernel_integrable (leftDensity_integrable hj x) t)
      ((convolution_kernel_integrable (leftDensity_integrable hj x) x).const_mul _),
    ← integral_div, ← integral_indicator measurableSet_Iio]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    change (exp (-|t-y|)*leftDensity j x y-
      exp (t-x)*(exp (-|x-y|)*leftDensity j x y))/2=
      (Iio x).indicator (fun y => green x t y*j y) y
    by_cases hy : y < x
    · rw [leftDensity, indicator_of_mem (show y ∈ Iio x from hy),
        indicator_of_mem (show y ∈ Iio x from hy), abs_of_nonneg (sub_nonneg.mpr hy.le)]
      dsimp only [green]
      rw [← mul_assoc (exp (t-x)), ← exp_add]
      have he : t-x+-(x-y)=t+y-2*x := by ring
      rw [he]
      ring
    · simp [leftDensity,hy])

end
end chebyshev2.HalfLine
