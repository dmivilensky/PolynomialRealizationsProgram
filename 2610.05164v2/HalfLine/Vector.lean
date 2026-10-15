import «2610.05164v2».HalfLine.Operator
import «2610.05164v2».Filters.GroundComparison

/-!
Article: 2610.05164v2, Theorem 3.3.
The literal relation r-circle = kappa ||v_x||² from Theorem 3.3.
Use: `«2610.05164v2».HalfLine.linear_eq_vector_norm` feeds `«2610.05164v2».HalfLine.zero_quadratics`
(zero quadratics).
Proof chain: `«2610.05164v2».HalfLine.commonMeasure_linear_filter` — 2610.05164v2, Theorem 3.3; A
common compact probability measure for all scales.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Continuum «2610.05164v2».Sobolev «2610.05164v2».GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `vector hm hn x =ᵐ[volume] (fun t => sqrt (leftDensity m x t)*exp
(t-x))`.

Use: `«2610.05164v2».HalfLine.pencil_of_green_equation` uses this identity to establish exact
identity `(ContinuousLinearMap.id ℝ FeatureSpace+s • operator hm hn x) (weightedVector hm hn x
hy hC)=vector hm hn x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem vector_coe_density {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    vector hm hn x =ᵐ[volume] (fun t => sqrt (leftDensity m x t)*exp (t-x)) := by
  filter_upwards [vector_coe hm hn x] with t ht
  rw [ht]
  by_cases hx : t < x <;> simp [leftDensity,hx]

/--
Exact identity `‖vector hm hn x‖^2=Filters.causal 2 m x`.

Use: `«2610.05164v2».HalfLine.linear_eq_vector_norm` rewrites with this identity to establish
exact identity `Filters.linear hm hn x=groundParameter hm hn*‖vector hm hn x‖^2`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_linear_filter`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Identify the summands/integrands
on their required domain before replacing the sum or integral.
-/
theorem vector_norm_sq {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    ‖vector hm hn x‖^2=Filters.causal 2 m x := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  have he : (fun t => inner ℝ (vector hm hn x t) (vector hm hn x t)) =ᵐ[volume]
      (Iio x).indicator (fun t => m t*exp (-2*(x-t))) := by
    filter_upwards [vector_coe hm hn x] with t ht
    rw [ht]
    by_cases hx : t < x
    · rw [indicator_of_mem (show t ∈ Iio x from hx),indicator_of_mem (show t ∈ Iio x from hx)]
      simp only [RCLike.inner_apply,conj_trivial]
      have hsq : (sqrt (m t)*exp (t-x))^2=m t*exp (-2*(x-t)) := by
        rw [mul_pow,sq_sqrt (hn t),← exp_nat_mul]
        congr 2
        ring
      nlinarith only [hsq]
    · simp [hx]
  rw [integral_congr_ae he,integral_indicator measurableSet_Iio,← integral_Iic_eq_integral_Iio,
    Filters.causal_integral]
  have he' : (fun t => Filters.kernel 2 x t*m t)=
      (Iic x).indicator (fun t => m t*exp (-2*(x-t))) := by
    funext t
    by_cases ht : t ≤ x <;> simp [Filters.kernel,ht,mul_comm]
  rw [he',integral_indicator measurableSet_Iic]

/--
The literal relation r-circle = kappa ||v_x||² from Theorem 3.3.

Exact identity `Filters.linear hm hn x=groundParameter hm hn*‖vector hm hn x‖^2`.

Use: `«2610.05164v2».HalfLine.commonMeasure_linear_filter` uses this identity to establish
exact identity `Filters.linear hm hn x/G.q x=∫ z, 1-z ∂commonMeasure G x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_linear_filter`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.vector_norm_sq` with the arguments
shown in the proof.
-/
theorem linear_eq_vector_norm {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    Filters.linear hm hn x=groundParameter hm hn*‖vector hm hn x‖^2 := by
  rw [vector_norm_sq]
  rfl

end
end «2610.05164v2».HalfLine
