import chebyshev2.HalfLine.BoundaryResolvent
import chebyshev2.Filters.Nonlinear

/-!
Article: chebyshev2, Theorem 3.3.
Green Volterra.
Use: `chebyshev2.HalfLine.green_exp_volterraKernel` feeds
`chebyshev2.HalfLine.jost_green_equation` (jost green equation).
Proof chain: `chebyshev2.HalfLine.commonMeasure_filter` — chebyshev2, Theorem 3.3; A common
compact probability measure for all scales.
-/
namespace chebyshev2.HalfLine
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Defines `volterraKernel` of type `ℝ → ℝ` by `(Iio x).indicator (fun z => 1-exp (-2*(x-z)))`.

Use: `chebyshev2.HalfLine.green_exp_volterraKernel` rewrites with this definition to
establish the stated quantitative bound `(Iio x).indicator (fun z => green x t z*exp (z-x)) z=
exp (t-x)/2*(volterraKernel x z-volterraKernel t z)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_filter`.
-/
def volterraKernel (x : ℝ) : ℝ → ℝ := (Iio x).indicator (fun z => 1-exp (-2*(x-z)))

/--
Integrability of the displayed function: `Integrable (fun z => volterraKernel x z*F z)`.

Use: `chebyshev2.HalfLine.jost_green_equation` rewrites with this integrability result to
establish exact identity `jostProfile s m x t+s*greenSolution x (fun z => leftDensity m x
z*jostProfile s m x z) t=exp (t-x)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_filter`.

Proof: Separate `z < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem volterraKernel_mul_integrable {F : ℝ → ℝ} (hF : Integrable F) (x : ℝ) :
    Integrable (fun z => volterraKernel x z*F z) := by
  -- Separate `z < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply hF.norm.mono'
  · exact (((by fun_prop : Continuous (fun z : ℝ => 1-exp (-2*(x-z)))).measurable.indicator
      measurableSet_Iio).aestronglyMeasurable).mul hF.aestronglyMeasurable
  · exact Eventually.of_forall (fun z => by
      change ‖volterraKernel x z*F z‖ ≤ ‖F z‖
      by_cases hz : z < x
      · have he : exp (-2*(x-z)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
        rw [volterraKernel, indicator_of_mem (show z ∈ Iio x from hz),norm_mul,
          Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr he)]
        exact mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ (exp_pos _).le)
      · simp [volterraKernel,hz])

/--
Exact identity `Filters.volterra s m f x=s/2*∫ z, volterraKernel x z*(m z*f z)`.

Use: `chebyshev2.HalfLine.jost_green_equation` rewrites with this identity to establish
exact identity `jostProfile s m x t+s*greenSolution x (fun z => leftDensity m x z*jostProfile s
m x z) t=exp (t-x)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_filter`.

Proof: Separate `z < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral.
-/
theorem volterra_full_integral {m f : ℝ → ℝ} (hj : Integrable (fun z => m z*f z)) (s x : ℝ) :
    Filters.volterra s m f x=s/2*∫ z, volterraKernel x z*(m z*f z) := by
  rw [Filters.volterra_integral hj, integral_Iic_eq_integral_Iio]
  congr 1
  rw [← integral_indicator measurableSet_Iio]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    by_cases hz : z < x <;> simp [volterraKernel,hz,mul_assoc])

/--
The stated quantitative bound `(Iio x).indicator (fun z => green x t z*exp (z-x)) z= exp
(t-x)/2*(volterraKernel x z-volterraKernel t z)`.

Use: `chebyshev2.HalfLine.jost_green_equation` uses this identity to establish exact
identity `jostProfile s m x t+s*greenSolution x (fun z => leftDensity m x z*jostProfile s m x
z) t=exp (t-x)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_filter`.

Proof: Separate `z < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem green_exp_volterraKernel {x t : ℝ} (ht : t ≤ x) (z : ℝ) :
    (Iio x).indicator (fun z => green x t z*exp (z-x)) z=
      exp (t-x)/2*(volterraKernel x z-volterraKernel t z) := by
  -- Separate `z < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hzx : z < x
  · rw [indicator_of_mem (show z ∈ Iio x from hzx),volterraKernel,
      indicator_of_mem (show z ∈ Iio x from hzx)]
    have he2 : exp (t+z-2*x)*exp (z-x)=exp (t-x)*exp (-2*(x-z)) := by
      rw [← exp_add, ← exp_add]
      congr 1
      ring
    by_cases hzt : z < t
    · rw [volterraKernel, indicator_of_mem (show z ∈ Iio t from hzt)]
      have he1 : exp (-|t-z|)*exp (z-x)=exp (t-x)*exp (-2*(t-z)) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hzt.le), ← exp_add, ← exp_add]
        congr 1
        ring
      dsimp only [green]
      linear_combination he1/2-he2/2
    · rw [volterraKernel, indicator_of_notMem (show z ∉ Iio t from hzt)]
      have he1 : exp (-|t-z|)*exp (z-x)=exp (t-x) := by
        rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt hzt)), ← exp_add]
        congr 1
        ring
      dsimp only [green]
      linear_combination he1/2-he2/2
  · have hzt : ¬ z < t := fun h => hzx (h.trans_le ht)
    simp [volterraKernel,hzx,hzt]

end
end chebyshev2.HalfLine
