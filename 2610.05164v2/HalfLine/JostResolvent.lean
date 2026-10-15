import «2610.05164v2».HalfLine.GreenVolterra

/-!
Article: 2610.05164v2, Theorem 3.3.
The all-scale ODE/resolvent bridge, including s=0 without cancellation.
Use: `«2610.05164v2».HalfLine.responseQuadratic_eq_nonlinear` feeds
`«2610.05164v2».HalfLine.commonMeasure_filter` (Theorem 3.3, with one actual measure for every
positive scale).
Proof chain: `«2610.05164v2».HalfLine.commonMeasure_filter` — 2610.05164v2, Theorem 3.3; A common
compact probability measure for all scales.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Continuum «2610.05164v2».GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Defines `jostProfile` of type `ℝ` by `exp (t-x)*Filters.jost s m t/Filters.jost s m x`.

Use: `«2610.05164v2».HalfLine.jostProfile_bound` rewrites with this definition to establish the
stated quantitative bound `‖jostProfile s m x t‖ ≤ 1`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.
-/
def jostProfile (s : ℝ) (m : ℝ → ℝ) (x t : ℝ) : ℝ :=
  exp (t-x)*Filters.jost s m t/Filters.jost s m x

/--
Continuity of the displayed function: `Continuous (jostProfile s m x)`.

Use: `«2610.05164v2».HalfLine.jost_green_equation` uses this continuity result to establish
exact identity `jostProfile s m x t+s*greenSolution x (fun z => leftDensity m x z*jostProfile s
m x z) t=exp (t-x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_continuous` with the arguments
shown in the proof.
-/
theorem jostProfile_continuous {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : Continuous (jostProfile s m x) :=
  ((by fun_prop : Continuous (fun t : ℝ => exp (t-x))).mul
    (Filters.jost_continuous hm hn hs)).div_const _

/--
The stated quantitative bound `‖jostProfile s m x t‖ ≤ 1`.

Use: `«2610.05164v2».HalfLine.jostVector` uses this bound in the displayed construction of
`jostVector`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_positive`,
`«2610.05164v2».Filters.jost_monotone` with the arguments shown in the proof.
-/
theorem jostProfile_bound {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) {x t : ℝ} (ht : t < x) : ‖jostProfile s m x t‖ ≤ 1 := by
  -- Use the identities/estimates `«2610.05164v2».Filters.jost_positive`,
  -- `«2610.05164v2».Filters.jost_monotone` with the arguments shown in the proof.
  have hpos : 0 ≤ jostProfile s m x t := div_nonneg
    (mul_nonneg (exp_pos _).le (Filters.jost_positive hm hn hs t).le)
    (Filters.jost_positive hm hn hs x).le
  rw [Real.norm_eq_abs, abs_of_nonneg hpos, jostProfile]
  apply (div_le_one (Filters.jost_positive hm hn hs x)).mpr
  exact (mul_le_of_le_one_left (Filters.jost_positive hm hn hs t).le
    (exp_le_one_iff.mpr (sub_nonpos.mpr ht.le))).trans (Filters.jost_monotone hm hn hs ht.le)

/--
Defines `jostVector` of type `FeatureSpace` by `weightedVector hm hn x (jostProfile_continuous
hm hn hs x).aestronglyMeasurable (fun _ ht => jostProfile_bound hm hn hs ht)`.

Use: `«2610.05164v2».HalfLine.responseQuadratic_eq_nonlinear` uses this definition to establish
exact identity `s*responseQuadratic (hm := hm) (hn := hn) x s hs=Filters.nonlinear s m x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.
-/
def jostVector {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : FeatureSpace := weightedVector hm hn x
  (jostProfile_continuous hm hn hs x).aestronglyMeasurable (fun _ ht => jostProfile_bound hm hn hs ht)

/--
Exact identity `jostProfile s m x t+s*greenSolution x (fun z => leftDensity m x z*jostProfile s
m x z) t=exp (t-x)`.

Use: `«2610.05164v2».HalfLine.positiveResolvent_vector` uses this identity to establish exact
identity `positiveResolvent (hm := hm) (hn := hn) x s hs (vector hm hn x)=jostVector hm hn hs
x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Separate `z < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral. Clear the denominators using the available nonzero hypotheses,
then verify the remaining algebraic identity.
-/
theorem jost_green_equation {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) {x t : ℝ} (ht : t < x) :
    jostProfile s m x t+s*greenSolution x (fun z => leftDensity m x z*jostProfile s m x z) t=exp (t-x) := by
  -- Separate `z < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hF := Filters.jost_forcing_integrable hm hn hs
  have hj := weighted_forcing_integrable hm hn x
    (jostProfile_continuous hm hn hs x).aestronglyMeasurable (fun _ hz => jostProfile_bound hm hn hs hz)
  have hg : greenSolution x (fun z => leftDensity m x z*jostProfile s m x z) t=
      exp (t-x)/(2*Filters.jost s m x)*
        ∫ z, (volterraKernel x z-volterraKernel t z)*(m z*Filters.jost s m z) := by
    rw [greenSolution_integral hj, ← integral_const_mul, ← integral_indicator measurableSet_Iio]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      have he := green_exp_volterraKernel ht.le z
      by_cases hz : z < x
      · rw [indicator_of_mem (show z ∈ Iio x from hz)] at he ⊢
        simp only [leftDensity,indicator_of_mem (show z ∈ Iio x from hz),jostProfile]
        field_simp [(Filters.jost_positive hm hn hs x).ne']
        linear_combination 2*m z*Filters.jost s m z*he
      · simp [leftDensity,hz,volterraKernel,not_lt.mpr (ht.le.trans (le_of_not_gt hz))])
  have hv : s*greenSolution x (fun z => leftDensity m x z*jostProfile s m x z) t=
      exp (t-x)/Filters.jost s m x*(Filters.volterra s m (Filters.jost s m) x-
        Filters.volterra s m (Filters.jost s m) t) := by
    rw [hg, volterra_full_integral hF, volterra_full_integral hF]
    have hi : (∫ z, (volterraKernel x z-volterraKernel t z)*(m z*Filters.jost s m z))=
        (∫ z, volterraKernel x z*(m z*Filters.jost s m z))-
          ∫ z, volterraKernel t z*(m z*Filters.jost s m z) := by
      rw [← integral_sub (volterraKernel_mul_integrable hF x) (volterraKernel_mul_integrable hF t)]
      congr 1
      funext z
      ring
    rw [hi]
    ring
  rw [hv,jostProfile]
  have hx := Filters.jost_equation hm hn hs x
  have htx := Filters.jost_equation hm hn hs t
  field_simp [(Filters.jost_positive hm hn hs x).ne']
  linear_combination htx-hx

/--
Exact identity `positiveResolvent (hm := hm) (hn := hn) x s hs (vector hm hn x)=jostVector hm
hn hs x`.

Use: `«2610.05164v2».HalfLine.responseQuadratic_eq_nonlinear` rewrites with this identity to
establish exact identity `s*responseQuadratic (hm := hm) (hn := hn) x s hs=Filters.nonlinear s
m x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.inverseOfUnit_apply_of_eq`,
`«2610.05164v2».HalfLine.pencil_of_green_equation`,
`«2610.05164v2».HalfLine.jostProfile_continuous` with the arguments shown in the proof.
-/
theorem positiveResolvent_vector {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    positiveResolvent (hm := hm) (hn := hn) x s hs (vector hm hn x)=jostVector hm hn hs x := by
  apply inverseOfUnit_apply_of_eq
  exact pencil_of_green_equation hm hn x
    (jostProfile_continuous hm hn hs x).aestronglyMeasurable
    (fun _ ht => jostProfile_bound hm hn hs ht) s (fun _ ht => jost_green_equation hm hn hs ht)

/--
The all-scale ODE/resolvent bridge, including s=0 without cancellation.

Exact identity `s*responseQuadratic (hm := hm) (hn := hn) x s hs=Filters.nonlinear s m x`.

Use: `«2610.05164v2».HalfLine.commonMeasure_filter` uses this identity to establish the precise
assertion is `groundParameter hm hn*Filters.nonlinear s m x/(s*G.q x)= ∫ z,
(1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure G x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem responseQuadratic_eq_nonlinear {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    s*responseQuadratic (hm := hm) (hn := hn) x s hs=Filters.nonlinear s m x := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  rw [responseQuadratic,positiveResolvent_vector hm hn hs x]
  unfold jostVector
  rw [vector_weighted_inner]
  have he : (fun t => exp (t-x)*(m t*jostProfile s m x t))=
      (fun t => exp (-2*x)*(exp (2*t)*(m t*Filters.jost s m t))/Filters.jost s m x) := by
    funext t
    dsimp only [jostProfile]
    have hex : exp (t-x)*exp (t-x)=exp (-2*x)*exp (2*t) := by
      rw [← exp_add, ← exp_add]
      congr 1
      ring
    linear_combination m t*Filters.jost s m t/Filters.jost s m x*hex
  rw [he, integral_div, integral_const_mul, ← integral_Iic_eq_integral_Iio]
  dsimp only [Filters.nonlinear, Filters.jostSlope, Filters.causal]
  ring

end
end «2610.05164v2».HalfLine
