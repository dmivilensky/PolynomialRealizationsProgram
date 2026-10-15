import «2610.05164v2».Filters.Cumulative

/-!
Article: 2610.05164v2, Theorem 3.4.
This is the literal Volterra kernel in Proposition 3(ii).
Use: `«2610.05164v2».Filters.volterra_integral` feeds
`«2610.05164v2».HalfLine.volterra_full_integral` (volterra full integral).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `volterra` of type `ℝ` by `s/2*(cumulative (fun t => m t*f t) x-causal 2 (fun t => m
t*f t) x)`.

Use: `«2610.05164v2».Filters.volterra_bounds` uses this definition to establish the stated
quantitative bound `volterra s m f x ∈ Icc (0:ℝ) (s/2*cumulative (fun t => m t*f t) x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.
-/
def volterra (s : ℝ) (m f : ℝ → ℝ) (x : ℝ) : ℝ :=
  s/2*(cumulative (fun t => m t*f t) x-causal 2 (fun t => m t*f t) x)

/--
The stated quantitative bound `causal 2 j x ≤ cumulative j x`.

Use: `«2610.05164v2».Filters.volterra_bounds` uses this bound to establish the stated
quantitative bound `volterra s m f x ∈ Icc (0:ℝ) (s/2*cumulative (fun t => m t*f t) x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.forcing_integrable` with the
arguments shown in the proof.
-/
theorem causal_le_cumulative {j : ℝ → ℝ} (hj : Integrable j) (hn : ∀ t, 0 ≤ j t) (x : ℝ) :
    causal 2 j x ≤ cumulative j x := by
  -- Use the identities/estimates `«2610.05164v2».Filters.forcing_integrable` with the
  -- arguments shown in the proof.
  rw [causal,← integral_const_mul]
  apply setIntegral_mono_on ((forcing_integrable (by norm_num : (0:ℝ) ≤ 2) hj x).const_mul _)
    hj.integrableOn measurableSet_Iic
  intro t ht
  rw [← mul_assoc,← exp_add]
  have he : exp (-2*x+2*t) ≤ 1 := exp_le_one_iff.mpr (by change t ≤ x at ht; linarith)
  exact mul_le_of_le_one_left (hn t) he

/--
The stated quantitative bound `volterra s m f x ∈ Icc (0:ℝ) (s/2*cumulative (fun t => m t*f t)
x)`.

Use: `«2610.05164v2».Filters.volterraTerm_properties` uses this identity to establish
continuity of the displayed function: `Continuous (volterraTerm s m n) ∧ ∀ x, volterraTerm s m
n x ∈ Icc (0:ℝ) (factorialBound s (cumulative m x) n)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_le_cumulative`,
`«2610.05164v2».Filters.causal_nonneg` with the arguments shown in the proof.
-/
theorem volterra_bounds {m f : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hj : Integrable (fun t => m t*f t)) (hn : ∀ t, 0 ≤ m t*f t) (x : ℝ) :
    volterra s m f x ∈ Icc (0:ℝ) (s/2*cumulative (fun t => m t*f t) x) := by
  constructor
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr (causal_le_cumulative hj hn x))
  · have h := causal_nonneg (c := 2) (Eventually.of_forall hn) x
    dsimp [volterra]
    nlinarith

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (volterra s m f)
a b`.

Use: `«2610.05164v2».Filters.volterra_continuous` uses this assertion to establish continuity
of the displayed function: `Continuous (volterra s m f)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.cumulative_locallyAC`,
`«2610.05164v2».Filters.causal_locallyAC` with the arguments shown in the proof.
-/
theorem volterra_locallyAC {m f : ℝ → ℝ} (hj : Integrable (fun t => m t*f t))
    (s a b : ℝ) : AbsolutelyContinuousOnInterval (volterra s m f) a b :=
  ((cumulative_locallyAC hj a b).sub (causal_locallyAC (by norm_num : (0:ℝ) ≤ 2) hj a b)).const_mul _

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (volterra s m
f) (s*causal 2 (fun t => m t*f t) x) x`.

Use: `«2610.05164v2».Filters.volterra_hasDerivAt` uses this identity to establish the actual
derivative at the stated point: `HasDerivAt (volterra s m f) (s*causal 2 (fun t => m t*f t) x)
x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem volterra_derivative_ae {m f : ℝ → ℝ} (hj : Integrable (fun t => m t*f t)) (s : ℝ) :
    ∀ᵐ x, HasDerivAt (volterra s m f) (s*causal 2 (fun t => m t*f t) x) x := by
  filter_upwards [cumulative_derivative hj,causal_derivative_ae (by norm_num : (0:ℝ) ≤ 2) hj] with x hM hC
  have hd := (hM.sub hC).const_mul (s/2)
  change HasDerivAt (volterra s m f) (s/2*(m x*f x-(m x*f x-2*causal 2 (fun t => m t*f t) x))) x at hd
  convert hd using 1
  ring

/--
The actual derivative at the stated point: `HasDerivAt (volterra s m f) (s*causal 2 (fun t => m
t*f t) x) x`.

Use: `«2610.05164v2».Filters.jost_hasDerivAt` uses this derivative formula to establish the
actual derivative at the stated point: `HasDerivAt (jost s m) (jostSlope s m x) x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.locallyAC_hasDerivAt_of_continuous`,
`«2610.05164v2».Filters.volterra_locallyAC`, `«2610.05164v2».Filters.volterra_derivative_ae`
with the arguments shown in the proof.
-/
theorem volterra_hasDerivAt {m f : ℝ → ℝ} (hj : Integrable (fun t => m t*f t)) (s x : ℝ) :
    HasDerivAt (volterra s m f) (s*causal 2 (fun t => m t*f t) x) x :=
  locallyAC_hasDerivAt_of_continuous (volterra_locallyAC hj s) (volterra_derivative_ae hj s)
    (continuous_const.mul (causal_continuous (by norm_num : (0:ℝ) ≤ 2) hj)) x

/--
Continuity of the displayed function: `Continuous (volterra s m f)`.

Use: `«2610.05164v2».Filters.jost_unique` uses this continuity result to establish exact
identity `w=jost s m`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.locallyAC_continuous`,
`«2610.05164v2».Filters.volterra_locallyAC` with the arguments shown in the proof.
-/
theorem volterra_continuous {m f : ℝ → ℝ} (hj : Integrable (fun t => m t*f t)) (s : ℝ) :
    Continuous (volterra s m f) := locallyAC_continuous (volterra_locallyAC hj s)

/--
Integrability of the displayed function: `Integrable (fun t => m t*f t)`.

Use: `«2610.05164v2».Filters.jost_equation` uses this integrability result to establish exact
identity `jost s m x=1+volterra s m (jost s m) x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem bounded_forcing_integrable {m f : ℝ → ℝ} (hm : Integrable m)
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hC : ∀ t, ‖f t‖ ≤ C) :
    Integrable (fun t => m t*f t) := by
  apply (hm.norm.mul_const C).mono' (hm.aestronglyMeasurable.mul hf)
  exact Eventually.of_forall (fun t => by
    change ‖m t*f t‖ ≤ ‖m t‖*C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC t) (norm_nonneg _))

/--
This is the literal Volterra kernel in Proposition 3(ii).

Exact identity `volterra s m f x=s/2*∫ t in Iic x, (1-exp (-2*(x-t)))*m t*f t`.

Use: `«2610.05164v2».Filters.jost_equation` rewrites with this identity to establish exact
identity `jost s m x=1+volterra s m (jost s m) x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.forcing_integrable` with the
arguments shown in the proof.
-/
theorem volterra_integral {m f : ℝ → ℝ} (hj : Integrable (fun t => m t*f t)) (s x : ℝ) :
    volterra s m f x=s/2*∫ t in Iic x, (1-exp (-2*(x-t)))*m t*f t := by
  -- Use the identities/estimates `«2610.05164v2».Filters.forcing_integrable` with the
  -- arguments shown in the proof.
  unfold volterra cumulative causal
  congr 1
  rw [← integral_const_mul,← integral_sub hj.integrableOn
    ((forcing_integrable (by norm_num : (0:ℝ) ≤ 2) hj x).const_mul _)]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  change m t*f t-exp (-2*x)*(exp (2*t)*(m t*f t))=(1-exp (-2*(x-t)))*m t*f t
  rw [← mul_assoc (exp (-2*x)),← exp_add]
  have he : -2*x+2*t = -2*(x-t) := by ring
  rw [he]
  ring

end
end «2610.05164v2».Filters
