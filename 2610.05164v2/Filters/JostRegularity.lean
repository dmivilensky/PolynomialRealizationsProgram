import «2610.05164v2».Filters.VolterraEquation

/-!
Article: 2610.05164v2, Proposition 3.
Jost Regularity.
Use: `«2610.05164v2».Filters.jost_monotone` feeds
`«2610.05164v2».LocalObstruction.jostFunction_growth` (jost Function growth).
Proof chain: `«2610.05164v2».HalfLine.commonMeasure_filter` — 2610.05164v2, Theorem 3.3; A common
compact probability measure for all scales.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `jostSlope` of type `ℝ` by `s*causal 2 (fun t => m t*jost s m t) x`.

Use: `«2610.05164v2».Filters.jost_c1` uses this definition to establish smoothness to the
stated order: `ContDiff ℝ 1 (jost s m)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.
-/
def jostSlope (s : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ := s*causal 2 (fun t => m t*jost s m t) x

/--
The actual derivative at the stated point: `HasDerivAt (jost s m) (jostSlope s m x) x`.

Use: `«2610.05164v2».Filters.jost_c1` uses this derivative formula to establish smoothness to
the stated order: `ContDiff ℝ 1 (jost s m)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem jost_hasDerivAt {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : HasDerivAt (jost s m) (jostSlope s m x) x := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have h := (hasDerivAt_const x (1:ℝ)).add (volterra_hasDerivAt (jost_forcing_integrable hm hn hs) s x)
  have he : (fun x => 1+volterra s m (jost s m) x)=jost s m :=
    funext (fun x => (jost_equation hm hn hs x).symm)
  change HasDerivAt (fun x => 1+volterra s m (jost s m) x)
    (0+s*causal 2 (fun t => m t*jost s m t) x) x at h
  rw [he] at h
  simpa only [jostSlope,zero_add] using h

/--
Continuity of the displayed function: `Continuous (jostSlope s m)`.

Use: `«2610.05164v2».Filters.jost_c1` uses this continuity result to establish smoothness to
the stated order: `ContDiff ℝ 1 (jost s m)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_continuous`,
`«2610.05164v2».Filters.jost_forcing_integrable` with the arguments shown in the proof.
-/
theorem jostSlope_continuous {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Continuous (jostSlope s m) :=
  continuous_const.mul (causal_continuous (by norm_num : (0:ℝ) ≤ 2) (jost_forcing_integrable hm hn hs))

/--
Smoothness to the stated order: `ContDiff ℝ 1 (jost s m)`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_continuousOn` uses this assertion
to establish continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ =>
P.determinantPotential hκ s p.1 p.2) (filterTriangle (s/κ))`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem jost_c1 {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : ContDiff ℝ 1 (jost s m) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (jost_hasDerivAt hm hn hs x).differentiableAt,?_⟩
  have he : deriv (jost s m)=jostSlope s m := funext (fun x => (jost_hasDerivAt hm hn hs x).deriv)
  rw [he]
  exact jostSlope_continuous hm hn hs

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (jostSlope s m)
a b`.

Use: `«2610.05164v2».Filters.jostFunctionSlope_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(jostFunctionSlope s m) a b`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_locallyAC`,
`«2610.05164v2».Filters.jost_forcing_integrable` with the arguments shown in the proof.
-/
theorem jostSlope_locallyAC {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (a b : ℝ) : AbsolutelyContinuousOnInterval (jostSlope s m) a b :=
  (causal_locallyAC (by norm_num : (0:ℝ) ≤ 2) (jost_forcing_integrable hm hn hs) a b).const_mul s

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (jostSlope s
m) (s*m x*jost s m x-2*jostSlope s m x) x`.

Use: `«2610.05164v2».Filters.jostFunction_ode` uses this assertion to establish establishes the
stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (jostFunctionSlope s m)
((1+s*m x)*jostFunction s m x) x`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem jost_second_derivative {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ x, HasDerivAt (jostSlope s m) (s*m x*jost s m x-2*jostSlope s m x) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [causal_derivative_ae (by norm_num : (0:ℝ) ≤ 2) (jost_forcing_integrable hm hn hs)] with x hx
  have h := hx.const_mul s
  change HasDerivAt (jostSlope s m) (s*(m x*jost s m x-2*causal 2 (fun t => m t*jost s m t) x)) x at h
  convert h using 1
  dsimp [jostSlope]
  ring

/--
The stated quantitative bound `0 ≤ jostSlope s m x`.

Use: `«2610.05164v2».Filters.jost_monotone` uses this bound to establish monotonicity in
increasing order: `Monotone (jost s m)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_nonneg`,
`«2610.05164v2».Filters.jost_positive` with the arguments shown in the proof.
-/
theorem jostSlope_nonneg {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : 0 ≤ jostSlope s m x :=
  mul_nonneg hs (causal_nonneg (Eventually.of_forall (fun t => mul_nonneg (hn t) (jost_positive hm hn hs t).le)) x)

/--
Monotonicity in increasing order: `Monotone (jost s m)`.

Use: `«2610.05164v2».Filters.nonlinear_bounds` uses this assertion to establish membership in
the specified domain/enclosure: `nonlinear s m x ∈ Icc (0:ℝ) (s*causal 2 m x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_hasDerivAt`,
`«2610.05164v2».Filters.jostSlope_nonneg` with the arguments shown in the proof.
-/
theorem jost_monotone {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Monotone (jost s m) :=
  monotone_of_hasDerivAt_nonneg (jost_hasDerivAt hm hn hs) (jostSlope_nonneg hm hn hs)

end
end «2610.05164v2».Filters
