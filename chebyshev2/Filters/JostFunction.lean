import chebyshev2.Filters.OutsideSupport

/-!
Article: chebyshev2, Lemma 11.
The actual second-order Jost equation in Proposition 3(ii).
Use: `chebyshev2.Filters.jostFunction_ode` feeds
`chebyshev2.LocalObstruction.jostFunctionSlope_derivative` (jost Function Slope derivative).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `jostFunction` of type `ℝ` by `exp x*jost s m x`.

Use: `chebyshev2.Filters.jostFunction_asymptotic` uses this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun x =>
jostFunction s m x/exp x) atBot (𝓝 1)`.

Article: chebyshev2, Lemma 11 via `chebyshev2.Comparison.Profile.rightJost_ode`.
-/
def jostFunction (s : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ := exp x*jost s m x
/--
Defines `jostFunctionSlope` of type `ℝ` by `exp x*(jost s m x+jostSlope s m x)`.

Use: `chebyshev2.Filters.jostFunction_hasDerivAt` uses this definition to establish the
actual derivative at the stated point: `HasDerivAt (jostFunction s m) (jostFunctionSlope s m x)
x`.

Article: chebyshev2, Lemma 11 via `chebyshev2.Comparison.Profile.rightJost_ode`.
-/
def jostFunctionSlope (s : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ := exp x*(jost s m x+jostSlope s m x)

/--
The actual derivative at the stated point: `HasDerivAt (jostFunction s m) (jostFunctionSlope s
m x) x`.

Use: `chebyshev2.Calibration.Data.rightJost_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt (C.rightJost hκ s)
(C.rightJostSlope hκ s x) x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_hasDerivAt` with the arguments
shown in the proof.
-/
theorem jostFunction_hasDerivAt {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : HasDerivAt (jostFunction s m) (jostFunctionSlope s m x) x := by
  convert (Real.hasDerivAt_exp x).mul (jost_hasDerivAt hm hn hs x) using 1
  · rfl
  · dsimp only [jostFunctionSlope]
    ring

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(jostFunctionSlope s m) a b`.

Use: `chebyshev2.Calibration.Data.rightJost_ode` uses this assertion to establish the
actual derivative at the stated point: `HasDerivAt (C.rightJostSlope hκ s)
((1+s*C.comparisonDensity hκ x)*C.rightJost hκ s x) x`.

Article: chebyshev2, Lemma 11 via `chebyshev2.Comparison.Profile.rightJost_ode`.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_c1`,
`chebyshev2.Filters.jostSlope_locallyAC` with the arguments shown in the proof.
-/
theorem jostFunctionSlope_locallyAC {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (a b : ℝ) : AbsolutelyContinuousOnInterval (jostFunctionSlope s m) a b := by
  have he : ContDiff ℝ 1 Real.exp := contDiff_exp
  apply (he.contDiffOn.absolutelyContinuousOnInterval.mul
    ((jost_c1 hm hn hs).contDiffOn.absolutelyContinuousOnInterval.add
      (jostSlope_locallyAC hm hn hs a b))).congr
  intro x _
  rfl

/--
The actual second-order Jost equation in Proposition 3(ii).

Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(jostFunctionSlope s m) ((1+s*m x)*jostFunction s m x) x`.

Use: `chebyshev2.Calibration.Data.rightJost_ode` uses this assertion to establish the
actual derivative at the stated point: `HasDerivAt (C.rightJostSlope hκ s)
((1+s*C.comparisonDensity hκ x)*C.rightJost hκ s x) x`.

Article: chebyshev2, Lemma 11 via `chebyshev2.Comparison.Profile.rightJost_ode`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem jostFunction_ode {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : ∀ᵐ x,
    HasDerivAt (jostFunctionSlope s m) ((1+s*m x)*jostFunction s m x) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [jost_second_derivative hm hn hs] with x hx
  convert (Real.hasDerivAt_exp x).mul ((jost_hasDerivAt hm hn hs x).add hx) using 1
  · rfl
  · dsimp only [jostFunction, Pi.add_apply]
    ring

/--
Exact identity `nonlinear s m x=jostFunctionSlope s m x/jostFunction s m x-1`.

Use: `chebyshev2.Calibration.Data.rightFilter_jost_quotient` uses this identity to
establish the precise assertion is `C.rightFilter hκ s q= -C.rightJostSlope hκ s
((C.comparisonSpeed hκ).X q)/ C.rightJost hκ s ((C.comparisonSpeed hκ).X q)-1`.

Article: chebyshev2, Lemma 11.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem nonlinear_jostFunction_quotient {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    nonlinear s m x=jostFunctionSlope s m x/jostFunction s m x-1 := by
  dsimp only [nonlinear,jostFunctionSlope,jostFunction]
  field_simp [(exp_pos x).ne',(jost_positive hm hn hs x).ne']
  ring

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun x =>
jostFunction s m x/exp x) atBot (𝓝 1)`.

Use: a standalone supporting limit for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem jostFunction_asymptotic {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Tendsto (fun x => jostFunction s m x/exp x) atBot (𝓝 1) := by
  have he : (fun x => jostFunction s m x/exp x)=jost s m := by
    funext x
    exact mul_div_cancel_left₀ _ (exp_ne_zero x)
  rw [he]
  exact jost_left_limit hm hn hs

end
end chebyshev2.Filters
