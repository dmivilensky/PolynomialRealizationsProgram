import «2610.05164v2».Filters.FredholmCurve
import «2610.05164v2».Filters.NonlinearMass

/-!
Article: 2610.05164v2, Proposition 3.
The cumulative transmission is exactly V+V'/2, the coefficient that survives at the right endpoint
in the Jost expansion.
Use: `«2610.05164v2».Filters.truncatedTransmission_right_limit` feeds
`«2610.05164v2».Filters.log_transmission_eq_logDeterminant` (Fredholm--Jost identity at the level of
the actual spectral logarithm).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `truncatedTransmission` of type `ℝ` by `1+s/2*cumulative (fun t => m t*jost s m t) x`.

Use: `«2610.05164v2».Filters.log_truncatedTransmission_derivative` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun
x => log (truncatedTransmission s m x)) (s*m x/(2+nonlinear s m x)) x`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.
-/
def truncatedTransmission (s : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ :=
  1+s/2*cumulative (fun t => m t*jost s m t) x

/--
The stated quantitative bound `1 ≤ truncatedTransmission s m x`.

Use: `«2610.05164v2».Filters.log_truncatedTransmission_derivative` uses this bound to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => log
(truncatedTransmission s m x)) (s*m x/(2+nonlinear s m x)) x`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.cumulative_bounds`,
`«2610.05164v2».Filters.jost_forcing_integrable`, `«2610.05164v2».Filters.jost_positive` with
the arguments shown in the proof.
-/
theorem truncatedTransmission_ge_one {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : 1 ≤ truncatedTransmission s m x := by
  have h := (cumulative_bounds (jost_forcing_integrable hm hn hs)
    (fun t => mul_nonneg (hn t) (jost_positive hm hn hs t).le) x).1
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hs (by norm_num : (0:ℝ) ≤ 2)) h)

/--
The cumulative transmission is exactly V+V'/2, the coefficient that survives at the right
endpoint in the Jost expansion.

Exact identity `truncatedTransmission s m x=jost s m x+jostSlope s m x/2`.

Use: `«2610.05164v2».Filters.log_truncatedTransmission_derivative` rewrites with this identity
to prove the eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(fun x => log (truncatedTransmission s m x)) (s*m x/(2+nonlinear s m x)) x`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_equation` with the arguments
shown in the proof.
-/
theorem truncatedTransmission_eq {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    truncatedTransmission s m x=jost s m x+jostSlope s m x/2 := by
  -- Use the identities/estimates `«2610.05164v2».Filters.jost_equation` with the arguments
  -- shown in the proof.
  have h := jost_equation hm hn hs x
  dsimp only [volterra] at h
  dsimp only [truncatedTransmission,jostSlope]
  linarith

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(truncatedTransmission s m) a b`.

Use: `«2610.05164v2».Filters.log_truncatedTransmission_locallyAC` uses this assertion to
establish absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (fun x
=> log (truncatedTransmission s m x)) a b`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.cumulative_locallyAC`,
`«2610.05164v2».Filters.jost_forcing_integrable` with the arguments shown in the proof.
-/
theorem truncatedTransmission_locallyAC {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (truncatedTransmission s m) a b :=
  (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => (1:ℝ))
    (uIcc a b)).absolutelyContinuousOnInterval.add
      ((cumulative_locallyAC (jost_forcing_integrable hm hn hs) a b).const_mul (s/2))
/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (fun x => log
(truncatedTransmission s m x)) a b`.

Use: `«2610.05164v2».Filters.leftLogDeterminant_eq_log_truncatedTransmission` uses this
identity to establish the identity `leftLogDeterminant hm hn s x=log (truncatedTransmission s
m x)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.locallyAC_of_dist_le`,
`«2610.05164v2».Filters.truncatedTransmission_locallyAC`,
`«2610.05164v2».Continuum.log_abs_sub_le` with the arguments shown in the proof.
-/
theorem log_truncatedTransmission_locallyAC {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => log (truncatedTransmission s m x)) a b := by
  apply locallyAC_of_dist_le (truncatedTransmission_locallyAC hm hn hs a b)
  intro x y
  simp only [Real.dist_eq]
  exact log_abs_sub_le (truncatedTransmission_ge_one hm hn hs x) (truncatedTransmission_ge_one hm hn hs y)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => log
(truncatedTransmission s m x)) (s*m x/(2+nonlinear s m x)) x`.

Use: `«2610.05164v2».Filters.leftLogDeterminant_eq_log_truncatedTransmission` uses this
identity to establish the identity `leftLogDeterminant hm hn s x=log (truncatedTransmission s
m x)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem log_truncatedTransmission_derivative {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ x, HasDerivAt (fun x => log (truncatedTransmission s m x))
      (s*m x/(2+nonlinear s m x)) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [cumulative_derivative (jost_forcing_integrable hm hn hs)] with x hx
  have hpos : 0 < truncatedTransmission s m x := zero_lt_one.trans_le (truncatedTransmission_ge_one hm hn hs x)
  have h := ((hx.const_mul (s/2)).const_add 1).log hpos.ne'
  change HasDerivAt (fun x => log (truncatedTransmission s m x))
    ((s/2*(m x*jost s m x))/truncatedTransmission s m x) x at h
  convert h using 1
  rw [truncatedTransmission_eq hm hn hs x]
  have hV := (jost_positive hm hn hs x).ne'
  have hr : 2+nonlinear s m x ≠ 0 := by
    have hn' := (nonlinear_bounds hm hn hs x).1
    linarith
  have hT : jost s m x+jostSlope s m x/2 ≠ 0 := by
    rw [← truncatedTransmission_eq hm hn hs x]
    exact hpos.ne'
  dsimp only [nonlinear]
  field_simp [hV,hT,hr]

/--
Convergence along the specified source filter to the specified limit: `Tendsto
(truncatedTransmission s m) atBot (𝓝 1)`.

Use: `«2610.05164v2».Filters.leftLogDeterminant_eq_log_truncatedTransmission` uses this limit
to establish the identity `leftLogDeterminant hm hn s x=log (truncatedTransmission s m x)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.cumulative_left_limit` with the
arguments shown in the proof.
-/
theorem truncatedTransmission_left_limit (s : ℝ) (m : ℝ → ℝ) :
    Tendsto (truncatedTransmission s m) atBot (𝓝 1) := by
  have h := (cumulative_left_limit (fun t => m t*jost s m t)).const_mul (s/2) |>.const_add 1
  change Tendsto (fun x => 1+s/2*cumulative (fun t => m t*jost s m t) x) atBot (𝓝 1)
  simpa only [mul_zero,add_zero] using h

/--
Convergence along the specified source filter to the specified limit: `Tendsto
(truncatedTransmission s m) atTop (𝓝 (transmission s m))`.

Use: `«2610.05164v2».Filters.log_transmission_eq_logDeterminant` uses this limit to establish
exact identity `log (transmission s m)=logDeterminant (kernelEigenvalue hm hn) s`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.cumulative_right_limit`,
`«2610.05164v2».Filters.jost_forcing_integrable` with the arguments shown in the proof.
-/
theorem truncatedTransmission_right_limit {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Tendsto (truncatedTransmission s m) atTop (𝓝 (transmission s m)) :=
  (cumulative_right_limit (jost_forcing_integrable hm hn hs)).const_mul (s/2) |>.const_add 1

end
end «2610.05164v2».Filters
