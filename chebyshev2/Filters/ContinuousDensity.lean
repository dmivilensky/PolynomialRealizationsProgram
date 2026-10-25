import chebyshev2.Filters.SpectralObservations

/-!
Article: chebyshev2, Lemma 11.
Continuous Density.
Use: `chebyshev2.Filters.causal_c1` feeds `chebyshev2.Comparison.causal_square_density_mass`
(causal square density mass).
Proof chain: `chebyshev2.Comparison.Profile.signed_trace_comparison` — chebyshev2, Theorem
3.4; Signed determinant and square-trace comparisons.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hc : Continuous m)
variable {s : ℝ} (hs : 0 ≤ s)
include hm hn hc hs

/--
The actual derivative at the stated point: `HasDerivAt (nonlinear s m) (s*m x-2*nonlinear s m
x-(nonlinear s m x)^2) x`.

Use: `chebyshev2.Filters.nonlinear_c1` uses this derivative formula to establish smoothness
to the stated order: `ContDiff ℝ 1 (nonlinear s m)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.locallyAC_hasDerivAt_of_continuous`,
`chebyshev2.Filters.nonlinear_locallyAC`, `chebyshev2.Filters.nonlinear_derivative`
with the arguments shown in the proof.
-/
theorem nonlinear_hasDerivAt (x : ℝ) :
    HasDerivAt (nonlinear s m) (s*m x-2*nonlinear s m x-(nonlinear s m x)^2) x :=
  locallyAC_hasDerivAt_of_continuous (nonlinear_locallyAC hm hn hs)
    (nonlinear_derivative hm hn hs)
    (((continuous_const.mul hc).sub (continuous_const.mul (nonlinear_continuous hm hn hs))).sub
      ((nonlinear_continuous hm hn hs).pow 2)) x

/--
Smoothness to the stated order: `ContDiff ℝ 1 (nonlinear s m)`.

Use: `chebyshev2.Calibration.Data.leftFilter_ac` uses this assertion to establish absolute
continuity on the specified interval: `AbsolutelyContinuousOnInterval (C.leftFilter hκ s) 0 2`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem nonlinear_c1 : ContDiff ℝ 1 (nonlinear s m) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (nonlinear_hasDerivAt hm hn hc hs x).differentiableAt,?_⟩
  have he : deriv (nonlinear s m)=fun x => s*m x-2*nonlinear s m x-(nonlinear s m x)^2 :=
    funext (fun x => (nonlinear_hasDerivAt hm hn hc hs x).deriv)
  rw [he]
  exact ((continuous_const.mul hc).sub (continuous_const.mul (nonlinear_continuous hm hn hs))).sub
    ((nonlinear_continuous hm hn hs).pow 2)

omit hc in
/--
The actual derivative at the stated point: `HasDerivAt (jost s m) (nonlinear s m x*jost s m x)
x`.

Use: `chebyshev2.Filters.jostWronskian_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt (jostWronskian s m) 0 x`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_positive`,
`chebyshev2.Filters.jost_hasDerivAt` with the arguments shown in the proof.
-/
theorem jost_hasDerivAt_filter (x : ℝ) :
    HasDerivAt (jost s m) (nonlinear s m x*jost s m x) x := by
  convert jost_hasDerivAt hm hn hs x using 1
  exact div_mul_cancel₀ _ (jost_positive hm hn hs x).ne'

omit hn hs in
/--
The actual derivative at the stated point: `HasDerivAt (causal c m) (m x-c*causal c m x) x`.

Use: `chebyshev2.Filters.causal_c1` uses this derivative formula to establish smoothness to
the stated order: `ContDiff ℝ 1 (causal c m)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.square_trace_cubic`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.locallyAC_hasDerivAt_of_continuous`,
`chebyshev2.Filters.causal_locallyAC`, `chebyshev2.Filters.causal_derivative_ae` with
the arguments shown in the proof.
-/
theorem causal_hasDerivAt {c : ℝ} (h : 0 ≤ c) (x : ℝ) :
    HasDerivAt (causal c m) (m x-c*causal c m x) x :=
  locallyAC_hasDerivAt_of_continuous (causal_locallyAC h hm) (causal_derivative_ae h hm)
    (hc.sub (continuous_const.mul (causal_continuous h hm))) x

omit hn hs in
/--
Smoothness to the stated order: `ContDiff ℝ 1 (causal c m)`.

Use: `chebyshev2.Calibration.Data.leftLinear_ac` uses this assertion to establish absolute
continuity on the specified interval: `AbsolutelyContinuousOnInterval (C.leftLinear hκ) 0 2`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem causal_c1 {c : ℝ} (h : 0 ≤ c) : ContDiff ℝ 1 (causal c m) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (causal_hasDerivAt hm hc h x).differentiableAt,?_⟩
  have he : deriv (causal c m)=fun x => m x-c*causal c m x :=
    funext (fun x => (causal_hasDerivAt hm hc h x).deriv)
  rw [he]
  exact hc.sub (continuous_const.mul (causal_continuous h hm))

end
end chebyshev2.Filters
