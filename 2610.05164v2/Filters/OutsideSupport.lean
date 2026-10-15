import «2610.05164v2».Filters.NonlinearMass

/-!
Article: 2610.05164v2, Lemma 11.
The exact right-hand Jost expansion.
Use: `«2610.05164v2».Filters.jost_right_of_density_zero` feeds
`«2610.05164v2».Comparison.Profile.rightJost_left_expansion` (right Jost left expansion).
Proof chain: `«2610.05164v2».Calibration.Data.rightJost_left_expansion` — 2610.05164v2, Lemma 11;
Right-filter bounds, endpoint conditions, ODE, Jost and integral formulas.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(∫ t in Iic x, j t)=∫ t, j t`.

Use: `«2610.05164v2».Filters.jost_right_of_density_zero` rewrites with this identity to
establish exact identity `exp x*jost s m x=transmission s m*exp x- (s/2*(∫ t, exp (2*t)*(m
t*jost s m t)))*exp (-x)`.

Article: 2610.05164v2, Lemma 11 via `«2610.05164v2».Calibration.Data.rightJost_left_expansion`.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem integral_Iic_eq_integral_of_right_zero {j : ℝ → ℝ} (x : ℝ)
    (hj : ∀ t, x < t → j t=0) : (∫ t in Iic x, j t)=∫ t, j t := by
  -- Separate `t ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [← integral_indicator measurableSet_Iic]
  congr 1
  funext t
  by_cases ht : t ≤ x
  · exact indicator_of_mem (show t ∈ Iic x from ht) j
  · rw [indicator_of_notMem (show t ∉ Iic x from ht)]
    exact (hj t (lt_of_not_ge ht)).symm

/--
Exact identity `jost s m x=1`.

Use: `«2610.05164v2».Calibration.Data.rightJost_normalization` rewrites with this identity to
establish exact identity `C.rightJost hκ s x=exp (-x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem jost_left_of_density_zero {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) (hz : ∀ t ≤ x, m t=0) : jost s m x=1 := by
  rw [jost_equation hm hn hs x, volterra_integral (jost_forcing_integrable hm hn hs)]
  have he : (fun t => (1-exp (-2*(x-t)))*m t*jost s m t)=ᵐ[volume.restrict (Iic x)]
      (fun _ => (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    rw [hz t ht, mul_zero, zero_mul]
  rw [integral_congr_ae he, integral_zero, mul_zero, add_zero]

/--
Exact identity `nonlinear s m x=0`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_zero` rewrites with this identity
to establish `P.determinantPotential hκ s 0 0= logDeterminant
(kernelEigenvalue ((P.speedData hκ).density_integrable hκ) ((P.speedData hκ).density_nonneg
hκ)) s`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem nonlinear_left_of_density_zero {m : ℝ → ℝ} (x s : ℝ)
    (hz : ∀ t ≤ x, m t=0) : nonlinear s m x=0 := by
  unfold nonlinear jostSlope causal
  have he : (fun t => exp (2*t)*(m t*jost s m t))=ᵐ[volume.restrict (Iic x)]
      (fun _ => (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    rw [hz t ht, zero_mul, mul_zero]
  rw [integral_congr_ae he, integral_zero, mul_zero, mul_zero, zero_div]

/--
Integrability of the displayed function: `Integrable (fun t => exp (2*t)*(m t*jost s m t))`.

Use: a standalone supporting integrability result for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 11.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem jost_right_coefficient_integrable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) (hz : ∀ t, x < t → m t=0) :
    Integrable (fun t => exp (2*t)*(m t*jost s m t)) := by
  -- Separate `t ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hi := (integrable_indicator_iff measurableSet_Iic).mpr
    (forcing_integrable (by norm_num : (0:ℝ) ≤ 2) (jost_forcing_integrable hm hn hs) x)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun t => by
    by_cases ht : t ≤ x
    · exact indicator_of_mem (show t ∈ Iic x from ht) _
    · rw [indicator_of_notMem (show t ∉ Iic x from ht)]
      change 0=exp (2*t)*(m t*jost s m t)
      rw [hz t (lt_of_not_ge ht),zero_mul,mul_zero])

/--
The exact right-hand Jost expansion. The coefficient of exp(x) is the analytic transmission
coefficient; its spectral identification is separate.

Exact identity `exp x*jost s m x=transmission s m*exp x- (s/2*(∫ t, exp (2*t)*(m t*jost s m
t)))*exp (-x)`.

Use: `«2610.05164v2».Calibration.Data.rightJost_left_expansion` uses this identity to establish
the identity stated in that declaration.

Article: 2610.05164v2, Lemma 11 via `«2610.05164v2».Calibration.Data.rightJost_left_expansion`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_equation`,
`«2610.05164v2».Filters.integral_Iic_eq_integral_of_right_zero` with the arguments shown in the
proof.
-/
theorem jost_right_of_density_zero {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) (hz : ∀ t, x < t → m t=0) :
    exp x*jost s m x=transmission s m*exp x-
      (s/2*(∫ t, exp (2*t)*(m t*jost s m t)))*exp (-x) := by
  -- Use the identities/estimates `«2610.05164v2».Filters.jost_equation`,
  -- `«2610.05164v2».Filters.integral_Iic_eq_integral_of_right_zero` with the arguments shown
  -- in the proof.
  rw [jost_equation hm hn hs x]
  unfold volterra cumulative causal transmission
  rw [integral_Iic_eq_integral_of_right_zero x (fun t ht => by rw [hz t ht, zero_mul]),
    integral_Iic_eq_integral_of_right_zero x (fun t ht => by
      change exp (2*t)*(m t*jost s m t)=0
      rw [hz t ht, zero_mul, mul_zero])]
  have he : exp x*exp (-2*x)=exp (-x) := by rw [← exp_add]; congr 1; ring
  linear_combination -(s/2*(∫ t, exp (2*t)*(m t*jost s m t)))*he

end
end «2610.05164v2».Filters
