import krylov.Design.PoissonSechSquared
import krylov.Design.HyperbolicSeriesLimit

/-!
Article: main_krylov, apC:lem:poisson, the complete real remainder statements.
Use: identify the actual primary-series remainders with the independently
estimated dual tails, proving their positivity and precise exponential
asymptotics. Also record both scaled leading constants of the majorants.
Source: the actual Poisson identities, genuine Lambert-series estimates,
and the integral test, with tanh as the squared-secant primitive.
-/

/-!
Article: krylov, Lemma D.5 [apC:lem:poisson].

Both literal Poisson identities have positive dual tails and the precise first exponential
coefficients; a genuine elliptic integral and its standard nome give the equivalent expression.
All sums use positive indices m≥1, with the half-endpoint contribution written separately.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory jacobi.Young Set
open scoped Topology

/-- Both genuine primary-series remainders equal the actual dual tails.
Article: main_krylov, apC:lem:poisson. -/
theorem poisson_remainders_eq_dual {θ : ℝ} (hθ : 0 < θ) :
    sampledSech θ - (π / (2 * θ) - 1 / 2) = sechDualTail θ ∧
      sampledSechSquared θ - (1 / θ - 1 / 2) = sechSquaredDualTail θ := by
  constructor
  · rw [poisson_sech hθ, sechDualTail]
    ring
  · rw [poisson_sechSquared hθ, sechSquaredDualTail]
    ring

/-- Both genuine primary-series remainders are strictly positive at every positive spacing.
Article: main_krylov, apC:lem:poisson. -/
theorem poisson_remainders_pos {θ : ℝ} (hθ : 0 < θ) :
    0 < sampledSech θ - (π / (2 * θ) - 1 / 2) ∧
      0 < sampledSechSquared θ - (1 / θ - 1 / 2) := by
  rw [(poisson_remainders_eq_dual hθ).1, (poisson_remainders_eq_dual hθ).2]
  exact dual_tails_pos hθ

/-- The actual secant-series remainder has the exact first exponential coefficient.
Article: main_krylov, apC:lem:poisson, the first `(1+o(1))` assertion. -/
theorem poisson_sech_remainder_asymptotic :
    Tendsto (fun θ : ℝ => (sampledSech θ - (π / (2 * θ) - 1 / 2)) /
      (2 * π / θ * exp (-(π ^ 2 / θ)))) (𝓝[>] 0) (𝓝 1) := by
  apply sechDualTail_exponential_asymptotic.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  rw [(poisson_remainders_eq_dual hθ).1]

/-- The actual squared-secant remainder has the exact first exponential coefficient.
Article: main_krylov, apC:lem:poisson, the second `(1+o(1))` assertion. -/
theorem poisson_sechSquared_remainder_asymptotic :
    Tendsto (fun θ : ℝ => (sampledSechSquared θ - (1 / θ - 1 / 2)) /
      (4 * π ^ 2 / θ ^ 2 * exp (-(π ^ 2 / θ)))) (𝓝[>] 0) (𝓝 1) := by
  apply sechSquaredDualTail_exponential_asymptotic.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  rw [(poisson_remainders_eq_dual hθ).2]

/-- The genuine positive-half-line squared-secant integral is one.
Article: main_krylov, the leading squared-majorant constant. -/
theorem integral_Ioi_sechSquared : (∫ x : ℝ in Ioi 0, sech x ^ 2) = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (tanh_derivative 0).continuousAt.continuousWithinAt
    (fun x (_ : x ∈ Ioi 0) => tanh_derivative x)
    sech_sq_integrable.integrableOn tanh_atTop
  simpa using h

/-- Both exact leading majorant constants have elementary one-mesh bounds.
Article: main_krylov, the upper majorants after thm:B. -/
theorem sampledSechSquared_scaled_bounds {θ : ℝ} (hθ : 0 < θ) :
    1 - θ ≤ θ * sampledSechSquared θ ∧ θ * sampledSechSquared θ ≤ 1 := by
  have ha : AntitoneOn (fun x : ℝ => sech x ^ 2) (Ici 0) := by
    intro x hx y hy hxy
    exact pow_le_pow_left₀ (sech_pos y).le (sech_antitoneOn hx hy hxy) 2
  have h := scaled_antitone_sample_bounds (fun x : ℝ => sech x ^ 2) ha
    sech_sq_integrable.integrableOn (fun x _ => sq_nonneg _) hθ
  rw [integral_Ioi_sechSquared] at h
  simpa only [sampledSechSquared, sech, Real.cosh_zero, inv_one, one_pow, mul_one] using h

/-- The actual scaled squared-majorant sum converges to one as spacing tends to zero.
Article: main_krylov, the asymptotic upper squared-majorant endpoint. -/
theorem sampledSechSquared_scaled_tendsto :
    Tendsto (fun θ : ℝ => θ * sampledSechSquared θ) (𝓝[>] 0) (𝓝 1) := by
  have hl : Tendsto (fun θ : ℝ => 1 - θ) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun θ : ℝ => 1 - θ) 0 := continuousAt_const.sub continuousAt_id
    simpa only [sub_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hl.squeeze' tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact (sampledSechSquared_scaled_bounds hθ).1
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact (sampledSechSquared_scaled_bounds hθ).2

end
end krylov.Design
