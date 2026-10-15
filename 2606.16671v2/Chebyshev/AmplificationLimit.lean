import «2606.16671v2».Chebyshev.Amplification
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Article: 2606.16671v2, Remark 5.5.
Both the terminal error and the drift amplification have exact large-condition limits.
Use: `«2606.16671v2».normalized_drift_scale_limit` feeds
`«2606.16671v2».SpectralInterval.drift_scale_limit` (Remark 5.5: the drift threshold divided by μ
converges to 1/a²).
Proof chain: `«2606.16671v2».SpectralInterval.drift_scale_limit` — 2606.16671v2, Remark 5.5; Exact
drift scale, accuracy asymptotics and rational finite examples.
-/
namespace «2606.16671v2»
noncomputable section
open Real Filter Topology Polynomial.Chebyshev

/--
Convergence along the specified source filter to the specified limit: `Tendsto (dslope arsinh
0) (𝓝 (0:ℝ)) (𝓝 1)`.

Use: `«2606.16671v2».chebyshev_small_gap_limit` uses this limit to establish convergence along
the specified source filter to the specified limit: `Tendsto (fun j => (T ℝ (N j)).eval
(1+2*r*u j)) l (𝓝 (cosh (2*a*sqrt r)))`.

Article: 2606.16671v2, Remark 5.5 via `«2606.16671v2».SpectralInterval.drift_factor_limit`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem arsinh_dslope_limit : Tendsto (dslope arsinh 0) (𝓝 (0:ℝ)) (𝓝 1) := by
  have hc := continuousAt_dslope_same.mpr (hasDerivAt_arsinh 0).differentiableAt
  simpa only [dslope_same, (hasDerivAt_arsinh 0).deriv, zero_pow (by norm_num : 2 ≠ 0),
    add_zero, sqrt_one, inv_one] using hc.tendsto

/--
Exact identity `dslope arsinh 0 x*x = arsinh x`.

Use: `«2606.16671v2».chebyshev_small_gap_limit` uses this identity to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun j => (T ℝ (N j)).eval
(1+2*r*u j)) l (𝓝 (cosh (2*a*sqrt r)))`.

Article: 2606.16671v2, Remark 5.5 via `«2606.16671v2».SpectralInterval.drift_factor_limit`.

Proof: Separate `x = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
private theorem arsinh_dslope_mul (x : ℝ) : dslope arsinh 0 x*x = arsinh x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [dslope_of_ne _ hx]
    simp only [slope, arsinh_zero, sub_zero, vsub_eq_sub, smul_eq_mul]
    field_simp

/--
The small-gap limit of the exact finite Chebyshev factor.

Convergence along the specified source filter to the specified limit: `Tendsto (fun j => (T ℝ
(N j)).eval (1+2*r*u j)) l (𝓝 (cosh (2*a*sqrt r)))`.

Use: `«2606.16671v2».normalized_amplification_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun j => (T ℝ (N j)).eval
(1+2*r*u j)/(T ℝ (N j)).eval (1+2*u j)) l (𝓝 (cosh (2*a*sqrt r)/cosh (2*a)))`.

Article: 2606.16671v2, Remark 5.5 via `«2606.16671v2».SpectralInterval.drift_factor_limit`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem chebyshev_small_gap_limit {α : Type*} {l : Filter α} {N : α → ℕ} {u : α → ℝ}
    {a r : ℝ} (hr : 0 ≤ r) (hu : ∀ᶠ j in l, 0 ≤ u j)
    (hu0 : Tendsto u l (𝓝 0))
    (hNu : Tendsto (fun j => (N j:ℝ)*sqrt (u j)) l (𝓝 a)) :
    Tendsto (fun j => (T ℝ (N j)).eval (1+2*r*u j)) l (𝓝 (cosh (2*a*sqrt r))) := by
  -- Record the convergence hx with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hx : Tendsto (fun j => sqrt r*sqrt (u j)) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := sqrt r)).mul
      (continuous_sqrt.continuousAt.tendsto.comp hu0)
  have hd := arsinh_dslope_limit.comp hx
  have hm := ((tendsto_const_nhds (x := 2*sqrt r)).mul hNu).mul hd
  simp only [mul_one] at hm
  have hh := continuous_cosh.continuousAt.tendsto.comp hm
  have he : 2*sqrt r*a = 2*a*sqrt r := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [hu] with j hj
  simp only [Function.comp_def]
  rw [show 1+2*r*u j = 1+2*(r*u j) by ring, chebyshev_arsinh _ _ (mul_nonneg hr hj),
    sqrt_mul hr]
  congr 1
  have h := arsinh_dslope_mul (sqrt r*sqrt (u j))
  linear_combination 2*(N j:ℝ)*h

/--
Both the terminal error and the drift amplification have exact large-condition limits.

Convergence along the specified source filter to the specified limit: `Tendsto (fun j => (T ℝ
(N j)).eval (1+2*r*u j)/(T ℝ (N j)).eval (1+2*u j)) l (𝓝 (cosh (2*a*sqrt r)/cosh (2*a)))`.

Use: `«2606.16671v2».SpectralInterval.drift_factor_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun j => (I
j).epsilon (N j)*(T ℝ (N j)).eval (1+2*r*(I j).mu/(I j).delta)) l (𝓝 (cosh (2*a*sqrt r)/cosh
(2*a)))`.

Article: 2606.16671v2, Remark 5.5 via `«2606.16671v2».SpectralInterval.drift_factor_limit`.

Proof: Use the identities/estimates `«2606.16671v2».chebyshev_small_gap_limit` with the
arguments shown in the proof.
-/
theorem normalized_amplification_limit {α : Type*} {l : Filter α} {N : α → ℕ} {u : α → ℝ}
    {a r : ℝ} (hr : 0 ≤ r) (hu : ∀ᶠ j in l, 0 ≤ u j)
    (hu0 : Tendsto u l (𝓝 0))
    (hNu : Tendsto (fun j => (N j:ℝ)*sqrt (u j)) l (𝓝 a)) :
    Tendsto (fun j => (T ℝ (N j)).eval (1+2*r*u j)/(T ℝ (N j)).eval (1+2*u j))
      l (𝓝 (cosh (2*a*sqrt r)/cosh (2*a))) := by
  -- Use the identities/estimates `«2606.16671v2».chebyshev_small_gap_limit` with the arguments
  -- shown in the proof.
  have hd := chebyshev_small_gap_limit (r := 1) (by norm_num) hu hu0 hNu
  simp only [mul_one, sqrt_one] at hd
  exact (chebyshev_small_gap_limit hr hu hu0 hNu).div hd (cosh_pos _).ne'

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun j => 1/(u
j*(N j:ℝ)^2)) l (𝓝 (1/a^2))`.

Use: `«2606.16671v2».SpectralInterval.drift_scale_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun j => (I
j).delta/((I j).mu*(N j:ℝ)^2)) l (𝓝 (1/a^2))`.

Article: 2606.16671v2, Remark 5.5 via `«2606.16671v2».SpectralInterval.drift_scale_limit`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem normalized_drift_scale_limit {α : Type*} {l : Filter α} {N : α → ℕ} {u : α → ℝ}
    {a : ℝ} (ha : a ≠ 0) (hu : ∀ᶠ j in l, 0 ≤ u j)
    (hNu : Tendsto (fun j => (N j:ℝ)*sqrt (u j)) l (𝓝 a)) :
    Tendsto (fun j => 1/(u j*(N j:ℝ)^2)) l (𝓝 (1/a^2)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hh := (tendsto_const_nhds (x := (1:ℝ))).div (hNu.pow 2) (pow_ne_zero 2 ha)
  apply hh.congr'
  filter_upwards [hu] with j hj
  change 1/((N j:ℝ)*sqrt (u j))^2 = _
  rw [mul_pow, sq_sqrt hj]
  congr 1
  ring

end
end «2606.16671v2»
