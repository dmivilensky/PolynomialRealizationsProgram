import «2606.16671v2».Chebyshev.AmplificationLimit
import «2606.16671v2».Realization.StaticShift

/-!
Article: 2606.16671v2, Remark 5.5.
At δ=μ the attaining static shift has residual and operator norm exactly one.
Result: `«2606.16671v2».Realization.static_shift_at_mu` supplies the stated article conclusion.
-/
namespace «2606.16671v2»
noncomputable section
open Real Filter Topology Polynomial Polynomial.Chebyshev
set_option backward.isDefEq.respectTransparency false

namespace SpectralInterval

/--
The stated quantitative bound `1 < I.kappa`.

Use: `«2606.16671v2».SpectralInterval.effectiveKappa_sqrt` rewrites with this bound to
establish exact identity `sqrt (I.effectiveKappa delta) = sqrt I.kappa/(1-sqrt (delta/I.mu))`.

Article: 2606.16671v2, Remark 5.5 via
`«2606.16671v2».SpectralInterval.amplification_effectiveKappa_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem kappa_gt_one (I : SpectralInterval) : 1 < I.kappa := by
  rw [kappa, lt_div_iff₀ I.mu_pos]
  simpa using I.mu_lt_L

/--
Exact identity `I.mu/I.delta = 1/(I.kappa-1)`.

Use: `«2606.16671v2».SpectralInterval.drift_factor_limit` uses this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun j => (I
j).epsilon (N j)*(T ℝ (N j)).eval (1+2*r*(I j).mu/(I j).delta)) l (𝓝 (cosh (2*a*sqrt r)/cosh
(2*a)))`.

Article: 2606.16671v2, Remark 5.5 via `«2606.16671v2».SpectralInterval.drift_scale_limit`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem gap_ratio_eq (I : SpectralInterval) : I.mu/I.delta = 1/(I.kappa-1) := by
  unfold kappa delta
  field_simp [I.mu_pos.ne', (sub_pos.mpr I.mu_lt_L).ne']

/--
Defines `effectiveKappa` of type `ℝ` by `I.kappa/(1-sqrt (delta/I.mu))^2`.

Use: `«2606.16671v2».SpectralInterval.effectiveKappa_sqrt` rewrites with this definition to
establish exact identity `sqrt (I.effectiveKappa delta) = sqrt I.kappa/(1-sqrt (delta/I.mu))`.

Article: 2606.16671v2, Remark 5.5 via
`«2606.16671v2».SpectralInterval.amplification_effectiveKappa_le`.
-/
def effectiveKappa (I : SpectralInterval) (delta : ℝ) : ℝ :=
  I.kappa/(1-sqrt (delta/I.mu))^2

/--
Exact identity `sqrt (I.effectiveKappa delta) = sqrt I.kappa/(1-sqrt (delta/I.mu))`.

Use: `«2606.16671v2».SpectralInterval.amplification_effectiveKappa_le` rewrites with this
identity to prove the bound `I.epsilon N*(T ℝ N).eval
(1+2*delta/I.delta) ≤ 2*exp (-2*(N:ℝ)/sqrt (I.effectiveKappa delta))`.

Article: 2606.16671v2, Remark 5.5 via
`«2606.16671v2».SpectralInterval.amplification_effectiveKappa_le`.

Proof: Use the identities/estimates `«2606.16671v2».SpectralInterval.kappa_gt_one` with the
arguments shown in the proof.
-/
theorem effectiveKappa_sqrt (I : SpectralInterval) {delta : ℝ}
    (hd : 0 ≤ delta) (hdmu : delta < I.mu) :
    sqrt (I.effectiveKappa delta) = sqrt I.kappa/(1-sqrt (delta/I.mu)) := by
  have hr : delta/I.mu < 1 := (div_lt_one I.mu_pos).mpr hdmu
  have hs : sqrt (delta/I.mu) < 1 := by
    simpa using sqrt_lt_sqrt (div_nonneg hd I.mu_pos.le) hr
  rw [effectiveKappa, sqrt_div (le_of_lt (lt_trans zero_lt_one I.kappa_gt_one)),
    sqrt_sq (by linarith)]

/--
The stated quantitative bound `I.epsilon N*(T ℝ N).eval (1+2*delta/I.delta) ≤ 2*exp
(-2*(N:ℝ)/sqrt (I.effectiveKappa delta))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Remark 5.5.

Proof: Use the identities/estimates `«2606.16671v2».SpectralInterval.effectiveKappa_sqrt`,
`«2606.16671v2».SpectralInterval.amplification_accelerated_le` with the arguments shown in the
proof.
-/
theorem amplification_effectiveKappa_le (I : SpectralInterval) (N : ℕ) {delta : ℝ}
    (hd : 0 ≤ delta) (hdmu : delta < I.mu) :
    I.epsilon N*(T ℝ N).eval (1+2*delta/I.delta) ≤
      2*exp (-2*(N:ℝ)/sqrt (I.effectiveKappa delta)) := by
  -- Use the identities/estimates `«2606.16671v2».SpectralInterval.effectiveKappa_sqrt`,
  -- `«2606.16671v2».SpectralInterval.amplification_accelerated_le` with the arguments shown in
  -- the proof.
  rw [I.effectiveKappa_sqrt hd hdmu]
  convert I.amplification_accelerated_le N delta hd hdmu.le using 1
  simp only [div_div_eq_mul_div]
  congr 2
  ring

end SpectralInterval

/--
For N/sqrt κ → a, the exact small-gap parameter satisfies N sqrt(μ/Δ) → a.

Convergence along the specified source filter to the specified limit: `Tendsto (fun j => (N
j:ℝ)*sqrt (1/(K j-1))) l (𝓝 a)`.

Use: `«2606.16671v2».SpectralInterval.drift_factor_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun j => (I
j).epsilon (N j)*(T ℝ (N j)).eval (1+2*r*(I j).mu/(I j).delta)) l (𝓝 (cosh (2*a*sqrt r)/cosh
(2*a)))`.

Article: 2606.16671v2, Remark 5.5 via `«2606.16671v2».SpectralInterval.drift_scale_limit`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem condition_horizon_limit {α : Type*} {l : Filter α}
    {K : α → ℝ} {N : α → ℕ} {a : ℝ} (hK : Tendsto K l atTop)
    (hN : Tendsto (fun j => (N j:ℝ)/sqrt (K j)) l (𝓝 a)) :
    Tendsto (fun j => (N j:ℝ)*sqrt (1/(K j-1))) l (𝓝 a) := by
  -- Record the convergence hi with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hi : Tendsto (fun j => 1/K j) l (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hK
  -- Record the convergence hc with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hc : Tendsto (fun j => 1/(1-1/K j)) l (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℝ))).div
      ((tendsto_const_nhds (x := (1:ℝ))).sub hi) (by norm_num : (1:ℝ)-0 ≠ 0)
    change Tendsto (fun j => 1/(1-1/K j)) l (𝓝 (1/(1-0))) at hh
    simpa using hh
  have hh := hN.mul (hc.sqrt)
  simp only [sqrt_one, mul_one] at hh
  apply hh.congr'
  filter_upwards [hK.eventually (eventually_gt_atTop (1:ℝ))] with j hj
  have he : 1/(1-1/K j) = K j/(K j-1) := by field_simp
  rw [he, sqrt_div (show 0 ≤ K j by linarith), sqrt_div (by norm_num : (0:ℝ) ≤ 1), sqrt_one]
  field_simp [(sqrt_pos.mpr (show 0 < K j by linarith)).ne']

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun j => 1/(K
j-1)) l (𝓝 0)`.

Use: `«2606.16671v2».SpectralInterval.drift_factor_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun j => (I
j).epsilon (N j)*(T ℝ (N j)).eval (1+2*r*(I j).mu/(I j).delta)) l (𝓝 (cosh (2*a*sqrt r)/cosh
(2*a)))`.

Article: 2606.16671v2, Remark 5.5 via `«2606.16671v2».SpectralInterval.drift_factor_limit`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem condition_gap_limit {α : Type*} {l : Filter α} {K : α → ℝ}
    (hK : Tendsto K l atTop) : Tendsto (fun j => 1/(K j-1)) l (𝓝 0) := by
  simpa only [one_div, Function.comp_def, sub_eq_add_neg] using
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right l (-1:ℝ) hK)

/--
Remark 5.5: the drift threshold divided by μ converges to 1/a².

Convergence along the specified source filter to the specified limit: `Tendsto (fun j => (I
j).delta/((I j).mu*(N j:ℝ)^2)) l (𝓝 (1/a^2))`.

Use: `«2606.16671v2».SpectralInterval.logarithmic_drift_scale_limit` uses this limit to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun j
=> (I j).delta/((I j).mu*(N j:ℝ)^2)) l (𝓝 (4/(log (2/epsilon))^2))`.

Article: 2606.16671v2, Remark 5.5.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem SpectralInterval.drift_scale_limit {α : Type*} {l : Filter α}
    {I : α → SpectralInterval} {N : α → ℕ} {a : ℝ} (ha : a ≠ 0)
    (hK : Tendsto (fun j => (I j).kappa) l atTop)
    (hN : Tendsto (fun j => (N j:ℝ)/sqrt (I j).kappa) l (𝓝 a)) :
    Tendsto (fun j => (I j).delta/((I j).mu*(N j:ℝ)^2)) l (𝓝 (1/a^2)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hh := normalized_drift_scale_limit ha
    (Eventually.of_forall (fun j => div_nonneg (I j).mu_pos.le (I j).delta_pos.le))
    (show Tendsto (fun j => (N j:ℝ)*sqrt ((I j).mu/(I j).delta)) l (𝓝 a) by
      simpa only [SpectralInterval.gap_ratio_eq] using condition_horizon_limit hK hN)
  convert hh using 1
  funext j
  field_simp

/--
Exact large-condition-number limit of the finite drift bound.

Convergence along the specified source filter to the specified limit: `Tendsto (fun j => (I
j).epsilon (N j)*(T ℝ (N j)).eval (1+2*r*(I j).mu/(I j).delta)) l (𝓝 (cosh (2*a*sqrt r)/cosh
(2*a)))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Remark 5.5.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem SpectralInterval.drift_factor_limit {α : Type*} {l : Filter α}
    {I : α → SpectralInterval} {N : α → ℕ} {a r : ℝ} (hr : 0 ≤ r)
    (hK : Tendsto (fun j => (I j).kappa) l atTop)
    (hN : Tendsto (fun j => (N j:ℝ)/sqrt (I j).kappa) l (𝓝 a)) :
    Tendsto (fun j => (I j).epsilon (N j)*(T ℝ (N j)).eval (1+2*r*(I j).mu/(I j).delta))
      l (𝓝 (cosh (2*a*sqrt r)/cosh (2*a))) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hh := normalized_amplification_limit hr
    (Eventually.of_forall (fun j => div_nonneg (I j).mu_pos.le (I j).delta_pos.le))
    (show Tendsto (fun j => (I j).mu/(I j).delta) l (𝓝 0) by
      simpa only [SpectralInterval.gap_ratio_eq] using condition_gap_limit hK)
    (show Tendsto (fun j => (N j:ℝ)*sqrt ((I j).mu/(I j).delta)) l (𝓝 a) by
      simpa only [SpectralInterval.gap_ratio_eq] using condition_horizon_limit hK hN)
  convert hh using 1
  funext j
  rw [SpectralInterval.epsilon, SpectralInterval.den, SpectralInterval.eta_eq_one_add]
  rw [show 2*(I j).mu/(I j).delta = 2*((I j).mu/(I j).delta) by ring,
    show 2*r*(I j).mu/(I j).delta = 2*r*((I j).mu/(I j).delta) by ring]
  ring

/--
At δ=μ the attaining static shift has residual and operator norm exactly one.

Exact identity `opNorm (R.operatorTransfer N (fun _ => scalarMatrix (I.mu-I.mu))) = 1`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Remark 5.5.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem Realization.static_shift_at_mu {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hfinal : R.residualPolynomial N = I.residual N) :
    opNorm (R.operatorTransfer N (fun _ => scalarMatrix (I.mu-I.mu))) = 1 := by
  -- Check each member of the finite index type; no case is omitted.
  rw [R.operatorTransfer_eq_aeval, hfinal]
  have he : aeval (scalarMatrix (I.mu-I.mu)) (I.residual N) = scalarMatrix 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp only [scalarMatrix, aeval_diagonal, Matrix.diagonal_apply_eq, sub_self,
      I.residual_eval_zero]
  rw [he, opNorm_scalarMatrix, abs_one]

end
end «2606.16671v2»
