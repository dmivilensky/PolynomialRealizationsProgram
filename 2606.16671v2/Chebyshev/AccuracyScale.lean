import «2606.16671v2».Chebyshev.DriftScale
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: 2606.16671v2, Remark 5.5.
The scale 4 μ/log²(2/ε) in Remark 5.5 follows from the large-condition limit.
Result: `«2606.16671v2».SpectralInterval.logarithmic_drift_scale_limit` supplies the stated article
conclusion.
-/
namespace «2606.16671v2»
noncomputable section
open Real Filter Topology
set_option backward.isDefEq.respectTransparency false

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun v : ℝ =>
cosh v/(exp v/2)) atTop (𝓝 1)`.

Use: `«2606.16671v2».low_accuracy_amplification_ratio_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun epsilon : ℝ
=> cosh (log (2/epsilon)*sqrt r)/ ((1/2:ℝ)*(2/epsilon)^sqrt r)) (𝓝[>] 0) (𝓝 1)`.

Article: 2606.16671v2, Remark 5.5 via `«2606.16671v2».low_accuracy_amplification_ratio_limit`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem cosh_exp_ratio_limit :
    Tendsto (fun v : ℝ => cosh v/(exp v/2)) atTop (𝓝 1) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hh := tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
  have hl := (tendsto_const_nhds (x := (1:ℝ))).add hh
  simp only [add_zero] at hl
  apply hl.congr
  intro v
  change 1+exp (-(2*v)) = cosh v/(exp v/2)
  rw [cosh_eq]
  have he : exp (-(2*v)) = exp (-v)/exp v := by rw [← exp_sub]; congr 1; ring
  rw [he]
  field_simp

/--
The logarithmic accuracy approximation has an exact relative correction.

Exact identity `1/cosh (log (2/epsilon)) = epsilon/(1+epsilon^2/4)`.

Use: `«2606.16671v2».terminal_log_accuracy_ratio_limit` rewrites with this identity to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun
epsilon : ℝ => (1/cosh (log (2/epsilon)))/epsilon) (𝓝[>] 0) (𝓝 1)`.

Article: 2606.16671v2, Remark 5.5 via `«2606.16671v2».terminal_log_accuracy_ratio_limit`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem terminal_log_accuracy_exact {epsilon : ℝ} (he : 0 < epsilon) :
    1/cosh (log (2/epsilon)) = epsilon/(1+epsilon^2/4) := by
  rw [cosh_eq, exp_log (by positivity), exp_neg, exp_log (by positivity)]
  field_simp
  ring

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun epsilon : ℝ
=> (1/cosh (log (2/epsilon)))/epsilon) (𝓝[>] 0) (𝓝 1)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Remark 5.5.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem terminal_log_accuracy_ratio_limit :
    Tendsto (fun epsilon : ℝ => (1/cosh (log (2/epsilon)))/epsilon)
      (𝓝[>] 0) (𝓝 1) := by
  -- Record the convergence he with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have he : Tendsto (fun epsilon : ℝ => 1/(1+epsilon^2/4)) (𝓝[>] 0) (𝓝 1) := by
    -- Record the convergence hh with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hh : Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hp := (tendsto_const_nhds (x := (1:ℝ))).div
      ((tendsto_const_nhds (x := (1:ℝ))).add ((hh.pow 2).div_const 4)) (by norm_num : (1:ℝ)+0^2/4 ≠ 0)
    change Tendsto (fun epsilon : ℝ => 1/(1+epsilon^2/4)) (𝓝[>] 0)
      (𝓝 (1/(1+0^2/4))) at hp
    simpa using hp
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon heps
  have hp : 0 < epsilon := heps
  rw [terminal_log_accuracy_exact heps]
  field_simp [hp.ne']

/--
The exponential approximation to amplification, for each fixed positive drift fraction. At r=0
the exact factor is 1, so the approximation with prefactor 1/2 does not apply.

Convergence along the specified source filter to the specified limit: `Tendsto (fun epsilon : ℝ
=> cosh (log (2/epsilon)*sqrt r)/ ((1/2:ℝ)*(2/epsilon)^sqrt r)) (𝓝[>] 0) (𝓝 1)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Remark 5.5.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem low_accuracy_amplification_ratio_limit {r : ℝ} (hr : 0 < r) :
    Tendsto (fun epsilon : ℝ => cosh (log (2/epsilon)*sqrt r)/
      ((1/2:ℝ)*(2/epsilon)^sqrt r)) (𝓝[>] 0) (𝓝 1) := by
  -- Record the convergence hlog with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hlog : Tendsto (fun epsilon : ℝ => log (2/epsilon)) (𝓝[>] 0) atTop := by
    -- Record the convergence hi with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hi : Tendsto (fun epsilon : ℝ => epsilon⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero
    have ht := hi.const_mul_atTop (by norm_num : (0:ℝ) < 2)
    simpa only [Function.comp_def, div_eq_mul_inv] using tendsto_log_atTop.comp ht
  have hh := cosh_exp_ratio_limit.comp (hlog.const_mul_atTop (sqrt_pos.mpr hr))
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon heps
  simp only [Function.comp_def]
  have hp : 0 < epsilon := heps
  rw [rpow_def_of_pos (by positivity : (0:ℝ) < 2/epsilon), mul_comm (sqrt r)]
  ring

/--
The scale 4 μ/log²(2/ε) in Remark 5.5 follows from the large-condition limit.

Convergence along the specified source filter to the specified limit: `Tendsto (fun j => (I
j).delta/((I j).mu*(N j:ℝ)^2)) l (𝓝 (4/(log (2/epsilon))^2))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Remark 5.5.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem SpectralInterval.logarithmic_drift_scale_limit {α : Type*} {l : Filter α}
    {I : α → SpectralInterval} {N : α → ℕ} {epsilon : ℝ}
    (he : 0 < epsilon) (he2 : epsilon < 2)
    (hK : Tendsto (fun j => (I j).kappa) l atTop)
    (hN : Tendsto (fun j => (N j:ℝ)/sqrt (I j).kappa) l (𝓝 (log (2/epsilon)/2))) :
    Tendsto (fun j => (I j).delta/((I j).mu*(N j:ℝ)^2)) l
      (𝓝 (4/(log (2/epsilon))^2)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hl : 0 < log (2/epsilon) := log_pos ((one_lt_div he).mpr he2)
  convert SpectralInterval.drift_scale_limit (div_ne_zero hl.ne' (by norm_num)) hK hN using 1
  congr 1
  field_simp
  norm_num

end
end «2606.16671v2»
