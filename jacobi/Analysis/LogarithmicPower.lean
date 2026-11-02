import jacobi.Analysis.AsymptoticSlope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field

/-!
Article: jacobi, Proposition C.4.
A positive leading power coefficient fixes the logarithmic exponent.
This elementary limit is used for the genuine packed density, whose
profile power and coordinate asymptotics are established separately.
Use: supercritical_density_coordinate_tail computes log(phi_alpha(t)^2)/log(t) from the actual original linear profile asymptotic.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter
open scoped Topology

/-- A genuine endpoint power asymptotic with positive coefficient has exactly the corresponding logarithmic exponent.
Use: supercritical_density_coordinate_tail computes log(phi_alpha(t)^2)/log(t) from the actual original linear profile asymptotic.
Article: jacobi, Proposition C.4.
Proof: the logarithm of the positive normalized ratio tends to the finite log(c), hence vanishes after division by log(t). Expand that logarithm on the actual positive endpoint filter. -/
theorem logarithmic_power_limit {f : ℝ → ℝ} {p c : ℝ} (hc : 0<c)
    (hf : Tendsto (fun t : ℝ => f t/t^p) (𝓝[>] (0:ℝ)) (𝓝 c)) :
    Tendsto (fun t : ℝ => log (f t)/log t) (𝓝[>] (0:ℝ)) (𝓝 p) := by
  -- Only the true positive normalized ratio is logged, so no sign assumption is hidden in the logarithmic expansion.
  have hl := ((Real.continuousAt_log hc.ne').tendsto.comp hf).div_atBot tendsto_log_nhdsGT_zero
  have h := hl.add_const p
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),
    hf.eventually (Ioi_mem_nhds hc)] with t ht hpos
  have hp := Real.rpow_pos_of_pos ht.1 p
  have hfp : 0<f t := by have h := (lt_div_iff₀ hp).mp hpos; simpa only [zero_mul] using h
  dsimp only [Function.comp_def]
  rw [Real.log_div hfp.ne' hp.ne',Real.log_rpow ht.1 p]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one ht.1 ht.2.ne]
  ring

end
end jacobi.Analysis
