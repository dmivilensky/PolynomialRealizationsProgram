import jacobi.Analysis.LogarithmicPower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Article: jacobi, Proposition C.4.
A positive relative asymptotic against a divergent scale has the same
logarithmic exponent. This is the elementary limit used after the
actual critical profile and packing-coordinate estimates are proved.
Use: the critical density tail applies this limit to log(1/m_alpha) versus log(1/t), keeping the same actual source density and coordinate.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter
open scoped Topology

/-- Positive finite relative asymptotics against a truly divergent scale preserve logarithmic growth.
Use: the critical density tail applies this limit to log(1/m_alpha) versus log(1/t), keeping the same actual source density and coordinate.
Article: jacobi, Proposition C.4.
Proof: log(f/g) has a finite limit and log(g) tends to infinity. Divide the identity log(f)=log(f/g)+log(g) by log(g) on the eventual positive filter. -/
theorem logarithmic_ratio_limit {ι : Type*} {l : Filter ι} {f g : ι → ℝ} {c : ℝ}
    (hc : 0<c) (hg : Tendsto g l atTop) (hf : Tendsto (fun t => f t/g t) l (𝓝 c)) :
    Tendsto (fun t => log (f t)/log (g t)) l (𝓝 1) := by
  -- The positive relative limit fixes the genuine sign before logarithms are expanded.
  have hl := ((Real.continuousAt_log hc.ne').tendsto.comp hf).div_atTop (tendsto_log_atTop.comp hg)
  have h := hl.add_const 1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [hg.eventually (eventually_gt_atTop (1:ℝ)),hf.eventually (Ioi_mem_nhds hc)] with t ht hpos
  have hgp : 0<g t := lt_trans zero_lt_one ht
  have hfp : 0<f t := by have hh := (lt_div_iff₀ hgp).mp hpos; simpa only [zero_mul] using hh
  dsimp only [Function.comp_def]
  rw [Real.log_div hfp.ne' hgp.ne']
  field_simp [(Real.log_pos ht).ne']
  ring

end
end jacobi.Analysis
