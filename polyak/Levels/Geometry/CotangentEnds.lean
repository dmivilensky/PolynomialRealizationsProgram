import polyak.Levels.Geometry.Ends
import Mathlib.Topology.Algebra.Order.Field

/-! The true cotangent tends to minus infinity at both ends. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set Filter
open scoped Topology

theorem cotangent_tendsto_zero_right (q : Tuning) :
    Tendsto (cotangent q) (𝓝[>] (0:ℝ)) atBot := by
  have hn : Tendsto (fun ω=>q.Xi (Real.cos ω)) (𝓝[>] (0:ℝ)) (𝓝 (q.Xi 1)) := by
    have hc : Continuous (fun ω : ℝ=>q.Xi (Real.cos ω)) := by
      rw [show (fun ω : ℝ=>q.Xi (Real.cos ω))=(fun ω=>(Chart.coefficients q).eval (Real.cos ω)) by funext ω; exact (Chart.eval_coefficients q _).symm]
      unfold Chart.Coefficients.eval
      fun_prop
    simpa only [Real.cos_zero] using (hc.continuousAt (x:=0)).tendsto.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  have hs : Tendsto Real.sin (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [Real.sin_zero] using (Real.continuous_sin.continuousAt (x:=0)).tendsto.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds Real.pi_pos)] with ω hω hp
      exact Real.sin_pos_of_pos_of_lt_pi hω hp
  change Tendsto (fun ω=>q.Xi (Real.cos ω)/Real.sin ω) (𝓝[>] (0:ℝ)) atBot
  simpa only [div_eq_mul_inv,Function.comp_def] using hn.neg_mul_atTop q.Xi_one_neg (tendsto_inv_nhdsGT_zero.comp hs)

theorem cotangent_tendsto_pi_left (q : Tuning) :
    Tendsto (cotangent q) (𝓝[<] Real.pi) atBot := by
  have hn : Tendsto (fun ω=>q.Xi (Real.cos ω)) (𝓝[<] Real.pi) (𝓝 (q.Xi (-1))) := by
    have hc : Continuous (fun ω : ℝ=>q.Xi (Real.cos ω)) := by
      rw [show (fun ω : ℝ=>q.Xi (Real.cos ω))=(fun ω=>(Chart.coefficients q).eval (Real.cos ω)) by funext ω; exact (Chart.eval_coefficients q _).symm]
      unfold Chart.Coefficients.eval
      fun_prop
    simpa only [Real.cos_pi] using (hc.continuousAt (x:=Real.pi)).tendsto.mono_left (show 𝓝[<] Real.pi≤𝓝 Real.pi from nhdsWithin_le_nhds)
  have hs : Tendsto Real.sin (𝓝[<] Real.pi) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [Real.sin_pi] using (Real.continuous_sin.continuousAt (x:=Real.pi)).tendsto.mono_left (show 𝓝[<] Real.pi≤𝓝 Real.pi from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds Real.pi_pos)] with ω hω hp
      exact Real.sin_pos_of_pos_of_lt_pi hp hω
  change Tendsto (fun ω=>q.Xi (Real.cos ω)/Real.sin ω) (𝓝[<] Real.pi) atBot
  simpa only [div_eq_mul_inv,Function.comp_def] using hn.neg_mul_atTop q.Xi_neg_one_neg (tendsto_inv_nhdsGT_zero.comp hs)

end polyak.Levels.Geometry
