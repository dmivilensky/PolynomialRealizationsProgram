import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Article: jacobi, Proposition C.4.
A derivative tending to a constant fixes the linear asymptotic of its
primitive. Exponential coordinates give the corresponding logarithmic
endpoint statement. These elementary mean-value arguments are used for
the actual Green diagonal and intrinsic packing coordinate.
Source: Lagrange's mean value theorem.
Use: logarithmic_endpoint_limit passes from the genuine singular derivative to its logarithmic primitive, as required by Proposition C.4.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter
open scoped Topology

/-- An eventually differentiable real function whose derivative tends to L has asymptotic slope L.
Use: logarithmic_endpoint_limit passes from the genuine singular derivative to its logarithmic primitive, as required by Proposition C.4.
Article: jacobi, Proposition C.4.
Source: Lagrange's mean value theorem, with the finite initial interval divided by x.
Proof: beyond a fixed positive point the derivative differs from L by
less than epsilon/2. The mean value theorem bounds the corresponding
secant error; the remaining fixed numerator divided by x tends to zero. -/
theorem asymptotic_slope {f f':ℝ→ℝ} {L:ℝ}
    (hd:∀ᶠ x in atTop,HasDerivAt f (f' x) x)
    (hl:Tendsto f' atTop (𝓝 L)) :
    Tendsto (fun x:ℝ=>f x/x) atTop (𝓝 L) := by
  -- The fixed initial value contributes only a constant-over-x error.
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨A,hA⟩ := eventually_atTop.mp
    (hd.and (hl.eventually (Metric.ball_mem_nhds L (half_pos he))))
  let B := max A 0
  have hB : 0≤B := le_max_right _ _
  have hb : A≤B := le_max_left _ _
  have hc : Tendsto (fun x:ℝ=>(f B-L*B)/x) atTop (𝓝 0) := by
    simpa only [mul_zero,div_eq_mul_inv] using
      tendsto_inv_atTop_zero.const_mul (f B-L*B)
  filter_upwards [eventually_gt_atTop B,
    hc.eventually (Metric.ball_mem_nhds 0 (half_pos he))] with x hx herr
  obtain ⟨c,hc,hmean⟩ := exists_hasDerivAt_eq_slope f f' hx
    (fun y hy=>(hA y (hb.trans hy.1)).1.continuousAt.continuousWithinAt)
    (fun y hy=>(hA y (hb.trans hy.1.le)).1)
  have hder : |f' c-L|<e/2 := by
    simpa only [Metric.mem_ball,Real.dist_eq] using (hA c (hb.trans hc.1.le)).2
  have hxp : 0<x := hB.trans_lt hx
  have ht : 0≤(x-B)/x := div_nonneg (sub_pos.mpr hx).le hxp.le
  have htle : (x-B)/x≤1 := (div_le_one hxp).mpr (by linarith)
  have heq : f x/x-L=(f' c-L)*((x-B)/x)+(f B-L*B)/x := by
    rw [hmean]
    field_simp [hxp.ne',(sub_pos.mpr hx).ne']
    ring
  rw [Real.dist_eq,heq]
  calc
    _ ≤ |f' c-L| *((x-B)/x)+|(f B-L*B)/x| := by
      simpa only [abs_mul,abs_of_nonneg ht] using abs_add_le
        ((f' c-L)*((x-B)/x)) ((f B-L*B)/x)
    _ ≤ |f' c-L|+|(f B-L*B)/x| := by
      nlinarith [mul_le_of_le_one_right (abs_nonneg (f' c-L)) htle]
    _ < e := by
      have hh : |(f B-L*B)/x|<e/2 := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using herr
      linarith

/-- An actual real derivative with t*f'(t)->L has the exact logarithmic endpoint primitive f(t)/log(t)->L.
Use: the critical sine endpoint and the divergent intrinsic packing coordinates use this theorem with their proved genuine derivatives.
Article: jacobi, Proposition C.4.
Source: the mean value theorem in the exponential coordinate t=exp(-x).
Proof: the composed function has derivative -exp(-x)*f'(exp(-x)),
which tends to -L. Its asymptotic slope is therefore -L. Substitute
x=-log(t), where exp(log(t))=t for every positive endpoint argument. -/
theorem logarithmic_endpoint_limit {f f':ℝ→ℝ} {L:ℝ}
    (hd:∀ᶠ t in 𝓝[>] (0:ℝ),HasDerivAt f (f' t) t)
    (hl:Tendsto (fun t:ℝ=>t*f' t) (𝓝[>] (0:ℝ)) (𝓝 L)) :
    Tendsto (fun t:ℝ=>f t/log t) (𝓝[>] (0:ℝ)) (𝓝 L) := by
  -- Exponential coordinates retain the full punctured endpoint filter.
  have ht : Tendsto (fun x:ℝ=>exp (-x)) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_exp_atBot_nhdsGT.comp tendsto_neg_atTop_atBot
  have hh : ∀ᶠ x:ℝ in atTop,
      HasDerivAt (fun y:ℝ=>f (exp (-y))) (-exp (-x)*f' (exp (-x))) x := by
    filter_upwards [ht.eventually hd] with x hx
    convert hx.comp x (((hasDerivAt_id x).neg).exp) using 1
    · rfl
    · dsimp only [Pi.neg_apply,id_eq]
      ring
  have hp : Tendsto (fun x:ℝ=>-exp (-x)*f' (exp (-x))) atTop (𝓝 (-L)) := by
    simpa only [Function.comp_def,neg_mul] using (hl.comp ht).neg
  have hs := (asymptotic_slope hh hp).neg
  have hlog := tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
  have h := hs.comp hlog
  simp only [Function.comp_def,neg_neg] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [self_mem_nhdsWithin] with t htpos
  rw [exp_log htpos]
  ring

end
end jacobi.Analysis
