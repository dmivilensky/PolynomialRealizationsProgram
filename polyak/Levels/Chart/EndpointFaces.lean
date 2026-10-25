import polyak.Levels.Chart.Coefficients

/-! The two endpoint faces of coefficient space. The +1 face forces the
condition number to infinity; the -1 face reaches the quadratic stability
line, including the exceptional K=2 side of a gap. -/
noncomputable section
namespace polyak.Levels.Chart
open General Filter
open scoped Topology

theorem Xi_one_identity (q : Tuning) :
    q.Xi 1= -q.y/((q.kappa-1)*(1-q.beta)) := by
  have hk := ne_of_gt q.kappa_pos
  have hk1 := ne_of_gt (sub_pos.mpr q.kappa_gt_one)
  have hd := ne_of_gt (sub_pos.mpr q.beta_lt_one)
  have hy := ne_of_gt q.y_pos
  dsimp [Tuning.Xi,Tuning.A,Tuning.B,Tuning.x]
  field_simp [hk,hk1,hd,hy]
  ring

theorem Xi_neg_one_identity (q : Tuning) :
    q.Xi (-1)*(q.y-q.x)*(1-q.beta)=
      -(2+2*q.beta-q.x)*(2+2*q.beta-q.y) := by
  have hd := ne_of_gt (sub_pos.mpr q.beta_lt_one)
  have hxy := ne_of_gt (sub_pos.mpr q.x_lt_y)
  dsimp [Tuning.Xi,Tuning.A,Tuning.B]
  field_simp [hd,hxy]
  ring

theorem stability_gap_pos (q : Tuning) : 0<2*(1+q.beta)-q.y := by linarith [q.y_lt]

theorem stability_gap_le_endpoint (q : Tuning) :
    2*(1+q.beta)-q.y≤ -q.Xi (-1) := by
  have hid := Xi_neg_one_identity q
  have hxy := sub_pos.mpr q.x_lt_y
  have hg := stability_gap_pos q
  have hleft : 0<2+2*q.beta-q.x := by linarith [q.y_lt,q.x_lt_y]
  have he : (q.y-q.x)*(1-q.beta)≤2+2*q.beta-q.x := by
    have hm := mul_nonneg hxy.le q.beta_nonneg
    linarith [q.y_lt]
  have hh := mul_le_mul_of_nonneg_left he (neg_pos.mpr q.Xi_neg_one_neg).le
  nlinarith

theorem y_lower_bound_from_endpoint (q : Tuning) :
    1/(1-q.Xi (-1))≤q.y := by
  have hM : 0<1-q.Xi (-1) := by linarith [q.Xi_neg_one_neg]
  apply (div_le_iff₀ hM).mpr
  by_cases hy : 1≤q.y
  · have hh := mul_nonneg q.y_pos.le (neg_pos.mpr q.Xi_neg_one_neg).le
    nlinarith
  have hy1 : q.y<1 := lt_of_not_ge hy
  have hid := Xi_neg_one_identity q
  have hxy : 0<q.y-q.x := sub_pos.mpr q.x_lt_y
  have hM0 : 0< -q.Xi (-1) := neg_pos.mpr q.Xi_neg_one_neg
  have hupper : (q.y-q.x)*(1-q.beta)≤q.y := by
    nlinarith [mul_nonneg hxy.le q.beta_nonneg,q.x_pos]
  have hmul := mul_le_mul_of_nonneg_left hupper hM0.le
  have hfa : 1<2+2*q.beta-q.x := by linarith [q.beta_nonneg,q.x_lt_y]
  have hfb : 1<2+2*q.beta-q.y := by linarith [q.beta_nonneg]
  nlinarith [mul_pos (by linarith : 0<1-q.y) (by linarith : 0<1-q.x)]

theorem kappa_endpoint_lower_bound (q : Tuning) :
    1≤(1-q.Xi (-1))*(-q.Xi 1)*(q.kappa-1) := by
  have hX : 0< -q.Xi 1 := neg_pos.mpr q.Xi_one_neg
  have hκ : 0<q.kappa-1 := sub_pos.mpr q.kappa_gt_one
  have hden : 0<1-q.Xi (-1) := by linarith [q.Xi_neg_one_neg]
  have hy := (div_le_iff₀ hden).mp (y_lower_bound_from_endpoint q)
  have he : q.y=(-q.Xi 1)*(q.kappa-1)*(1-q.beta) := by
    rw [Xi_one_identity]
    field_simp [ne_of_gt (sub_pos.mpr q.beta_lt_one)]
  have hsmall : q.y≤(-q.Xi 1)*(q.kappa-1) := by
    rw [he]
    have hp := mul_nonneg (mul_pos hX hκ).le q.beta_nonneg
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hsmall hden.le
  nlinarith

/-- The source +1 face forces κ→∞, with only endpoint convergence needed. -/
theorem kappa_tendsto_atTop_of_endpoint_face {ι : Type*} {l : Filter ι}
    [NeBot l] (q : ι→Tuning) {b : ℝ}
    (hplus : Tendsto (fun i=>(q i).Xi 1) l (𝓝 0))
    (hminus : Tendsto (fun i=>(q i).Xi (-1)) l (𝓝 b)) :
    Tendsto (fun i=>(q i).kappa) l atTop := by
  rw [tendsto_atTop]
  intro R
  let M := max R 2
  have hM : 1<M := by have := le_max_right R 2; dsimp [M]; linarith
  have ht : Tendsto (fun i=>(1-(q i).Xi (-1))*(-(q i).Xi 1)*(M-1)) l (𝓝 0) := by
    simpa only [neg_zero,mul_zero,zero_mul] using
      (((tendsto_const_nhds.sub hminus).mul hplus.neg).mul_const (M-1))
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with i hi
  have hbnd := kappa_endpoint_lower_bound (q i)
  have hprod : 0<(1-(q i).Xi (-1))*(-(q i).Xi 1) := by
    apply mul_pos <;> linarith [(q i).Xi_one_neg,(q i).Xi_neg_one_neg]
  have hk : M<(q i).kappa := by nlinarith
  exact (le_max_left R 2).trans hk.le

theorem stability_gap_tendsto_zero_of_endpoint_face {ι : Type*} {l : Filter ι}
    (q : ι→Tuning) (hminus : Tendsto (fun i=>(q i).Xi (-1)) l (𝓝 0)) :
    Tendsto (fun i=>2*(1+(q i).beta)-(q i).y) l (𝓝 0) := by
  apply squeeze_zero (fun i=>(stability_gap_pos (q i)).le)
    (fun i=>stability_gap_le_endpoint (q i))
  simpa only [neg_zero] using hminus.neg

end polyak.Levels.Chart
