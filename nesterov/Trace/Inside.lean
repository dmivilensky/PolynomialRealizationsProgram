import nesterov.Trace.Disk

/-! A positive boundary trace bounds every real radial value. This is the
rigidity argument used at the nonnegative-symbol boundary without pole estimates. -/
namespace nesterov.Trace
noncomputable section
open Complex Metric Set Real Filter MeasureTheory
open scoped Topology

def insideValue (F : ℂ→ℂ) (x : ℝ) (z : ℂ) : ℝ :=
  2*x*z.im/Complex.normSq (z-(x:ℂ))*(F z).im

private theorem kernel_conj {z : ℂ} (hz : Complex.normSq z=1) {x : ℝ} (hx : |x|<1) :
    star (z/(z-(x:ℂ)))=1/(1-(x:ℂ)*z) := by
  have hzx : z-(x:ℂ)≠0 := by
    intro h
    have he : z=(x:ℂ) := sub_eq_zero.mp h
    rw [he,Complex.normSq_ofReal] at hz
    have hh := abs_lt.mp hx
    nlinarith
  have hden : 1-(x:ℂ)*z≠0 := by
    intro h
    have hh := congrArg Complex.normSq (sub_eq_zero.mp h)
    simp only [Complex.normSq_one,Complex.normSq_mul,Complex.normSq_ofReal,hz,mul_one] at hh
    have hxx := abs_lt.mp hx
    nlinarith
  have hc : z*star z=1 := by
    change z*(starRingEnd ℂ) z=1
    rw [Complex.mul_conj]
    exact_mod_cast hz
  rw [star_div₀,star_sub,Complex.star_def,Complex.conj_ofReal]
  have hs : (starRingEnd ℂ) z-(x:ℂ)≠0 := by
    have hh := star_ne_zero.mpr hzx
    simpa only [star_sub,Complex.star_def,Complex.conj_ofReal] using hh
  apply (div_eq_div_iff hs hden).mpr
  simp only [Complex.star_def] at hc
  linear_combination -(x:ℂ)*hc

theorem insideValue_circleAverage {F : ℂ→ℂ}
    (hF : DiffContOnCl ℂ F (ball 0 1)) (hzero : F 0=0) {x : ℝ} (hx : |x|<1) :
    circleAverage (insideValue F x) 0 1=(F (x:ℂ)).re := by
  have hden (z : ℂ) (hz : z∈closedBall (0:ℂ) 1) : 1-(x:ℂ)*z≠0 := by
    have hnorm : ‖(x:ℂ)*z‖<1 := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      have hz' : ‖z‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using hz
      nlinarith [abs_nonneg x,norm_nonneg z]
    exact sub_ne_zero.mpr (fun he=>by rw [←he,norm_one] at hnorm;exact lt_irrefl _ hnorm)
  have hHH : DiffContOnCl ℂ (fun z=>F z/(1-(x:ℂ)*z)) (ball 0 1) := by
    refine ⟨hF.1.div (by fun_prop) (fun z hz=>hden z (ball_subset_closedBall hz)),?_⟩
    apply hF.2.div (by fun_prop)
    intro z hz
    exact hden z (by simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hz)
  have hHmean : circleAverage (fun z=>F z/(1-(x:ℂ)*z)) 0 1=0 := by
    have hh : DiffContOnCl ℂ (fun z=>F z/(1-(x:ℂ)*z)) (ball 0 |(1:ℝ)|) := by simpa using hHH
    simpa [hzero] using hh.circleAverage
  have hxball : (x:ℂ)∈ball (0:ℂ) |(1:ℝ)| := by simpa [Complex.norm_real,Real.norm_eq_abs] using hx
  have hC : circleAverage (fun z=>(z/(z-(x:ℂ)))*F z) 0 1=F (x:ℂ) := by
    have hh : DiffContOnCl ℂ F (ball 0 |(1:ℝ)|) := by simpa using hF
    simpa only [sub_zero,smul_eq_mul] using hh.circleAverage_smul_div hxball
  have hcF : ContinuousOn F (sphere 0 1) := hF.2.mono (by rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)];exact sphere_subset_closedBall)
  have hci : CircleIntegrable (fun z=>(z/(z-(x:ℂ)))*F z) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    apply ContinuousOn.mul _ hcF
    apply ContinuousOn.div continuousOn_id (by fun_prop)
    intro z hz
    have hn : ‖z‖=1 := by simpa [mem_sphere,dist_zero_right] using hz
    intro he
    have hz' : z=(x:ℂ) := sub_eq_zero.mp he
    rw [hz',Complex.norm_real,Real.norm_eq_abs] at hn
    exact hx.ne hn
  have hhi : CircleIntegrable (fun z=>F z/(1-(x:ℂ)*z)) 0 1 :=
    (hHH.2.mono (by rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)];exact sphere_subset_closedBall)).circleIntegrable (by norm_num)
  have hdiff : circleAverage (fun z=>(z/(z-(x:ℂ)))*F z-F z/(1-(x:ℂ)*z)) 0 1=F (x:ℂ) := by
    rw [circleAverage_fun_sub hci hhi,hC,hHmean,sub_zero]
  have hr := Complex.reCLM.circleAverage_comp_comm (CircleIntegrable.sub hci hhi)
  change circleAverage (fun z=>((z/(z-(x:ℂ)))*F z-F z/(1-(x:ℂ)*z)).re) 0 1=
    (circleAverage (fun z=>(z/(z-(x:ℂ)))*F z-F z/(1-(x:ℂ)*z)) 0 1).re at hr
  rw [hdiff] at hr
  rw [←hr]
  apply circleAverage_congr_sphere
  intro z hz
  have hzn : Complex.normSq z=1 := by
    rw [Complex.normSq_eq_norm_sq]
    have hn : ‖z‖=1 := by simpa [mem_sphere,dist_zero_right] using hz
    rw [hn,one_pow]
  change insideValue F x z=((z/(z-(x:ℂ)))*F z-F z/(1-(x:ℂ)*z)).re
  have hk := kernel_conj hzn hx
  rw [show F z/(1-(x:ℂ)*z)=(1/(1-(x:ℂ)*z))*F z by ring,←hk,←sub_mul]
  unfold insideValue
  simp only [Complex.sub_re,Complex.mul_re,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.div_im,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,sub_zero]
  ring

end
end nesterov.Trace
