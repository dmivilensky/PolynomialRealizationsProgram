import nesterov.Trace.Inside

/-! The positive trace kernel bounds all real radial values, including the
boundary value at 1. This yields rigidity without a singular integral limit. -/
namespace nesterov.Trace
noncomputable section
open Complex Metric Set Real
open scoped Topology

theorem insideValue_bounds {F : ℂ→ℂ} {z : ℂ} (hz : Complex.normSq z=1)
    (hreal : (F 1).im=0) (hB : 0≤boundaryValue F z) {x : ℝ} (hx0 : 0<x) (hx1 : x<1) :
    0 ≤ insideValue F x z ∧ insideValue F x z≤boundaryValue F z := by
  by_cases hz1 : z=1
  · subst z
    simpa [insideValue] using hB
  have hd : 0<1-z.re := by
    have hre : z.re≤1 := by
      have hn : ‖z‖=1 := by
        rw [←sq_eq_sq₀ (norm_nonneg z) (by norm_num : (0:ℝ)≤1),Complex.sq_norm]
        simpa using hz
      exact (Complex.re_le_norm z).trans hn.le
    refine lt_of_le_of_ne (sub_nonneg.mpr hre) ?_
    intro he
    have hr : z.re=1 := by linarith
    have hi : z.im=0 := by simp only [Complex.normSq_apply,hr] at hz;nlinarith
    exact hz1 (Complex.ext hr hi)
  have hden : 0<Complex.normSq (z-(x:ℂ)) := by
    apply Complex.normSq_pos.mpr
    intro he
    have hz' : z=(x:ℂ) := sub_eq_zero.mp he
    rw [hz',Complex.normSq_ofReal] at hz
    nlinarith
  have hde : 2*x*(1-z.re)≤Complex.normSq (z-(x:ℂ)) := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
      Complex.ofReal_im,sub_zero] at hz ⊢
    nlinarith [sq_nonneg (x-1)]
  have hBe : boundaryValue F z=(z.im*(F z).im)/(1-z.re) := by
    rw [boundaryValue_eq_weighted_im hz hz1 hreal]
    ring
  have hC : 0≤z.im*(F z).im := by
    rw [hBe] at hB
    simpa only [zero_mul] using (le_div_iff₀ hd).mp hB
  have hi : insideValue F x z=(2*x*(z.im*(F z).im))/Complex.normSq (z-(x:ℂ)) := by
    unfold insideValue
    ring
  rw [hi,hBe]
  refine ⟨div_nonneg (by positivity) hden.le,?_⟩
  apply (div_le_div_iff₀ hden hd).mpr
  nlinarith [mul_le_mul_of_nonneg_right hde hC]

theorem radial_comparison {F : ℂ→ℂ}
    (hF : DiffContOnCl ℂ F (ball 0 1))
    (hG : DiffContOnCl ℂ (dslope F 1) (ball 0 1))
    (hzero : F 0=0) (hreal : (F 1).im=0)
    (hB : ∀ z∈sphere (0:ℂ) 1,0≤boundaryValue F z) {x : ℝ} (hx0 : 0<x) (hx1 : x<1) :
    0≤(F (x:ℂ)).re ∧ (F (x:ℂ)).re≤(F 1).re := by
  have hx : |x|<1 := by rwa [abs_of_pos hx0]
  have hfc : ContinuousOn F (sphere (0:ℂ) 1) := hF.2.mono (by
    rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)]
    exact sphere_subset_closedBall)
  have hii : CircleIntegrable (insideValue F x) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    unfold insideValue
    apply ContinuousOn.mul _ (Complex.continuous_im.comp_continuousOn hfc)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro z hz
    apply (Complex.normSq_pos.mpr ?_).ne'
    intro he
    have hz' : z=(x:ℂ) := sub_eq_zero.mp he
    have hn : ‖z‖=1 := by simpa only [mem_sphere,dist_zero_right] using hz
    rw [hz',Complex.norm_real,Real.norm_eq_abs] at hn
    exact hx.ne hn
  have hbi : CircleIntegrable (boundaryValue F) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    apply (boundaryValue_continuousOn ?_ ?_).mono sphere_subset_closedBall
    · simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hF.2
    · simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hG.2
  have hp (z : ℂ) (hz : z∈sphere (0:ℂ) |(1:ℝ)|) :
      0 ≤ insideValue F x z ∧ insideValue F x z≤boundaryValue F z := by
    have hz' : z∈sphere (0:ℂ) 1 := by simpa using hz
    have hn : ‖z‖=1 := by simpa only [mem_sphere,dist_zero_right] using hz'
    have hns : Complex.normSq z=1 := by rw [Complex.normSq_eq_norm_sq,hn,one_pow]
    exact insideValue_bounds hns hreal (hB z hz') hx0 hx1
  have hlo := circleAverage_nonneg_of_nonneg (fun z hz=>(hp z hz).1)
  have hhi := circleAverage_mono hii hbi (fun z hz=>(hp z hz).2)
  rw [insideValue_circleAverage hF hzero hx] at hlo hhi
  rw [boundaryValue_circleAverage hF hG,hzero,Complex.zero_re,sub_zero] at hhi
  exact ⟨hlo,hhi⟩

end
end nesterov.Trace
