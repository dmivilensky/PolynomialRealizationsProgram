import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
Article: Theorem `trace`, analytic trace identity on the closed unit disk.
Use: apply the mean-value theorem to a holomorphic function and its divided
slope at 1. This proves the boundary identity without a singular kernel limit.
-/
namespace nesterov.Trace
noncomputable section
open Complex Metric Set Real
open scoped Topology

/-- A continuous representative of the weighted imaginary boundary value. -/
def boundaryValue (F : ℂ→ℂ) (z : ℂ) : ℝ :=
  2*(dslope F 1 z).re+(F z).re-(F 1).re

theorem boundaryValue_continuousOn {F : ℂ→ℂ}
    (hF : ContinuousOn F (closedBall 0 1))
    (hG : ContinuousOn (dslope F 1) (closedBall 0 1)) :
    ContinuousOn (boundaryValue F) (closedBall 0 1) := by
  unfold boundaryValue
  exact ((continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hG)).add
    (Complex.continuous_re.comp_continuousOn hF)).sub continuousOn_const

theorem boundaryValue_circleAverage {F : ℂ→ℂ}
    (hF : DiffContOnCl ℂ F (ball 0 1))
    (hG : DiffContOnCl ℂ (dslope F 1) (ball 0 1)) :
    circleAverage (boundaryValue F) 0 1=(F 1).re-(F 0).re := by
  have hfc : CircleIntegrable F 0 1 :=
    (hF.2.mono (by rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)];exact sphere_subset_closedBall)).circleIntegrable (by norm_num)
  have hgc : CircleIntegrable (dslope F 1) 0 1 :=
    (hG.2.mono (by rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)];exact sphere_subset_closedBall)).circleIntegrable (by norm_num)
  have hfR := Complex.reCLM.circleAverage_comp_comm hfc
  have hgR := Complex.reCLM.circleAverage_comp_comm hgc
  have hfI : CircleIntegrable (fun z=>(F z).re) 0 1 := by
    exact (Complex.continuous_re.comp_continuousOn (hF.2.mono (by rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)];exact sphere_subset_closedBall))).circleIntegrable (by norm_num)
  have hgI : CircleIntegrable (fun z=>(dslope F 1 z).re) 0 1 := by
    exact (Complex.continuous_re.comp_continuousOn (hG.2.mono (by rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)];exact sphere_subset_closedBall))).circleIntegrable (by norm_num)
  have hvF : circleAverage F 0 1=F 0 := by
    have hh : DiffContOnCl ℂ F (ball 0 |(1:ℝ)|) := by simpa using hF
    exact hh.circleAverage
  have hvG : circleAverage (dslope F 1) 0 1=dslope F 1 0 := by
    have hh : DiffContOnCl ℂ (dslope F 1) (ball 0 |(1:ℝ)|) := by simpa using hG
    exact hh.circleAverage
  rw [hvF] at hfR
  rw [hvG] at hgR
  have h2g : CircleIntegrable (fun z=>2*(dslope F 1 z).re) 0 1 := by
    change IntervalIntegrable (fun θ=>2*(dslope F 1 (circleMap 0 1 θ)).re) MeasureTheory.volume 0 (2*Real.pi)
    exact hgI.const_mul 2
  have hsum : CircleIntegrable (fun z=>2*(dslope F 1 z).re+(F z).re) 0 1 := CircleIntegrable.add h2g hfI
  unfold boundaryValue
  rw [circleAverage_fun_sub hsum (circleIntegrable_const _ _ _),
    circleAverage_fun_add h2g hfI]
  simp only [←smul_eq_mul, circleAverage_fun_smul, circleAverage_const]
  change 2*circleAverage (fun z=>(dslope F 1 z).re) 0 1+
    circleAverage (fun z=>(F z).re) 0 1-(F 1).re=_
  change circleAverage (fun z=>(F z).re) 0 1=(F 0).re at hfR
  change circleAverage (fun z=>(dslope F 1 z).re) 0 1=(dslope F 1 0).re at hgR
  rw [hfR,hgR]
  rw [dslope_of_ne F (by norm_num : (0:ℂ)≠1),slope_def_field]
  simp only [zero_sub,div_neg,div_one,neg_re,sub_re]
  ring

theorem boundaryValue_eq_weighted_im {F : ℂ→ℂ} {z : ℂ}
    (hz : Complex.normSq z=1) (hne : z≠1) (hreal : (F 1).im=0) :
    boundaryValue F z=z.im/(1-z.re)*(F z).im := by
  have hn : 1-z.re≠0 := by
    intro hh
    have hr : z.re=1 := by linarith
    have hi : z.im=0 := by simp only [Complex.normSq_apply,hr] at hz;nlinarith
    exact hne (Complex.ext hr hi)
  have hd : Complex.normSq (z-1)=2*(1-z.re) := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero] at hz ⊢
    nlinarith
  unfold boundaryValue
  rw [dslope_of_ne F hne,slope_def_field]
  simp only [div_eq_mul_inv,Complex.mul_re,Complex.inv_re,Complex.inv_im,
    Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero,hreal,hd]
  field_simp [hn]
  ring

end
end nesterov.Trace
