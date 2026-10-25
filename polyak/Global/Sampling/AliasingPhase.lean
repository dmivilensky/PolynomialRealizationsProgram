import polyak.Global.Sampling.Phase
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! The genuine second right derivative of the mirrored source phase.
Its jump at π is retained, rather than replaced by a global C2 claim. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General Set MeasureTheory

def phaseSecond (q : Tuning) (s x : ℝ) : ℝ :=
  if x < Real.pi then deriv (deriv (phaseBranch q s)) x
  else -deriv (deriv (phaseBranch q s)) (2*Real.pi-x)

@[fun_prop] theorem continuous_phaseDerivative (q : Tuning) (s : ℝ) :
    Continuous (phaseDerivative q s) := by
  apply continuous_periodicExtension Real.two_pi_pos (mirrorDerivative_ends q s)
  exact continuousOn_mirrorDerivative (fun x hx =>
    (analyticAt_phaseBranch q s hx).deriv.continuousAt)

theorem phaseDerivative_periodic (q : Tuning) (s : ℝ) :
    Function.Periodic (phaseDerivative q s) (2*Real.pi) :=
  periodicExtension_periodic _ _

theorem hasDerivWithinAt_phaseDerivative_right (q : Tuning) (s : ℝ)
    {x : ℝ} (hx : x ∈ Ioo 0 (2*Real.pi)) :
    HasDerivWithinAt (phaseDerivative q s) (phaseSecond q s x) (Ioi x) x := by
  have hh := hasDerivWithinAt_periodicExtension_right Real.two_pi_pos
    (fun y hy => hasDerivWithinAt_mirrorDerivative_right
      (fun z hz => (analyticAt_phaseBranch q s hz).deriv.differentiableAt.hasDerivAt) hy) x
  have hm : x ∈ Ico 0 (0+2*Real.pi) := ⟨hx.1.le,by simpa only [zero_add] using hx.2⟩
  simpa only [phaseDerivative,periodicExtension,
    (toIcoMod_eq_self Real.two_pi_pos).mpr hm,phaseSecond] using
      hh.mono Ioi_subset_Ici_self

@[fun_prop] theorem measurable_phaseSecond (q : Tuning) (s : ℝ) :
    Measurable (phaseSecond q s) := by
  unfold phaseSecond
  exact Measurable.ite measurableSet_Iio (measurable_deriv _)
    ((measurable_deriv _).comp (measurable_const.sub measurable_id)).neg

theorem phaseSecond_intervalIntegrable (q : Tuning) (s : ℝ) :
    IntervalIntegrable (phaseSecond q s) volume 0 (2*Real.pi) := by
  obtain ⟨M1,M2,_hM1,_hM2,_hb1,hb2⟩ := phaseBranch_bounds q s
  have hb (x : ℝ) (hx : x∈Icc 0 (2*Real.pi)) : ‖phaseSecond q s x‖ ≤ M2 := by
    simp only [phaseSecond,Real.norm_eq_abs]
    split_ifs with hxp
    · exact hb2 x ⟨hx.1,hxp.le⟩
    · rw [abs_neg]
      exact hb2 _ ⟨by linarith [hx.2],by linarith [le_of_not_gt hxp]⟩
  have hi : IntegrableOn (phaseSecond q s) (Icc (0:ℝ) (2*Real.pi)) volume := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      (measurable_phaseSecond q s).aestronglyMeasurable M2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hb x hx
  apply IntegrableOn.intervalIntegrable
  simpa only [uIcc_of_le Real.two_pi_pos.le] using hi

end polyak.Global.Sampling
