import polyak.Global.Sampling.Phase
import polyak.Global.Circle.Phase

/-! The periodic lifted-phase moments are exactly the folded source
program moments, including both endpoints and every signed lag. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General polyak.Levels MeasureTheory Set

theorem phase_on_fundamental (q : Tuning) (s : ℝ) {x : ℝ}
    (hx : x∈Ico 0 (2*Real.pi)) :
    phase q s x=mirror Real.pi (phaseBranch q s) x := by
  unfold phase periodicExtension
  rw [(toIcoMod_eq_self Real.two_pi_pos).mpr (by simpa only [zero_add] using hx)]

theorem circle_fold_complement {x : ℝ} (hx : x∈Icc Real.pi (2*Real.pi)) :
    (Circle.fold (Circle.ofReal x):ℝ)=2*Real.pi-x := by
  let u : Frequency := ⟨2*Real.pi-x,by constructor <;> linarith [hx.1,hx.2]⟩
  have he : Circle.ofReal x= -Circle.embed u := by
    change (x:Global.Circle)= -((2*Real.pi-x:ℝ):Global.Circle)
    rw [AddCircle.coe_sub,AddCircle.coe_period,zero_sub,neg_neg]
  rw [he,Circle.fold_reflect_embed]

theorem circle_minimizer_wave (q : Tuning) (s : ℝ) (x : Global.Circle) :
    Circle.minimizer (Geometry.shiftedCurve q s) x=
      (Circle.wave (phase q s) (phase_periodic q s) 0 x).re := by
  have he : (fun x:Global.Circle=>Circle.minimizer (Geometry.shiftedCurve q s) x)=
      fun x=>(Circle.wave (phase q s) (phase_periodic q s) 0 x).re := by
    apply AddCircle.Ico_ext (2*Real.pi) (0:ℝ)
    intro y hy
    have hy' : y∈Ico 0 (2*Real.pi) := by simpa only [zero_add] using hy
    change Circle.minimizer (Geometry.shiftedCurve q s) (Circle.ofReal y)=
      (Circle.wave (phase q s) (phase_periodic q s) 0 (Circle.ofReal y)).re
    rw [Circle.wave_ofReal,Kernels.cis_re]
    simp only [Int.cast_zero,zero_mul,zero_sub,Real.cos_neg]
    by_cases hyle : y≤Real.pi
    · let u : Frequency := ⟨y,hy'.1,hyle⟩
      have hf : Circle.fold (Circle.ofReal y)=u := Circle.fold_embed u
      change Real.cos (Geometry.shiftedAngle q s (Circle.fold (Circle.ofReal y)))=_
      rw [hf,phase_actual q s ⟨hy'.1,hyle⟩]
    · have hmem : 2*Real.pi-y∈Icc 0 Real.pi := by constructor <;> linarith [hy'.2]
      change Real.cos (Geometry.shiftedAngle q s (Circle.fold (Circle.ofReal y)))=_
      rw [circle_fold_complement ⟨(le_of_not_ge hyle),hy'.2.le⟩,
        phase_on_fundamental q s hy',mirror,ite_eq_right hyle,phaseBranch_actual q s hmem]
      exact (Real.cos_two_pi_sub _).symm
  exact congrFun he x

theorem circle_lag_wave (q : Tuning) (s : ℝ) (n : ℤ) (x : Global.Circle) :
    Circle.lag (Geometry.shiftedCurve q s) n x=
      (Circle.wave (phase q s) (phase_periodic q s) 0 x-
        Circle.wave (phase q s) (phase_periodic q s) n x).re := by
  have he : (fun x:Global.Circle=>Circle.lag (Geometry.shiftedCurve q s) n x)=
      fun x=>(Circle.wave (phase q s) (phase_periodic q s) 0 x-
        Circle.wave (phase q s) (phase_periodic q s) n x).re := by
    apply AddCircle.Ico_ext (2*Real.pi) (0:ℝ)
    intro y hy
    have hy' : y∈Ico 0 (2*Real.pi) := by simpa only [zero_add] using hy
    change Circle.lag (Geometry.shiftedCurve q s) n (Circle.ofReal y)=
      (Circle.wave (phase q s) (phase_periodic q s) 0 (Circle.ofReal y)-
        Circle.wave (phase q s) (phase_periodic q s) n (Circle.ofReal y)).re
    rw [Complex.sub_re,←circle_minimizer_wave,Circle.wave_ofReal,Kernels.cis_re]
    change Real.cos (Geometry.shiftedAngle q s (Circle.fold (Circle.ofReal y)))-
      Real.cos ((n:ℝ)*(Circle.fold (Circle.ofReal y):ℝ)-
        Geometry.shiftedAngle q s (Circle.fold (Circle.ofReal y)))=_
    congr 1
    by_cases hyle : y≤Real.pi
    · let u : Frequency := ⟨y,hy'.1,hyle⟩
      have hf : Circle.fold (Circle.ofReal y)=u := Circle.fold_embed u
      rw [hf,phase_actual q s ⟨hy'.1,hyle⟩]
    · have hmem : 2*Real.pi-y∈Icc 0 Real.pi := by constructor <;> linarith [hy'.2]
      rw [circle_fold_complement ⟨le_of_not_ge hyle,hy'.2.le⟩,
        phase_on_fundamental q s hy',mirror,ite_eq_right hyle,phaseBranch_actual q s hmem]
      have hc := Real.cos_add_int_mul_two_pi
        (-((n:ℝ)*(2*Real.pi-y)-Geometry.shiftedAngle q s (2*Real.pi-y))) n
      have hr : -((n:ℝ)*(2*Real.pi-y)-Geometry.shiftedAngle q s (2*Real.pi-y))+
          (n:ℝ)*(2*Real.pi)=
          (n:ℝ)*y-(2*Real.pi-Geometry.shiftedAngle q s (2*Real.pi-y))+2*Real.pi := by ring
      rw [hr,Real.cos_add_two_pi,Real.cos_neg] at hc
      exact hc.symm
  exact congrFun he x

theorem phaseConstraint_actual (q : Tuning) (s : ℝ) (μ : Measure Global.Circle)
    [IsFiniteMeasure μ] (n : ℤ) :
    Circle.phaseConstraint (phase q s) (phase_periodic q s) μ n=
      ∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ := by
  simp_rw [circle_lag_wave q s n]
  rw [Circle.phaseConstraint,Circle.phaseMoment,Circle.phaseMoment,
    ←integral_sub (Circle.wave_integrable _ (continuous_phase q s) _ _)
      (Circle.wave_integrable _ (continuous_phase q s) _ _)]
  exact (Complex.reCLM.integral_comp_comm
    ((Circle.wave_integrable _ (continuous_phase q s) _ _).sub
      (Circle.wave_integrable _ (continuous_phase q s) _ _))).symm

theorem phaseMinimizer_actual (q : Tuning) (s : ℝ) (μ : Measure Global.Circle)
    [IsFiniteMeasure μ] :
    Circle.phaseMinimizer (phase q s) (phase_periodic q s) μ=
      ∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ := by
  simp_rw [circle_minimizer_wave q s]
  rw [Circle.phaseMinimizer,Circle.phaseMoment]
  exact (Complex.reCLM.integral_comp_comm
    (Circle.wave_integrable _ (continuous_phase q s) _ _)).symm

end polyak.Global.Sampling
