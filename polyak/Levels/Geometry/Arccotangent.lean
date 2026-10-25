import polyak.Levels.Geometry.ShiftedCurve
import polyak.Levels.Geometry.TuningCotangent

/-! The shifted polar angle agrees with the genuine arccotangent branch.
All differentiation therefore applies to the actual closed-interval curve. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set Filter
open scoped Topology

def arccotangent (u : ℝ) : ℝ := Real.pi/2-Real.arctan u

theorem arccotangent_mem (u : ℝ) : arccotangent u∈Ioo 0 Real.pi := by
  have hh:=Real.arctan_mem_Ioo u
  unfold arccotangent
  constructor <;> linarith [hh.1,hh.2,Real.pi_pos]

theorem cot_arccotangent (u : ℝ) :
    Real.cos (arccotangent u)/Real.sin (arccotangent u)=u := by
  unfold arccotangent
  rw [Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,←Real.tan_eq_sin_div_cos,Real.tan_arctan]

theorem angle_eq_of_cot_eq {a b : ℝ} (ha : a∈Ioo 0 Real.pi) (hb : b∈Ioo 0 Real.pi)
    (he : Real.cos a/Real.sin a=Real.cos b/Real.sin b) : a=b := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with h|h
  · have hh:=(cot_strictAnti hb ha).mpr h
    rw [he] at hh
    exact (lt_irrefl _ hh)
  · have hh:=(cot_strictAnti ha hb).mpr h
    rw [he] at hh
    exact (lt_irrefl _ hh)

theorem shiftedAngle_eq_arccotangent (q : Tuning) (s : ℝ) {ω : ℝ}
    (hω : ω∈Ioo 0 Real.pi) : shiftedAngle q s ω=arccotangent (cotangent q ω+s) := by
  apply angle_eq_of_cot_eq (shiftedAngle_mem q s hω) (arccotangent_mem _)
  rw [cot_shiftedAngle q s hω,cot_arccotangent]
  rfl

theorem shiftedAngle_le_half_pi_iff (q : Tuning) (s : ℝ) {ω : ℝ}
    (hω : ω∈Ioo 0 Real.pi) : shiftedAngle q s ω≤Real.pi/2 ↔ 0≤cotangent q ω+s := by
  rw [shiftedAngle_eq_arccotangent q s hω]
  unfold arccotangent
  have hm : 0≤Real.arctan (cotangent q ω+s) ↔ 0≤cotangent q ω+s := Real.arctan_nonneg
  exact ⟨fun h=>hm.mp (by linarith),fun h=>by have hh:=hm.mpr h; linarith⟩

def shiftedFirst (q : Tuning) (s ω : ℝ) : ℝ :=
  -cotangentFirst q ω/(1+(cotangent q ω+s)^2)

def shiftedSecond (q : Tuning) (s ω : ℝ) : ℝ :=
  -cotangentSecond q ω/(1+(cotangent q ω+s)^2)+
    2*(cotangent q ω+s)*(cotangentFirst q ω)^2/(1+(cotangent q ω+s)^2)^2

theorem hasDerivAt_arccotangent (u : ℝ) :
    HasDerivAt arccotangent (-(1/(1+u^2))) u :=
  (Real.hasDerivAt_arctan u).const_sub (Real.pi/2)

theorem hasDerivAt_shiftedAngle (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    HasDerivAt (shiftedAngle q s) (shiftedFirst q s ω) ω := by
  have he : shiftedAngle q s=ᶠ[𝓝 ω] (fun x=>arccotangent (cotangent q x+s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hω] with x hx
    exact shiftedAngle_eq_arccotangent q s hx
  have hh₀ := (hasDerivAt_arccotangent (cotangent q ω+s)).comp ω
    ((hasDerivAt_cotangent q hω).add_const s)
  have hh : HasDerivAt (fun x=>arccotangent (cotangent q x+s))
      (-(1/(1+(cotangent q ω+s)^2))*cotangentFirst q ω) ω := by
    simpa only [Function.comp_def] using hh₀
  have hh' := hh.congr_of_eventuallyEq he
  convert hh' using 1
  unfold shiftedFirst
  ring

theorem hasDerivAt_shiftedFirst (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    HasDerivAt (shiftedFirst q s) (shiftedSecond q s ω) ω := by
  have hu:=(hasDerivAt_cotangent q hω).add_const s
  have hv : HasDerivAt (fun x=> -cotangentFirst q x) (-cotangentSecond q ω) ω :=
    (hasDerivAt_cotangentFirst q hω).neg
  have hd : HasDerivAt (fun x=>1+(cotangent q x+s)^2)
      (2*(cotangent q ω+s)*cotangentFirst q ω) ω := by
    convert (hu.pow 2).const_add 1 using 1
    ring
  have hn : 1+(cotangent q ω+s)^2≠0 := by positivity
  unfold shiftedFirst shiftedSecond
  convert hv.div hd hn using 1
  field_simp
  ring

theorem deriv2_shiftedAngle (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    deriv^[2] (shiftedAngle q s) ω=shiftedSecond q s ω := by
  have he : deriv (shiftedAngle q s)=ᶠ[𝓝 ω] shiftedFirst q s := by
    filter_upwards [isOpen_Ioo.mem_nhds hω] with x hx
    exact (hasDerivAt_shiftedAngle q s hx).deriv
  change deriv (deriv (shiftedAngle q s)) ω=_
  rw [he.deriv_eq]
  exact (hasDerivAt_shiftedFirst q s hω).deriv

/-- Strict positive curvature everywhere at or below the phase pi/2. -/
theorem shiftedAngle_second_pos (q : Tuning) (s : ℝ) {ω : ℝ}
    (hω : ω∈Ioo 0 Real.pi) (hphase : shiftedAngle q s ω≤Real.pi/2) :
    0<deriv^[2] (shiftedAngle q s) ω := by
  rw [deriv2_shiftedAngle q s hω]
  have hu:=(shiftedAngle_le_half_pi_iff q s hω).mp hphase
  have hnegative:=cotangentSecond_neg q hω
  unfold shiftedSecond
  exact add_pos_of_pos_of_nonneg
    (div_pos (neg_pos.mpr hnegative) (by positivity)) (by positivity)

end polyak.Levels.Geometry
