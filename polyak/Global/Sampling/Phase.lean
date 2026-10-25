import polyak.Global.Sampling.Mirror

/-! A genuine periodic C1 phase for every shifted source curve, with a
bounded first derivative and a Lipschitz first derivative. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General polyak.Levels Set

def phase (q : Tuning) (s : ℝ) : ℝ→ℝ :=
  periodicExtension Real.two_pi_pos (mirror Real.pi (phaseBranch q s))

def phaseDerivative (q : Tuning) (s : ℝ) : ℝ→ℝ :=
  periodicExtension Real.two_pi_pos (mirrorDerivative Real.pi (deriv (phaseBranch q s)))

theorem phase_periodic (q : Tuning) (s : ℝ) : Function.Periodic (phase q s) (2*Real.pi) :=
  periodicExtension_periodic _ _

theorem mirror_phaseBranch_ends (q : Tuning) (s : ℝ) :
    mirror Real.pi (phaseBranch q s) 0=mirror Real.pi (phaseBranch q s) (2*Real.pi) := by
  simp only [mirror,ite_eq_left Real.pi_pos.le,phaseBranch_zero]
  rw [ite_eq_right (by linarith [Real.pi_pos] : ¬2*Real.pi≤Real.pi)]
  rw [sub_self,phaseBranch_zero]
  ring

theorem mirrorDerivative_ends (q : Tuning) (s : ℝ) :
    mirrorDerivative Real.pi (deriv (phaseBranch q s)) 0=
      mirrorDerivative Real.pi (deriv (phaseBranch q s)) (2*Real.pi) := by
  simp only [mirrorDerivative,ite_eq_left Real.pi_pos.le]
  rw [ite_eq_right (by linarith [Real.pi_pos] : ¬2*Real.pi≤Real.pi),sub_self]

theorem hasDerivAt_phase (q : Tuning) (s x : ℝ) : HasDerivAt (phase q s) (phaseDerivative q s x) x := by
  apply hasDerivAt_periodicExtension Real.two_pi_pos
    (fun z hz=>hasDerivAt_mirror Real.pi_pos
      (fun t ht=>(analyticAt_phaseBranch q s ht).differentiableAt.hasDerivAt)
      (phaseBranch_pi q s) hz) (mirror_phaseBranch_ends q s) (mirrorDerivative_ends q s)

@[fun_prop] theorem continuous_phase (q : Tuning) (s : ℝ) : Continuous (phase q s) :=
  continuous_iff_continuousAt.mpr (fun x=>(hasDerivAt_phase q s x).continuousAt)

theorem phase_actual (q : Tuning) (s : ℝ) {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    phase q s x=Geometry.shiftedAngle q s x := by
  have hm : x∈Ico 0 (0+2*Real.pi) := by constructor; exact hx.1; linarith [hx.2,Real.pi_pos]
  simp only [phase,periodicExtension,(toIcoMod_eq_self Real.two_pi_pos).mpr hm,
    mirror,ite_eq_left hx.2,phaseBranch_actual q s hx]

theorem phase_derivative_bounds (q : Tuning) (s : ℝ) :
    ∃M1 M2 : ℝ,0≤M1 ∧ 0≤M2 ∧
      (∀x,|phaseDerivative q s x|≤M1) ∧
      (∀x y,|phaseDerivative q s x-phaseDerivative q s y|≤M2*|x-y|) := by
  obtain ⟨M1,M2,hM1,hM2,hb1,hb2⟩:=phaseBranch_bounds q s
  have hmem (x:ℝ) : toIcoMod Real.two_pi_pos 0 x∈Ico 0 (2*Real.pi) := by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 x
  have hdf : ∀x∈Icc 0 Real.pi,HasDerivAt (deriv (phaseBranch q s))
      (deriv (deriv (phaseBranch q s)) x) x := by
    intro x hx
    exact (analyticAt_phaseBranch q s hx).deriv.differentiableAt.hasDerivAt
  refine ⟨M1,M2,hM1,hM2,?_,?_⟩
  · intro x
    dsimp [phaseDerivative,periodicExtension,mirrorDerivative]
    split_ifs with hx
    · exact hb1 _ ⟨(hmem x).1,hx⟩
    · apply hb1
      constructor <;> linarith [(hmem x).2,le_of_not_ge hx]
  · intro x y
    apply periodicExtension_lipschitz Real.two_pi_pos (mirrorDerivative_ends q s)
      (continuousOn_mirrorDerivative (fun z hz=>(hdf z hz).continuousAt))
      (fun z hz=>hasDerivWithinAt_mirrorDerivative_right hdf hz)
    intro z hz
    split_ifs with hza
    · exact hb2 z ⟨hz.1,hza.le⟩
    · rw [abs_neg]
      apply hb2
      constructor <;> linarith [hz.2,le_of_not_gt hza]

theorem phase_uniform_taylor (q : Tuning) (s : ℝ) :
    ∃M1 M2 : ℝ,0≤M1 ∧ 0≤M2 ∧
      (∀x,|phaseDerivative q s x|≤M1) ∧
      ∀v t,|phase q s (v+t)-phase q s v-phaseDerivative q s v*t|≤M2*t^2/2 := by
  obtain ⟨M1,M2,hM1,hM2,hb,hlip⟩:=phase_derivative_bounds q s
  exact ⟨M1,M2,hM1,hM2,hb,phase_taylor_bound (hasDerivAt_phase q s) hlip⟩

end polyak.Global.Sampling
