import polyak.Levels.Geometry.JointAnalytic
import Mathlib.Analysis.Calculus.MeanValue

/-! The actual shifted phase has one analytic real branch near [0,pi]. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General polyak.Levels Set

def phaseBranch (q : Tuning) (s x : ℝ) : ℝ :=
  Geometry.jointAngle ![q.kappa,q.y,q.beta,s,x]

theorem phaseBranch_actual (q : Tuning) (s : ℝ) {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    phaseBranch q s x=Geometry.shiftedAngle q s x := Geometry.jointAngle_actual q s hx

theorem analyticAt_phaseBranch (q : Tuning) (s : ℝ) {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    AnalyticAt ℝ (phaseBranch q s) x := by
  have hm : AnalyticAt ℝ (fun x:ℝ=>![q.kappa,q.y,q.beta,s,x]) x := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_id
  exact (Geometry.analyticAt_jointAngle_actual q s hx).comp (f:=fun x:ℝ=>![q.kappa,q.y,q.beta,s,x]) hm

@[simp] theorem phaseBranch_zero (q : Tuning) (s : ℝ) : phaseBranch q s 0=Real.pi := by
  rw [phaseBranch_actual q s ⟨le_rfl,Real.pi_pos.le⟩]
  simp

@[simp] theorem phaseBranch_pi (q : Tuning) (s : ℝ) : phaseBranch q s Real.pi=Real.pi := by
  rw [phaseBranch_actual q s ⟨Real.pi_pos.le,le_rfl⟩]
  simp

theorem phaseBranch_bounds (q : Tuning) (s : ℝ) :
    ∃M1 M2 : ℝ,0≤M1 ∧ 0≤M2 ∧
      (∀x∈Icc 0 Real.pi,|deriv (phaseBranch q s) x|≤M1) ∧
      (∀x∈Icc 0 Real.pi,|deriv (deriv (phaseBranch q s)) x|≤M2) := by
  have hd : ContinuousOn (fun x=>|deriv (phaseBranch q s) x|) (Icc 0 Real.pi) := by
    intro x hx
    exact (analyticAt_phaseBranch q s hx).deriv.continuousAt.abs.continuousWithinAt
  have hdd : ContinuousOn (fun x=>|deriv (deriv (phaseBranch q s)) x|) (Icc 0 Real.pi) := by
    intro x hx
    exact (analyticAt_phaseBranch q s hx).deriv.deriv.continuousAt.abs.continuousWithinAt
  obtain ⟨M1,hM1⟩:=isCompact_Icc.bddAbove_image hd
  obtain ⟨M2,hM2⟩:=isCompact_Icc.bddAbove_image hdd
  refine ⟨max M1 0,max M2 0,le_max_right _ _,le_max_right _ _,?_,?_⟩
  · intro x hx
    exact (hM1 ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  · intro x hx
    exact (hM2 ⟨x,hx,rfl⟩).trans (le_max_left _ _)

end polyak.Global.Sampling
