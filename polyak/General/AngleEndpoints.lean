import polyak.General.Angle

/-! Article: lem:angle. Literal endpoint limits of the continued angle. -/
namespace polyak.General
noncomputable section
open Filter
open scoped Topology
namespace Tuning

theorem angle_continuousAt (q : Tuning) {ω : ℝ} (hω : ω∈Set.Icc 0 Real.pi) :
    ContinuousAt q.angle ω := by
  have hn : ContinuousAt (fun w : ℝ => q.Xi (Real.cos w)) ω := by
    dsimp [Xi]
    fun_prop
  have hd : ContinuousAt q.angleRadius ω := by
    exact ((hn.pow 2).add (Real.continuous_sin.continuousAt.pow 2)).sqrt
  exact Real.continuous_arccos.continuousAt.comp (hn.div hd (ne_of_gt (q.angleRadius_pos hω)))

theorem angle_tendsto_zero (q : Tuning) : Tendsto q.angle (𝓝 0) (𝓝 Real.pi) := by
  have h := (q.angle_continuousAt (ω:=0) ⟨le_rfl,Real.pi_pos.le⟩).tendsto
  simpa only [q.angle_zero] using h

theorem angle_tendsto_pi (q : Tuning) : Tendsto q.angle (𝓝 Real.pi) (𝓝 Real.pi) := by
  have h := (q.angle_continuousAt (ω:=Real.pi) ⟨Real.pi_pos.le,le_rfl⟩).tendsto
  simpa only [q.angle_pi] using h

end Tuning
end
end polyak.General
