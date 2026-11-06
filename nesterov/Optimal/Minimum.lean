import nesterov.Optimal.Model

/-! The actual attained minimum in the optimal-tuning criterion. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Set Filter
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem cornerRatioAt_continuousOn (a : A) :
    ContinuousOn (F.cornerRatioAt a) (Icc 0 2) := by
  apply ContinuousOn.div (by unfold cornerNAt;fun_prop) (by fun_prop)
  intro ξ hξ
  have : 0<4*(3-ξ) := by linarith [hξ.2]
  exact this.ne'

theorem cornerLagAt_attained (a : A) :
    ∃ ξ∈Icc (0:ℝ) 2,F.cornerRatioAt a ξ=F.cornerLagAt a := by
  obtain ⟨ξ,hξ,hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤2)) (F.cornerRatioAt_continuousOn a)
  refine ⟨ξ,hξ,?_⟩
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_,ξ,hξ,rfl⟩
    · rintro v ⟨x,hx,rfl⟩
      exact hmin hx
  · exact csInf_le (isCompact_Icc.image_of_continuousOn
      (F.cornerRatioAt_continuousOn a)).bddBelow ⟨ξ,hξ,rfl⟩

theorem cornerLagAt_le (a : A) {ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2) :
    F.cornerLagAt a≤F.cornerRatioAt a ξ :=
  csInf_le (isCompact_Icc.image_of_continuousOn
    (F.cornerRatioAt_continuousOn a)).bddBelow ⟨ξ,hξ,rfl⟩

theorem le_cornerLagAt (a : A) {c : ℝ}
    (h : ∀ ξ∈Icc (0:ℝ) 2,c≤F.cornerRatioAt a ξ) : c≤F.cornerLagAt a := by
  apply le_csInf
  · exact ⟨_,0,by norm_num,rfl⟩
  · rintro v ⟨ξ,hξ,rfl⟩
    exact h ξ hξ

theorem cornerRatioAt_zero (a : A) : F.cornerRatioAt a 0=F.thetaAt a/3 := by
  simp [cornerRatioAt,cornerNAt]
  ring

theorem cornerRatioAt_two (a : A) :
    F.cornerRatioAt a 2=F.stabilityMargin a-2*F.thetaAt a := by
  unfold cornerRatioAt cornerNAt
  norm_num
  ring

theorem cornerLagAt_le_theta (a : A) : F.cornerLagAt a≤F.thetaAt a/3 := by
  simpa only [F.cornerRatioAt_zero] using F.cornerLagAt_le a (by norm_num : (0:ℝ)∈Icc 0 2)

theorem cornerLagAt_le_margin (a : A) :
    F.cornerLagAt a≤F.stabilityMargin a-2*F.thetaAt a := by
  simpa only [F.cornerRatioAt_two] using F.cornerLagAt_le a (by norm_num : (2:ℝ)∈Icc 0 2)

end
end nesterov.TwoStep.Scaling
