import nesterov.Flow.Constants

/-!
Article: §2 target-rate level sets, the continuous part used by stages 5–7.
Use: exact closed level inequalities and the unique minimum step at a positive
requested exponent, with no asymptotic approximation.
-/
namespace nesterov.Flow
noncomputable section

theorem le_cQ_iff (θ m c : ℝ) :
    c≤cQ θ m ↔ c≤θ/2 ∧ 0≤delta θ m c := by
  unfold cQ delta
  split_ifs with h
  · constructor
    · intro hc
      exact ⟨hc,by nlinarith [sq_nonneg (c-θ/2)]⟩
    · exact And.left
  · have hs := Real.sqrt_nonneg (θ^2-4*m)
    have hsq := Real.sq_sqrt (show 0≤θ^2-4*m by linarith)
    constructor
    · intro hc
      refine ⟨by linarith,?_⟩
      have h₁ : 0≤θ-2*c-Real.sqrt (θ^2-4*m) := by linarith
      have h₂ : 0≤θ-2*c+Real.sqrt (θ^2-4*m) := by linarith
      nlinarith [mul_nonneg h₁ h₂]
    · rintro ⟨hc,hd⟩
      have hbound : Real.sqrt (θ^2-4*m)≤θ-2*c := by nlinarith
      linarith

theorem le_cF_iff {c : ℝ} (hc : 0≤c) (θ m : ℝ) :
    c≤cF θ m ↔ 3*c≤θ ∧ c*θ-c^2≤m := by
  rw [cF,le_min_iff,le_cQ_iff]
  unfold delta
  constructor
  · rintro ⟨ht,_,hd⟩
    constructor <;> nlinarith
  · rintro ⟨ht,hd⟩
    exact ⟨by linarith,by linarith,by nlinarith⟩

theorem minimum_step_of_level {θ m c : ℝ} (hc : 0<c) (h : c≤cF θ m) :
    2*c^2≤m ∧ (m=2*c^2 ↔ θ=3*c ∧ m=2*c^2) := by
  obtain ⟨hθ,hm⟩ := (le_cF_iff hc.le θ m).mp h
  have hstep : 2*c^2≤m := by nlinarith
  refine ⟨hstep,?_,fun he=>he.2⟩
  intro he
  exact ⟨by nlinarith,he⟩

theorem minimum_step_attained {c : ℝ} (hc : 0≤c) : c≤cF (3*c) (2*c^2) :=
  (le_cF_iff hc _ _).mpr ⟨le_rfl,by ring_nf;exact le_rfl⟩

end
end nesterov.Flow
