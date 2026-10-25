import polyak.Energy.Slack

/-!
Article: Appendix A, startup interpolation involving time zero.
Use: bound every changed interpolation slack uniformly by one finite constant.
Proof: expand around the minimizer inequality, bound the four cross inner products,
and complete the square when the minimizer slack is strict.
-/

namespace polyak.Realization
noncomputable section
open Interpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: signed interpolation with the minimizer datum. -/
def originSlack (x σ : E) (v δ : ℝ) : ℝ :=
  (1/4 : ℝ)*(‖x‖^2-‖σ‖^2)+δ*(v-(1/2 : ℝ)*inner ℝ σ x)

/-- Article: the corrected time-zero pair. Use: its value is half the gradient-position inner product. -/
def initialPairSlack (a b x σ : E) (v δ : ℝ) : ℝ :=
  Energy.pairQuadratic δ a x b σ+δ*(v-(1/2 : ℝ)*inner ℝ b a)

/-- Article: corrected pair expansion. Use: only linear cross terms remain beyond the minimizer slack. -/
theorem initialPairSlack_eq (a b x σ : E) (v δ : ℝ) :
    initialPairSlack a b x σ v δ = originSlack x σ v δ+
      (1/4 : ℝ)*(‖a‖^2-‖b‖^2)-(1/2 : ℝ)*inner ℝ a x+
      (1/2 : ℝ)*inner ℝ b σ+
      δ/2*(inner ℝ σ a-inner ℝ b x) := by
  simp only [initialPairSlack,originSlack,Energy.pairQuadratic,norm_sub_sq_real,
    inner_add_left,inner_sub_right]
  rw [real_inner_comm x a,real_inner_comm σ b]
  ring

/-- Article: startup defect grows at most linearly in the position norm.
Use: independent of time, dimension and the size of the added coordinate. -/
theorem initialPairSlack_ge (a b x σ : E) (v δ : ℝ) (hδ : δ=1 ∨ δ= -1)
    (hσ : ‖σ‖ ≤ ‖x‖) :
    originSlack x σ v δ-(‖a‖+‖b‖)*‖x‖-‖b‖^2/4  ≤ 
      initialPairSlack a b x σ v δ := by
  rw [initialPairSlack_eq]
  have hax := abs_le.mp (abs_real_inner_le_norm a x)
  have hbs := abs_le.mp (abs_real_inner_le_norm b σ)
  have hsa := abs_le.mp (abs_real_inner_le_norm σ a)
  have hbx := abs_le.mp (abs_real_inner_le_norm b x)
  have h₁ := mul_le_mul_of_nonneg_left hσ (norm_nonneg b)
  have h₂ := mul_le_mul_of_nonneg_right hσ (norm_nonneg a)
  rcases hδ with rfl | rfl <;> nlinarith [sq_nonneg ‖a‖]

/-- Article: uniform finite startup defect.
Use: bounded waves need nonnegative star slack; growing waves use a strictly positive quadratic reserve. -/
theorem exists_initialPairSlack_lower_bound (a b : E) (x σ : ℕ → E) (v : ℕ → ℝ)
    (hσ : ∀ k, ‖σ k‖ ≤ ‖x k‖)
    (hstar : ∀ k δ, δ=1 ∨ δ= -1 → 0 ≤ originSlack (x k) (σ k) (v k) δ)
    (hcontrol : (∀ k, ‖x k‖ ≤ 1) ∨
      ∃ η : ℝ, 0<η ∧ ∀ k δ, δ=1 ∨ δ= -1 →
        η*‖x k‖^2 ≤ originSlack (x k) (σ k) (v k) δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k δ, δ=1 ∨ δ= -1 →
      -M ≤ initialPairSlack a b (x k) (σ k) (v k) δ := by
  let D := ‖a‖+‖b‖
  have hD : 0 ≤ D := add_nonneg (norm_nonneg a) (norm_nonneg b)
  rcases hcontrol with hbounded | ⟨η,hη,hηstar⟩
  · refine ⟨D+‖b‖^2/4,by positivity,fun k δ hδ => ?_⟩
    have hh := initialPairSlack_ge a b (x k) (σ k) (v k) δ hδ (hσ k)
    have hdx := mul_le_mul_of_nonneg_left (hbounded k) hD
    have hst := hstar k δ hδ
    dsimp [D] at *
    nlinarith
  · refine ⟨D^2/η+‖b‖^2/4,by positivity,fun k δ hδ => ?_⟩
    have hh := initialPairSlack_ge a b (x k) (σ k) (v k) δ hδ (hσ k)
    have hs := hηstar k δ hδ
    have hsq := sq_nonneg (η*‖x k‖-D)
    have he : D^2/η*η=D^2 := div_mul_cancel₀ _ (ne_of_gt hη)
    have hbound : -(D^2/η) ≤ η*‖x k‖^2-D*‖x k‖ := by
      rw [← neg_div]
      apply (div_le_iff₀ hη).mpr
      nlinarith [sq_nonneg D,sq_nonneg (η*‖x k‖)]
    dsimp [D] at *
    nlinarith

end
end polyak.Realization
