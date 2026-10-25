import polyak.Dynamics.Scale
import polyak.Dynamics.Original

/-!
Article: normalization of the initial error in the finite-horizon problem.
Use: realize each source ratio by an actual centered objective and a unit initial point.
-/

namespace polyak.Dynamics
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Article: eq:hb. Use: actual trajectories commute with amplitude scaling. -/
theorem iterate_amplitude (g h : E → E) (α β r : ℝ)
    (hgrad : ∀ y, g (r • y) = r • h y) (y₀ : E) (n : ℕ) :
    iterate g α β (r • y₀) n = r • iterate h α β y₀ n := by
  have hstate : ∀ n, state g α β (r • y₀) n =
      (r • (state h α β y₀ n).1, r • (state h α β y₀ n).2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [state, ih, step, hgrad]
      congr 1
      module
  exact congrArg Prod.fst (hstate n)

/-- Article: eq:WN. Use: a source ratio equals the actual error from unit initial norm.
Proof: center at the actual minimizer, rescale the genuine objective, then
conjugate its actual gradient executor by the inverse amplitude. -/
theorem exists_unit_instance {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {μ L : ℝ} {f : H → ℝ}
    (hf : SmoothStronglyConvex μ L f) (a x₀ : H) (hmin : ∀ y, f a ≤ f y)
    (hne : x₀ ≠ a) (α β : ℝ) :
    ∃ (F : H → ℝ) (y₀ : H), CenteredSmoothStronglyConvex μ L F ∧ ‖y₀‖ = 1 ∧
      ∀ n, ‖iterate (gradient f) α β x₀ n-a‖ / ‖x₀-a‖ =
        ‖iterate (gradient F) α β y₀ n‖ := by
  let r := ‖x₀-a‖
  have hr : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hne)
  let g := centerObjective f a
  let F := rescaleObjective r g
  let y₀ := (1/r) • (x₀-a)
  have hg : CenteredSmoothStronglyConvex μ L g := by
    refine ⟨hf.centerObjective a, ?_, ?_⟩
    · simp [g, centerObjective]
    · rw [(hasGradientAt_centerObjective hf.differentiable a 0).gradient]
      simpa using (hf.minimizer_iff a).mp hmin
  have hF : CenteredSmoothStronglyConvex μ L F := by
    refine ⟨hg.toSmoothStronglyConvex.rescaleObjective hr, ?_, ?_⟩
    · simp [F, rescaleObjective, hg.value_zero]
    · rw [(hasGradientAt_rescaleObjective hg.differentiable hr 0).gradient]
      simp [hg.gradient_zero]
  have hy : r • y₀ = x₀-a := by
    dsimp [y₀]
    rw [smul_smul]
    simp [ne_of_gt hr]
  have hgrad (y : H) : gradient g (r • y) = r • gradient F y := by
    rw [(hasGradientAt_rescaleObjective hg.differentiable hr y).gradient, smul_smul]
    simp [ne_of_gt hr]
  refine ⟨F, y₀, hF, ?_, ?_⟩
  · dsimp [y₀]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hr)]
    change 1/r*r=1
    field_simp
  · intro n
    have ht := iterate_translate (gradient f) (gradient g) a α β
      (fun e => (hasGradientAt_centerObjective hf.differentiable a e).gradient.symm)
      (x₀-a) n
    simp only [add_sub_cancel] at ht
    have ha := iterate_amplitude (gradient g) (gradient F) α β r hgrad y₀ n
    rw [hy] at ha
    rw [ht, add_sub_cancel_left, ha, norm_smul, Real.norm_of_nonneg hr.le]
    change r * ‖iterate (gradient F) α β y₀ n‖ / r = _
    field_simp

end
end polyak.Dynamics
