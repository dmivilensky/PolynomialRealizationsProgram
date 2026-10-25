import polyak.Dynamics.Normalization
import polyak.Functions.Transforms

/-!
Article: Lemma normalization, actual original objectives and their real iterates.
Use: close the normalization dictionary without supplying an error trajectory or gradient formula.
-/

namespace polyak.Dynamics
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: eq:psi. Use: the source potential at a genuine minimizer of f. -/
def originalPotential (μ L : ℝ) (f : E → ℝ) (a : E) : E → ℝ :=
  normalizeFunction μ L (centerObjective f a)

/-- Article: lem:normalization. Use: the potential computed from f genuinely belongs to S. -/
theorem originalPotential_normalized {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (a : E) (hmin : ∀ y, f a ≤ f y) :
    NormalizedSmooth (originalPotential μ L f a) := by
  apply CenteredSmoothStronglyConvex.normalize
  refine ⟨hf.centerObjective a, ?_, ?_⟩
  · simp [centerObjective]
  · rw [(hasGradientAt_centerObjective hf.differentiable a 0).gradient]
    simpa using (hf.minimizer_iff a).mp hmin

/-- Article: lem:normalization. Use: derive the actual original gradient from its computed potential. -/
theorem original_gradient_dictionary {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (a e : E) :
    gradient f (a+e) = ((L+μ)/2) • e -
      ((L-μ)/2) • gradient (originalPotential μ L f a) e := by
  have hid := denormalize_normalize hf.mu_lt_L (centerObjective f a)
  have hdiff : Differentiable ℝ (originalPotential μ L f a) :=
    fun e => (hasGradientAt_normalize (hf.centerObjective a).differentiable e).differentiableAt
  have hg := (hasGradientAt_denormalize (μ := μ) (L := L) hdiff e).gradient
  change gradient (denormalizeFunction μ L
    (normalizeFunction μ L (centerObjective f a))) e = _ at hg
  rw [hid, (hasGradientAt_centerObjective hf.differentiable a e).gradient] at hg
  exact hg

/-- Article: lem:normalization. Use: the exact normalized recurrence holds on the actual run. -/
theorem original_normalized_run {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (a : E) (hmin : ∀ y, f a ≤ f y)
    (α β : ℝ) (x₀ : E) :
    NormalizedSmooth (originalPotential μ L f a) ∧ ∀ n : ℕ,
      ((state (gradient f) α β x₀ n).1-a, (state (gradient f) α β x₀ n).2-a) =
        normalizedState (gradient (originalPotential μ L f a))
          (normalizedA μ L α β) (normalizedB μ L α) β (x₀-a) n := by
  refine ⟨originalPotential_normalized hf a hmin, ?_⟩
  intro n
  simpa using normalized_error_state (gradient f) (gradient (originalPotential μ L f a))
    μ L α β a (x₀-a) (original_gradient_dictionary hf a) n

end
end polyak.Dynamics
