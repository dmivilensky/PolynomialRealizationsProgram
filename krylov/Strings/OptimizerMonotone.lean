import krylov.Strings.OptimizerPhysicalExtension

/-!
Article: main_krylov, thm:value, admissibility of the constructed optimizer.
Use: prove global monotonicity of its actual continuous physical position,
including the harmless extension before the physical origin.
Source: positivity of the two quadrature derivatives and genuine clock range.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set

/-- Monotonicity is preserved by the extended inverse physical clock. -/
theorem extendedPullback_monotone {s f : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hf : Monotone f) :
    Monotone (extendedPullback s f) := by
  have hright (x : ℝ) : physicalClock s (inverseClock s (max x (physicalCutoff s))) =
      max x (physicalCutoff s) := by
    obtain ⟨t, _, ht⟩ := clock_surjOn_above hs h₁ (-1) (le_max_right x (physicalCutoff s))
    rw [← ht]
    have hi : inverseClock s (physicalClock s t) = t :=
      Function.leftInverse_invFun (physicalClock_strictMono hs hp).injective t
    rw [hi]
  intro x y hxy
  apply hf
  apply (physicalClock_strictMono hs hp).le_iff_le.mp
  rw [hright, hright]
  exact max_le_max_right _ hxy

/-- The actual optimizer position is a globally monotone continuous
representative, as required by the general-mass Bellman bound. -/
theorem extendedPosition_monotone {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) : Monotone (extendedPosition s) := by
  apply extendedPullback_monotone hs hp h₁
  exact (strictMono_of_hasDerivAt_pos (expPrimitive_derivative hs)
    (fun t ↦ mul_pos (hp t) (expPrimitive_pos s t))).monotone

end
end krylov.Strings.OptimizerQuadratures
