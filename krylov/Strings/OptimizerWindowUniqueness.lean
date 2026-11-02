import krylov.Strings.OptimizerUniqueness
import krylov.Strings.OptimizerLocalInverseFeedback

/-!
Article: main_krylov, thm:value, equality on a finite physical window.
Use: compare a locally optimal actual state with the globally constructed
feedback state without imposing feedback outside the finite window.
Source: compact-range ODE uniqueness and local actual RN decomposition.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Admissible feedback ODE trajectories with the same initial state agree on their common compact window. -/
theorem feedback_state_unique_window {σ : ℝ → ℝ} {α β : ℝ → FeedbackState} (L : ℝ≥0)
    (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r) (hσpos : ∀ r ≥ 1, 0 < σ r)
    (hcα : ContinuousOn α (Icc 0 (L : ℝ))) (hcβ : ContinuousOn β (Icc 0 (L : ℝ)))
    (hdα : ∀ x ∈ Ico 0 (L : ℝ), HasDerivWithinAt α (feedbackField σ (α x)) (Ici 0) x)
    (hdβ : ∀ x ∈ Ico 0 (L : ℝ), HasDerivWithinAt β (feedbackField σ (β x)) (Ici 0) x)
    (hpα : ∀ x ∈ Icc 0 (L : ℝ), 0 < (α x).1 ∧ 0 < (α x).2.2 ∧
      1 ≤ stateRatio (α x).1 (α x).2.1 (α x).2.2)
    (hpβ : ∀ x ∈ Icc 0 (L : ℝ), 0 < (β x).1 ∧ 0 < (β x).2.2 ∧
      1 ≤ stateRatio (β x).1 (β x).2.1 (β x).2.2)
    (h₀ : α 0 = β 0) : EqOn α β (Icc 0 (L : ℝ)) := by
  let C : Set FeedbackState := α '' Icc 0 (L : ℝ) ∪ β '' Icc 0 (L : ℝ)
  have hC : IsCompact C := (isCompact_Icc.image_of_continuousOn hcα).union
    (isCompact_Icc.image_of_continuousOn hcβ)
  have hdiff : ∀ z ∈ C, ContDiffAt ℝ 1 (feedbackField σ) z := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · obtain ⟨hφ, hK, hr⟩ := hpα t ht
      exact feedbackField_contDiffAt (hσ _ hr) hφ.ne' hK.ne' (hσpos _ hr).ne'
    · obtain ⟨hφ, hK, hr⟩ := hpβ t ht
      exact feedbackField_contDiffAt (hσ _ hr) hφ.ne' hK.ne' (hσpos _ hr).ne'
  have hlocal : LocallyLipschitzOn C (feedbackField σ) := by
    intro z hz
    obtain ⟨K, S, hS, hLip⟩ := (hdiff z hz).exists_lipschitzOnWith
    exact ⟨K, S, mem_nhdsWithin_of_mem_nhds hS, hLip⟩
  obtain ⟨K, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hC hlocal
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ feedbackField σ)
    (s := fun _ ↦ C) (fun _ _ ↦ hLip) hcα
    (fun t ht ↦ (hdα t ht).mono (fun y hy ↦ ht.1.trans hy))
    (fun t ht ↦ Or.inl ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩) hcβ
    (fun t ht ↦ (hdβ t ht).mono (fun y hy ↦ ht.1.trans hy))
    (fun t ht ↦ Or.inr ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩) h₀

/-- Equality of the actual state with the feedback candidate identifies
the actual mass measure on the same window. -/
theorem restrict_eq_constructedMass_of_feedback_state_eq (M : Mass) {φ σ s U : ℝ → ℝ}
    (L : ℝ≥0) (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    (hgraph : ∀ t ≥ 0, s t = σ (U t))
    (hSing : (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0)
    (hfb : M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] actualFeedbackDensity M φ σ)
    (heq : EqOn (actualFeedbackState M φ) (OptimizerQuadratures.constructedFeedbackState s U)
      (Icc 0 (L : ℝ))) :
    M.measure.restrict (Ioc 0 (L : ℝ)) =
      (OptimizerQuadratures.constructedMass s hs hp h₁).measure.restrict (Ioc 0 (L : ℝ)) := by
  have hv : M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] OptimizerQuadratures.extendedDensity s := by
    filter_upwards [hfb, ae_restrict_mem measurableSet_Ioc] with x hx hxm
    have h := heq ⟨hxm.1.le, hxm.2⟩
    have hcurve := OptimizerQuadratures.constructed_density_feedback hs hU hp h₁ hU₀ hode hgraph hxm.1.le
    rw [hcurve]
    change M.typeDensity x = feedbackDensity (OptimizerQuadratures.constructedFeedbackState s U x).1
      (OptimizerQuadratures.constructedFeedbackState s U x).2.1
      (Real.sqrt (σ (stateRatio (OptimizerQuadratures.constructedFeedbackState s U x).1
        (OptimizerQuadratures.constructedFeedbackState s U x).2.1
        (OptimizerQuadratures.constructedFeedbackState s U x).2.2)))
    rw [← h]
    exact hx
  exact (M.restrict_eq_density_of_singular_zero L hSing hv).trans
    (OptimizerDensity.globalMass_restrict_density (OptimizerQuadratures.extendedDensity s)
      (OptimizerQuadratures.extendedDensity_continuous hs hp h₁) L).symm

/-- Local singular-mass vanishing, feedback and state equality identify the restricted actual mass measures. -/
theorem restrict_eq_of_feedback_state_eq (M N : Mass) {φ ψ σ : ℝ → ℝ} (L : ℝ≥0)
    (hSM : (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0)
    (hSN : (N.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0)
    (hvM : M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] actualFeedbackDensity M φ σ)
    (hvN : N.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] actualFeedbackDensity N ψ σ)
    (heq : EqOn (actualFeedbackState M φ) (actualFeedbackState N ψ) (Icc 0 (L : ℝ))) :
    M.measure.restrict (Ioc 0 (L : ℝ)) = N.measure.restrict (Ioc 0 (L : ℝ)) := by
  have hvN' : N.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] actualFeedbackDensity M φ σ := by
    filter_upwards [hvN, ae_restrict_mem measurableSet_Ioc] with x hx hxm
    have h := heq ⟨hxm.1.le, hxm.2⟩
    change N.typeDensity x = feedbackDensity (actualFeedbackState M φ x).1
      (actualFeedbackState M φ x).2.1 (Real.sqrt (σ (stateRatio (actualFeedbackState M φ x).1
        (actualFeedbackState M φ x).2.1 (actualFeedbackState M φ x).2.2)))
    rw [h]
    exact hx
  exact (M.restrict_eq_density_of_singular_zero L hSM hvM).trans
    (N.restrict_eq_density_of_singular_zero L hSN hvN').symm

end
end krylov.Strings
