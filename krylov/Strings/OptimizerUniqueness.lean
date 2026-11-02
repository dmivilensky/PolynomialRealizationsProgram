import krylov.Strings.OptimizerInverseFeedback
import krylov.ContinuumBV.Optimality

/-!
Article: main_krylov, thm:value, uniqueness of the actual maximizing string.
Use: apply equality consequences to the actual mass-defined state, recover
its right closed-loop ODE, and use compact-range Picard uniqueness.
Source: the full BV identity, the proved inverse feedback bridge and mathlib's
closed-interval ODE uniqueness theorem. No terminal decay is assumed.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Local C1 regularity suffices for global uniqueness along two actual
positive paths: compactness supplies the uniform Lipschitz constant on
each finite union of path images. -/
theorem feedback_state_unique_halfline {σ : ℝ → ℝ} {α β : ℝ → FeedbackState}
    (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r) (hσpos : ∀ r ≥ 1, 0 < σ r)
    (hcα : ContinuousOn α (Ici 0)) (hcβ : ContinuousOn β (Ici 0))
    (hdα : ∀ x ≥ 0, HasDerivWithinAt α (feedbackField σ (α x)) (Ici 0) x)
    (hdβ : ∀ x ≥ 0, HasDerivWithinAt β (feedbackField σ (β x)) (Ici 0) x)
    (hpα : ∀ x ≥ 0, 0 < (α x).1 ∧ 0 < (α x).2.2 ∧
      1 ≤ stateRatio (α x).1 (α x).2.1 (α x).2.2)
    (hpβ : ∀ x ≥ 0, 0 < (β x).1 ∧ 0 < (β x).2.2 ∧
      1 ≤ stateRatio (β x).1 (β x).2.1 (β x).2.2)
    (h₀ : α 0 = β 0) : EqOn α β (Ici 0) := by
  intro x hx
  let C : Set FeedbackState := α '' Icc 0 x ∪ β '' Icc 0 x
  have hcαx := hcα.mono (show Icc 0 x ⊆ Ici 0 from fun _ ht ↦ ht.1)
  have hcβx := hcβ.mono (show Icc 0 x ⊆ Ici 0 from fun _ ht ↦ ht.1)
  have hC : IsCompact C := (isCompact_Icc.image_of_continuousOn hcαx).union
    (isCompact_Icc.image_of_continuousOn hcβx)
  have hdiff : ∀ z ∈ C, ContDiffAt ℝ 1 (feedbackField σ) z := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · obtain ⟨hφ, hK, hr⟩ := hpα t ht.1
      exact feedbackField_contDiffAt (hσ _ hr) hφ.ne' hK.ne' (hσpos _ hr).ne'
    · obtain ⟨hφ, hK, hr⟩ := hpβ t ht.1
      exact feedbackField_contDiffAt (hσ _ hr) hφ.ne' hK.ne' (hσpos _ hr).ne'
  have hlocal : LocallyLipschitzOn C (feedbackField σ) := by
    intro z hz
    obtain ⟨K, S, hS, hLip⟩ := (hdiff z hz).exists_lipschitzOnWith
    exact ⟨K, S, mem_nhdsWithin_of_mem_nhds hS, hLip⟩
  obtain ⟨K, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hC hlocal
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ feedbackField σ)
    (s := fun _ ↦ C) (fun _ _ ↦ hLip) hcαx
    (fun t ht ↦ (hdα t ht.1).mono (fun y hy ↦ ht.1.trans hy))
    (fun t ht ↦ Or.inl ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩) hcβx
    (fun t ht ↦ (hdβ t ht.1).mono (fun y hy ↦ ht.1.trans hy))
    (fun t ht ↦ Or.inr ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩) h₀
  exact heq ⟨hx, le_rfl⟩

/-- An actual maximizing mass satisfies the actual right closed-loop ODE.
This is a direct consequence of global reward equality, with no regularity
or absolute-continuity assumption added to the maximizing mass. -/
theorem optimal_actualState_hasDerivWithinAt (M : Mass) {φ σ : ℝ → ℝ} {γ : ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (he : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (hγ : 0 < γ) (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r ≥ 1, krylov.ContinuumControl.FeedbackGraphAt γ σ r)
    (hopt : M.reward γ φ = ENNReal.ofReal (krylov.ContinuumControl.feedbackValue γ σ 1))
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (actualFeedbackState M φ)
      (feedbackField σ (actualFeedbackState M φ x)) (Ici 0) x := by
  have ha := (krylov.ContinuumBV.actual_optimal_losses_zero M hc hm h₀ he hγ hσ hgraph hopt).2.2
  apply actualFeedbackState_hasDerivWithinAt M hc hm h₀ he ha
    (fun r hr ↦ (hσ r hr).continuousAt) (fun r hr ↦ (hgraph r hr).positive)
    (fun L ↦ krylov.ContinuumBV.actual_optimal_singularPart_zero M hc hm h₀ he hγ hσ hgraph hopt L)
    (fun L ↦ ?_) hx
  exact krylov.ContinuumBV.actual_optimal_feedback M hc hm h₀ he hγ hσ hgraph hopt L

/-- Every admissible actual state has positive position and energy and ratio at least one. -/
theorem actualFeedbackState_domain (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) {x : ℝ} (hx : 0 ≤ x) :
    0 < (actualFeedbackState M φ x).1 ∧ 0 < (actualFeedbackState M φ x).2.2 ∧
      1 ≤ stateRatio (actualFeedbackState M φ x).1 (actualFeedbackState M φ x).2.1
        (actualFeedbackState M φ x).2.2 := by
  have hφ := hm hx
  rw [h₀] at hφ
  exact ⟨zero_lt_one.trans_le hφ,
    zero_lt_one.trans_le (integralEnergy_one_le _ _ _),
    mass_state_ratio_ge_one M hx h₀ hc.continuousOn (hm.monotoneOn _)⟩

/-- Any two actual maximizing strings have the same physical state. -/
theorem optimal_actualState_unique (M N : Mass) {φ ψ σ : ℝ → ℝ} {γ : ℝ}
    (hcφ : Continuous φ) (hcψ : Continuous ψ) (hmφ : Monotone φ) (hmψ : Monotone ψ)
    (hφ₀ : φ 0 = 1) (hψ₀ : ψ 0 = 1)
    (heφ : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (heψ : ∀ x ≥ 0, ψ x = 1 + ∫ t in Ioc 0 x, integralSlope N.measure ψ t)
    (hγ : 0 < γ) (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r ≥ 1, krylov.ContinuumControl.FeedbackGraphAt γ σ r)
    (hoptM : M.reward γ φ = ENNReal.ofReal (krylov.ContinuumControl.feedbackValue γ σ 1))
    (hoptN : N.reward γ ψ = ENNReal.ofReal (krylov.ContinuumControl.feedbackValue γ σ 1)) :
    EqOn (actualFeedbackState M φ) (actualFeedbackState N ψ) (Ici 0) := by
  have haM := (krylov.ContinuumBV.actual_optimal_losses_zero M hcφ hmφ hφ₀ heφ hγ hσ hgraph hoptM).2.2
  have haN := (krylov.ContinuumBV.actual_optimal_losses_zero N hcψ hmψ hψ₀ heψ hγ hσ hgraph hoptN).2.2
  apply feedback_state_unique_halfline hσ (fun r hr ↦ (hgraph r hr).positive)
    (hcφ.prodMk ((M.slope_continuous_of_no_atoms hcφ haM).prodMk
      (M.energy_continuous_of_no_atoms hcφ haM))).continuousOn
    (hcψ.prodMk ((N.slope_continuous_of_no_atoms hcψ haN).prodMk
      (N.energy_continuous_of_no_atoms hcψ haN))).continuousOn
    (fun x hx ↦ optimal_actualState_hasDerivWithinAt M hcφ hmφ hφ₀ heφ hγ hσ hgraph hoptM hx)
    (fun x hx ↦ optimal_actualState_hasDerivWithinAt N hcψ hmψ hψ₀ heψ hγ hσ hgraph hoptN hx)
    (fun x hx ↦ actualFeedbackState_domain M hcφ hmφ hφ₀ hx)
    (fun x hx ↦ actualFeedbackState_domain N hcψ hmψ hψ₀ hx)
  simp [integralSlope, integralEnergy, hφ₀, hψ₀]

namespace Mass

/-- Local equality of post-origin measures determines the entire normalized
cumulative string, because both origin atoms are exactly one. -/
theorem eq_of_restrict_positive_eq (M N : Mass)
    (hμ : ∀ L : ℝ≥0, M.measure.restrict (Ioc 0 (L : ℝ)) =
      N.measure.restrict (Ioc 0 (L : ℝ))) : M = N := by
  have hc : M.cumulative = N.cumulative := by
    ext x
    by_cases hx : 0 ≤ x
    · have h := hμ (⟨x, hx⟩ : ℝ≥0)
      have heq := congrArg (fun μ : Measure ℝ ↦ μ univ) h
      simp only [Measure.restrict_apply_univ] at heq
      have hr := congrArg ENNReal.toReal heq
      change (M.measure (Ioc 0 x)).toReal = (N.measure (Ioc 0 x)).toReal at hr
      rw [M.real_mass_Ioc_zero hx, N.real_mass_Ioc_zero hx] at hr
      linarith
    · rw [M.negative x (not_le.mp hx), N.negative x (not_le.mp hx)]
  cases M
  cases N
  cases hc
  rfl

end Mass

/-- The maximizing string itself is unique, including its actual mass
measure; equality of the state alone is not the final conclusion. -/
theorem optimal_mass_unique (M N : Mass) {φ ψ σ : ℝ → ℝ} {γ : ℝ}
    (hcφ : Continuous φ) (hcψ : Continuous ψ) (hmφ : Monotone φ) (hmψ : Monotone ψ)
    (hφ₀ : φ 0 = 1) (hψ₀ : ψ 0 = 1)
    (heφ : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (heψ : ∀ x ≥ 0, ψ x = 1 + ∫ t in Ioc 0 x, integralSlope N.measure ψ t)
    (hγ : 0 < γ) (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r ≥ 1, krylov.ContinuumControl.FeedbackGraphAt γ σ r)
    (hoptM : M.reward γ φ = ENNReal.ofReal (krylov.ContinuumControl.feedbackValue γ σ 1))
    (hoptN : N.reward γ ψ = ENNReal.ofReal (krylov.ContinuumControl.feedbackValue γ σ 1)) : M = N := by
  have heq := optimal_actualState_unique M N hcφ hcψ hmφ hmψ hφ₀ hψ₀ heφ heψ hγ hσ hgraph hoptM hoptN
  apply M.eq_of_restrict_positive_eq N
  intro L
  have hSM := krylov.ContinuumBV.actual_optimal_singularPart_zero M hcφ hmφ hφ₀ heφ hγ hσ hgraph hoptM L
  have hSN := krylov.ContinuumBV.actual_optimal_singularPart_zero N hcψ hmψ hψ₀ heψ hγ hσ hgraph hoptN L
  have hvM : M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] actualFeedbackDensity M φ σ :=
    krylov.ContinuumBV.actual_optimal_feedback M hcφ hmφ hφ₀ heφ hγ hσ hgraph hoptM L
  have hvN : N.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] actualFeedbackDensity M φ σ := by
    filter_upwards [krylov.ContinuumBV.actual_optimal_feedback N hcψ hmψ hψ₀ heψ hγ hσ hgraph hoptN L,
      ae_restrict_mem measurableSet_Ioc] with x hx hxm
    have h := heq hxm.1.le
    change actualFeedbackState M φ x = actualFeedbackState N ψ x at h
    change N.typeDensity x = feedbackDensity (actualFeedbackState M φ x).1
      (actualFeedbackState M φ x).2.1 (Real.sqrt (σ (stateRatio (actualFeedbackState M φ x).1
        (actualFeedbackState M φ x).2.1 (actualFeedbackState M φ x).2.2)))
    rw [h]
    exact hx
  exact (M.restrict_eq_density_of_singular_zero L hSM hvM).trans
    (N.restrict_eq_density_of_singular_zero L hSN hvN).symm

end
end krylov.Strings
