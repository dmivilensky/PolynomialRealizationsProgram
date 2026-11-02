import krylov.ContinuumBV.FiniteOptimality

/-!
Article: main_krylov, thm:value, arbitrary finite-endpoint equality cases.
Use: remove singular mass and recover feedback on every compact window from
equality of the full finite-endpoint reward. Endpoint divergence is permitted.
Source: the full BV identity, actual RN locality and positive-loss localization.
-/

namespace krylov.Strings.OptimizerFinite
noncomputable section
open Set Filter MeasureTheory
open krylov.ContinuumBV krylov.ContinuumControl
open scoped Topology NNReal ENNReal

variable {ℓ : ℝ} (hℓ : 0 < ℓ) (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
  (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) {φ : ℝ → ℝ}
  (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ)) (hz : φ 0 = 1)
  (he : ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
    ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t)
  {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ) (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r)
  (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
  (hopt : reward hℓ f h₀ γ φ = ENNReal.ofReal (feedbackValue γ σ 1))

include hc hm hz he hγ hσ hgraph hopt

/-- Every compact continuous singular loss vanishes for a finite-endpoint
optimizer, also when its mass has no global finite extension. -/
theorem optimal_continuous_singular_zero (w : Windows ℓ) {ψ : ℝ → ℝ}
    (hcψ : Continuous ψ) (hmψ : Monotone ψ) (hψ₀ : ψ 0 = 1)
    (hφψ : EqOn φ ψ (Icc 0 (w.val : ℝ))) :
    (∫ x in Ioc 0 (w.val : ℝ), massCost (windowMass hℓ f h₀ w) γ σ ψ x
      ∂continuousSingularMass (windowMass hℓ f h₀ w)) = 0 := by
  have hδ : 0 ≤ 1 / 2 * (∫ x in Ioc 0 (w.val : ℝ),
      massCost (windowMass hℓ f h₀ w) γ σ ψ x
        ∂continuousSingularMass (windowMass hℓ f h₀ w)) :=
    mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioc (fun x hx ↦
      (massCost_pos _ hcψ hmψ hψ₀ w.val γ (fun r hr ↦ (hgraph r hr).positive)
        (Ioc_subset_Icc_self hx)).le))
  have hC := feedbackValue_pos hγ le_rfl (hgraph 1 le_rfl).positive
  have hzero := penalty_eq_zero_of_optimal_reward hℓ f h₀ γ φ hC hδ hopt w (by
    intro v hwv
    obtain ⟨χ, hcχ, hmχ, hχ₀, hφχ, heχ⟩ :=
      exists_compact_state_extension hℓ f h₀ hc hm hz v (he v)
    have hμ : (windowMass hℓ f h₀ w).measure.restrict (Ioc 0 (w.val : ℝ)) =
        (windowMass hℓ f h₀ v).measure.restrict (Ioc 0 (w.val : ℝ)) := by
      simpa only [min_eq_left hwv] using windowMass_compatible hℓ f h₀ w v
    have hagree : EqOn ψ χ (Icc 0 (w.val : ℝ)) := fun t ht ↦
      (hφψ ht).symm.trans (hφχ ⟨ht.1, ht.2.trans (show (w.val : ℝ) ≤ v.val from hwv)⟩)
    have hloc : (∫ x in Ioc 0 (w.val : ℝ), massCost (windowMass hℓ f h₀ w) γ σ ψ x
        ∂continuousSingularMass (windowMass hℓ f h₀ w)) =
        ∫ x in Ioc 0 (w.val : ℝ), massCost (windowMass hℓ f h₀ v) γ σ χ x
          ∂continuousSingularMass (windowMass hℓ f h₀ v) := by
      rw [continuousSingularMass_eq_of_restrict_eq _ _ hμ]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact massCost_eq_of_restrict_eq _ _ hμ hagree (Ioc_subset_Icc_self hx) γ σ
    have hi := (actual_cadlag_cost_identity _ hcχ hmχ hχ₀ v.val heχ hγ.ne' hσ hgraph).2.2.1
    have hmono : (∫ x in Ioc 0 (w.val : ℝ), massCost (windowMass hℓ f h₀ w) γ σ ψ x
        ∂continuousSingularMass (windowMass hℓ f h₀ w)) ≤
        ∫ x in Ioc 0 (v.val : ℝ), massCost (windowMass hℓ f h₀ v) γ σ χ x
          ∂continuousSingularMass (windowMass hℓ f h₀ v) := by
      rw [hloc]
      apply setIntegral_mono_set hi
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact (massCost_pos _ hcχ hmχ hχ₀ v.val γ (fun r hr ↦ (hgraph r hr).positive)
          (Ioc_subset_Icc_self hx)).le
      · exact Eventually.of_forall (fun _ hx ↦ Ioc_subset_Ioc le_rfl
          (show (w.val : ℝ) ≤ v.val from hwv) hx)
    have hb := (actual_prefix_loss_bounds _ hcχ hmχ hχ₀ v.val heχ hγ hσ hgraph).2.1
    rw [Mass.rewardPrefix_eq_of_eqOn _ γ hφχ,
      actual_rewardPrefix_eq_ofReal_integral _ hγ.le hcχ]
    exact ENNReal.ofReal_le_ofReal (by linarith))
  linarith

/-- An arbitrary finite-endpoint maximizing string has no singular mass
on any compact positive window, and has the actual feedback RN density there. -/
theorem optimal_window_conditions (w : Windows ℓ) {ψ : ℝ → ℝ}
    (hcψ : Continuous ψ) (hmψ : Monotone ψ) (hψ₀ : ψ 0 = 1)
    (hφψ : EqOn φ ψ (Icc 0 (w.val : ℝ))) :
    (∀ x ∈ Ioc 0 (w.val : ℝ), (windowMass hℓ f h₀ w).measure {x} = 0) ∧
      (windowMass hℓ f h₀ w).measure.singularPart volume (Ioc 0 (w.val : ℝ)) = 0 ∧
      ∀ᵐ x ∂volume.restrict (Ioc 0 (w.val : ℝ)), (windowMass hℓ f h₀ w).typeDensity x =
        integralSlope (windowMass hℓ f h₀ w).measure ψ x / (ψ x * Real.sqrt
          (σ (ψ x * integralSlope (windowMass hℓ f h₀ w).measure ψ x /
            integralEnergy (windowMass hℓ f h₀ w).measure ψ x))) := by
  let M := windowMass hℓ f h₀ w
  have heψ := Mass.position_equation_congr M w.val (he w) hφψ
  have hno := fun x hx ↦ optimal_no_atoms hℓ f h₀ hc hm hz he hγ hσ hgraph hopt w (x := x) hx
  have hsq := optimal_square_zero hℓ f h₀ hc hm hz he hγ hσ hgraph hopt w hφψ
  have hsc := optimal_continuous_singular_zero hℓ f h₀ hc hm hz he hγ hσ hgraph hopt w hcψ hmψ hψ₀ hφψ
  have hi := (actual_cadlag_cost_identity M hcψ hmψ hψ₀ w.val heψ hγ.ne' hσ hgraph).2.2.1
  have hnonneg : 0 ≤ᵐ[(continuousSingularMass M).restrict (Ioc 0 (w.val : ℝ))]
      massCost M γ σ ψ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (massCost_pos M hcψ hmψ hψ₀ w.val γ (fun r hr ↦ (hgraph r hr).positive)
      (Ioc_subset_Icc_self hx)).le
  have hzae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).1 hsc
  have hfalse : ∀ᵐ x ∂(continuousSingularMass M).restrict (Ioc 0 (w.val : ℝ)), False := by
    filter_upwards [hzae, ae_restrict_mem measurableSet_Ioc] with x hx hxL
    exact (massCost_pos M hcψ hmψ hψ₀ w.val γ (fun r hr ↦ (hgraph r hr).positive)
      (Ioc_subset_Icc_self hxL)).ne' hx
  have hμ : (continuousSingularMass M).restrict (Ioc 0 (w.val : ℝ)) = 0 :=
    ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hfalse)
  have hat : Ioc (0 : ℝ) w.val ∩ massAtomSet M = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact hx.2.ne' (hno x hx.1)
  refine ⟨hno, ?_, ?_⟩
  · rw [singularPart_eq_continuous_add_atoms, Measure.add_apply,
      Measure.restrict_apply measurableSet_Ioc, hat, measure_empty,
      Measure.restrict_eq_zero.1 hμ, add_zero]
  · have hIsq := (actual_fundamental_identity M hcψ hmψ hψ₀ w.val heψ hγ hσ hgraph).1
    have hqa := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (fun x ↦ actualSquareCost_nonneg M γ σ ψ x)) hIsq).1 hsq
    filter_upwards [hqa, ae_restrict_mem measurableSet_Ioc] with x hx hxL
    have hp := compactStateDomain_positive_ratio M ψ w.val (clippedState_mem M hcψ hmψ hψ₀ w.val x)
    simp only [clippedState, clipTime_of_mem w.val (Ioc_subset_Icc_self hxL)] at hp
    have hpow : integralEnergy M.measure ψ x ^ (-γ) ≠ 0 := (Real.rpow_pos_of_pos hp.2.2.1 _).ne'
    have hsquare := (mul_eq_zero.1 hx).resolve_left hpow
    exact (square_zero_iff_feedback hp.1 hp.2.1
      (Real.sqrt_pos.2 (hgraph _ hp.2.2.2).positive) (M.typeDensity x)).1 hsquare

end
end krylov.Strings.OptimizerFinite
