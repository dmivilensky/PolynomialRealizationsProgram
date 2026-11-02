import krylov.ContinuumBV.RewardBound

/-!
Article: main_krylov, thm:value, necessity of the feedback law.
Use: an optimizer cannot hide a positive loss at finite physical time. Every
such loss lowers the universal bound for the entire remaining reward. Thus
arbitrary maximizing strings have no singular continuous mass or positive
position atoms and satisfy the actual feedback density almost everywhere.
Source: the full BV fundamental identity, monotonicity of nonnegative losses
and increasing finite-prefix rewards. No terminal-decay premise is needed.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology NNReal

/-- An eventual real prefix bound controls the full extended reward. Earlier
prefixes are handled by monotonicity; no global real integrability is assumed. -/
theorem actual_reward_le_of_eventual_prefix_le (M : Mass) {γ : ℝ} (hγ : 0 ≤ γ)
    {φ : ℝ → ℝ} (hc : Continuous φ) (L C : ℝ)
    (hprefix : ∀ X ≥ L, (∫ x in Ioc 0 X, M.rewardDensity γ φ x) ≤ C) :
    M.reward γ φ ≤ ENNReal.ofReal C := by
  apply M.reward_le_of_prefix_le γ φ
  intro X _
  exact (M.rewardPrefix_mono γ φ (le_max_left X L)).trans (by
    rw [actual_rewardPrefix_eq_ofReal_integral M hγ hc]
    exact ENNReal.ofReal_le_ofReal (hprefix (max X L) (le_max_right _ _)))

/-- At the optimal reward, any fixed nonnegative penalty deducted from all
sufficiently late prefix bounds must vanish. -/
theorem penalty_eq_zero_of_optimal_reward (M : Mass) {γ : ℝ} (hγ : 0 ≤ γ)
    {φ : ℝ → ℝ} (hc : Continuous φ) {C δ L : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ)
    (hopt : M.reward γ φ = ENNReal.ofReal C)
    (hprefix : ∀ X ≥ L, (∫ x in Ioc 0 X, M.rewardDensity γ φ x) + δ ≤ C) : δ = 0 := by
  have hu := actual_reward_le_of_eventual_prefix_le M hγ hc L (C - δ)
    (fun X hX => by linarith [hprefix X hX])
  rw [hopt] at hu
  by_contra hne
  have hpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hne)
  have hstrict : ENNReal.ofReal (C - δ) < ENNReal.ofReal C := by
    exact (ENNReal.ofReal_lt_ofReal_iff hC).2 (by linarith)
  exact (not_lt_of_ge hu) hstrict

/-- Each individual kind of loss lowers the finite-prefix reward bound.
In the atomic case this includes every atom separately, however small. -/
theorem actual_prefix_loss_bounds (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    ((∫ x in Ioc 0 (L : ℝ), M.rewardDensity γ φ x) +
      1 / 2 * (∫ x in Ioc 0 (L : ℝ), actualSquareCost M γ σ φ x) ≤ feedbackValue γ σ 1) ∧
    ((∫ x in Ioc 0 (L : ℝ), M.rewardDensity γ φ x) +
      1 / 2 * (∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂continuousSingularMass M) ≤ feedbackValue γ σ 1) ∧
    (∀ x : actualAtoms M L, (∫ t in Ioc 0 (L : ℝ), M.rewardDensity γ φ t) +
      actualAtomLoss M γ σ φ x ≤ feedbackValue γ σ 1) := by
  have hid := (actual_fundamental_identity M hc hm h₀ L he hγ hσ hgraph).2
  rw [statePotential_clipped_zero M h₀ L γ σ] at hid
  have hsq : 0 ≤ ∫ x in Ioc 0 (L : ℝ), actualSquareCost M γ σ φ x :=
    setIntegral_nonneg measurableSet_Ioc (fun x _ => actualSquareCost_nonneg M γ σ φ x)
  have hsc : 0 ≤ ∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂continuousSingularMass M :=
    setIntegral_nonneg measurableSet_Ioc (fun x hx => (massCost_pos M hc hm h₀ L γ
      (fun r hr => (hgraph r hr).positive) (Ioc_subset_Icc_self hx)).le)
  have hat : 0 ≤ ∑' x : actualAtoms M L, actualAtomLoss M γ σ φ x :=
    tsum_nonneg (fun x => (actualAtomLoss_pos M hc hm h₀ L hgraph x).le)
  have hdom := clippedState_mem M hc hm h₀ L (L : ℝ)
  have hp := compactStateDomain_positive_ratio M φ L hdom
  have hterminal : 0 < statePotential γ σ (clippedState M φ L L) :=
    stateValue_pos hγ hp.2.2.1 hdom.2 (hgraph _ hp.2.2.2).positive
  refine ⟨by linarith, by linarith, ?_⟩
  intro x
  have hle := (summable_all_actual_atomLoss M hc hm h₀ L hγ.ne' hσ hgraph).le_tsum x
    (fun y _ => (actualAtomLoss_pos M hc hm h₀ L hgraph y).le)
  linarith

/-- For an actual optimizer all finite square and continuous singular loss
integrals vanish, and there are no positive-position atoms. The conclusion
uses the full extended reward and does not assume terminal potential decay. -/
theorem actual_optimal_losses_zero (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (he : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    (hopt : M.reward γ φ = ENNReal.ofReal (feedbackValue γ σ 1)) :
    (∀ L : ℝ≥0, (∫ x in Ioc 0 (L : ℝ), actualSquareCost M γ σ φ x) = 0) ∧
    (∀ L : ℝ≥0, (∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂continuousSingularMass M) = 0) ∧
    (∀ x > 0, M.measure {x} = 0) := by
  have hC : 0 < feedbackValue γ σ 1 := feedbackValue_pos hγ le_rfl (hgraph 1 le_rfl).positive
  refine ⟨?_, ?_, ?_⟩
  · intro L
    have hδ : 0 ≤ 1 / 2 * (∫ x in Ioc 0 (L : ℝ), actualSquareCost M γ σ φ x) :=
      mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioc
        (fun x _ => actualSquareCost_nonneg M γ σ φ x))
    have hz := penalty_eq_zero_of_optimal_reward M hγ.le hc hC hδ hopt (L := L) (by
      intro X hX
      let Y : ℝ≥0 := ⟨X, L.property.trans hX⟩
      have hb := (actual_prefix_loss_bounds M hc hm h₀ Y (fun x hx => he x hx.1) hγ hσ hgraph).1
      have hi := (actual_fundamental_identity M hc hm h₀ Y (fun x hx => he x hx.1) hγ hσ hgraph).1
      have hmono : (∫ x in Ioc 0 (L : ℝ), actualSquareCost M γ σ φ x) ≤
          ∫ x in Ioc 0 X, actualSquareCost M γ σ φ x :=
        setIntegral_mono_set hi (Eventually.of_forall (fun x => actualSquareCost_nonneg M γ σ φ x))
          (Eventually.of_forall (fun _ hx => Ioc_subset_Ioc le_rfl hX hx))
      change (∫ x in Ioc 0 X, M.rewardDensity γ φ x) +
        1 / 2 * (∫ x in Ioc 0 X, actualSquareCost M γ σ φ x) ≤ feedbackValue γ σ 1 at hb
      linarith)
    linarith
  · intro L
    have hδ : 0 ≤ 1 / 2 * (∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂continuousSingularMass M) :=
      mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioc (fun x hx =>
        (massCost_pos M hc hm h₀ L γ (fun r hr => (hgraph r hr).positive) (Ioc_subset_Icc_self hx)).le))
    have hz := penalty_eq_zero_of_optimal_reward M hγ.le hc hC hδ hopt (L := L) (by
      intro X hX
      let Y : ℝ≥0 := ⟨X, L.property.trans hX⟩
      have hb := (actual_prefix_loss_bounds M hc hm h₀ Y (fun x hx => he x hx.1) hγ hσ hgraph).2.1
      have hi := (actual_cadlag_cost_identity M hc hm h₀ Y (fun x hx => he x hx.1) hγ.ne' hσ hgraph).2.2.1
      have hmono : (∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂continuousSingularMass M) ≤
          ∫ x in Ioc 0 X, massCost M γ σ φ x ∂continuousSingularMass M :=
        setIntegral_mono_set hi (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact (massCost_pos M hc hm h₀ Y γ (fun r hr => (hgraph r hr).positive)
            (Ioc_subset_Icc_self hx)).le)
          (Eventually.of_forall (fun _ hx => Ioc_subset_Ioc le_rfl hX hx))
      change (∫ x in Ioc 0 X, M.rewardDensity γ φ x) +
        1 / 2 * (∫ x in Ioc 0 X, massCost M γ σ φ x ∂continuousSingularMass M) ≤ feedbackValue γ σ 1 at hb
      linarith)
    linarith
  · intro x hx
    by_contra hmass
    have hpos : 0 < M.measure {x} := bot_lt_iff_ne_bot.2 hmass
    let L : ℝ≥0 := ⟨x, hx.le⟩
    let atom : actualAtoms M L := ⟨x, ⟨⟨hx, le_rfl⟩, hpos⟩⟩
    have hJ := actualAtomLoss_pos M hc hm h₀ L hgraph atom
    have hz := penalty_eq_zero_of_optimal_reward M hγ.le hc hC hJ.le hopt (L := x) (by
      intro X hX
      let Y : ℝ≥0 := ⟨X, hx.le.trans hX⟩
      let atomY : actualAtoms M Y := ⟨x, ⟨⟨hx, hX⟩, hpos⟩⟩
      exact (actual_prefix_loss_bounds M hc hm h₀ Y (fun x hx => he x hx.1) hγ hσ hgraph).2.2 atomY)
    exact hJ.ne' hz

/-- Every actual optimizer satisfies the unique feedback density almost
everywhere on each compact positive physical window. -/
theorem actual_optimal_feedback (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (he : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    (hopt : M.reward γ φ = ENNReal.ofReal (feedbackValue γ σ 1)) (L : ℝ≥0) :
    ∀ᵐ x ∂volume.restrict (Ioc 0 (L : ℝ)), M.typeDensity x =
      integralSlope M.measure φ x / (φ x * Real.sqrt
        (σ (φ x * integralSlope M.measure φ x / integralEnergy M.measure φ x))) := by
  have hzero := (actual_optimal_losses_zero M hc hm h₀ he hγ hσ hgraph hopt).1 L
  have hi := (actual_fundamental_identity M hc hm h₀ L (fun x hx => he x hx.1) hγ hσ hgraph).1
  have hzae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun x => actualSquareCost_nonneg M γ σ φ x)) hi).1 hzero
  filter_upwards [hzae, ae_restrict_mem measurableSet_Ioc] with x hx hxL
  have hp := compactStateDomain_positive_ratio M φ L (clippedState_mem M hc hm h₀ L x)
  simp only [clippedState, clipTime_of_mem L (Ioc_subset_Icc_self hxL)] at hp
  have hpow : integralEnergy M.measure φ x ^ (-γ) ≠ 0 := (Real.rpow_pos_of_pos hp.2.2.1 _).ne'
  have hsquare := (mul_eq_zero.1 hx).resolve_left hpow
  exact (square_zero_iff_feedback hp.1 hp.2.1
    (Real.sqrt_pos.2 (hgraph _ hp.2.2.2).positive) (M.typeDensity x)).1 hsquare

/-- Every actual optimizer has no singular mass on the positive physical
axis. The distinguished unit origin atom is retained by the open-left window. -/
theorem actual_optimal_singularPart_zero (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (he : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    (hopt : M.reward γ φ = ENNReal.ofReal (feedbackValue γ σ 1)) (L : ℝ≥0) :
    M.measure.singularPart volume (Ioc 0 (L : ℝ)) = 0 := by
  obtain ⟨_hsq, hsc, hno⟩ := actual_optimal_losses_zero M hc hm h₀ he hγ hσ hgraph hopt
  have hi := (actual_cadlag_cost_identity M hc hm h₀ L (fun x hx => he x hx.1) hγ.ne' hσ hgraph).2.2.1
  have hnonneg : 0 ≤ᵐ[(continuousSingularMass M).restrict (Ioc 0 (L : ℝ))] massCost M γ σ φ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (massCost_pos M hc hm h₀ L γ (fun r hr => (hgraph r hr).positive) (Ioc_subset_Icc_self hx)).le
  have hzae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).1 (hsc L)
  have hfalse : ∀ᵐ x ∂(continuousSingularMass M).restrict (Ioc 0 (L : ℝ)), False := by
    filter_upwards [hzae, ae_restrict_mem measurableSet_Ioc] with x hx hxL
    exact (massCost_pos M hc hm h₀ L γ (fun r hr => (hgraph r hr).positive)
      (Ioc_subset_Icc_self hxL)).ne' hx
  have hμ : (continuousSingularMass M).restrict (Ioc 0 (L : ℝ)) = 0 :=
    ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hfalse)
  have hat : Ioc (0 : ℝ) L ∩ massAtomSet M = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hpos : 0 < M.measure {x} := hx.2
    exact hpos.ne' (hno x hx.1.1)
  rw [singularPart_eq_continuous_add_atoms, Measure.add_apply,
    Measure.restrict_apply measurableSet_Ioc, hat, measure_empty,
    Measure.restrict_eq_zero.1 hμ, add_zero]

end
end krylov.ContinuumBV
