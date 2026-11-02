import krylov.ContinuumBV.LocalCosts

/-!
Article: main_krylov, thm:value, equality for finite physical lengths.
Use: localize the full loss analysis to compact representatives of [0,ℓ).
No extension or boundedness at the excluded endpoint is assumed.
Source: actual RN locality, compact state extension and monotone reward exhaustion.
-/

namespace krylov.Strings.OptimizerFinite
noncomputable section
open Set Filter MeasureTheory
open krylov.ContinuumBV krylov.ContinuumControl
open scoped Topology NNReal ENNReal

/-- A finite-endpoint physical state has a globally continuous monotone
extension on each compact window, with exactly the original local equation. -/
theorem exists_compact_state_extension {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ))
    (hz : φ 0 = 1) (w : Windows ℓ)
    (he : ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Monotone ψ ∧ ψ 0 = 1 ∧
      EqOn φ ψ (Icc 0 (w.val : ℝ)) ∧
      ∀ x ∈ Icc 0 (w.val : ℝ), ψ x = 1 +
        ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure ψ t := by
  let ψ : ℝ → ℝ := IccExtend w.val.property (stateRestriction hc w)
  have hagree : EqOn φ ψ (Icc 0 (w.val : ℝ)) := by
    intro t ht
    exact (IccExtend_of_mem w.val.property (stateRestriction hc w) ht).symm
  exact ⟨ψ, (stateRestriction hc w).continuous.Icc_extend',
    (stateRestriction_monotone hc hm w).IccExtend w.val.property,
    (hagree ⟨le_rfl, w.val.property⟩).symm.trans hz, hagree,
    Mass.position_equation_congr _ w.val he hagree⟩

/-- The compact RN-defined rewards increase with the physical endpoint,
independently of the chosen mass extension. -/
theorem rewardPrefix_mono {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    (γ : ℝ) (φ : ℝ → ℝ) {w v : Windows ℓ} (hwv : w.val ≤ v.val) :
    (windowMass hℓ f h₀ w).rewardPrefix γ φ w.val ≤
      (windowMass hℓ f h₀ v).rewardPrefix γ φ v.val := by
  have hμ : (windowMass hℓ f h₀ w).measure.restrict (Ioc 0 (w.val : ℝ)) =
      (windowMass hℓ f h₀ v).measure.restrict (Ioc 0 (w.val : ℝ)) := by
    simpa only [min_eq_left hwv] using windowMass_compatible hℓ f h₀ w v
  rw [rewardPrefix_eq_of_restrict_eq _ _ hμ (fun _ _ ↦ rfl) γ]
  exact Mass.rewardPrefix_mono _ γ φ (show (w.val : ℝ) ≤ (v.val : ℝ) from hwv)

/-- A fixed positive prefix loss is incompatible with finite-endpoint
attainment. The argument uses extended rewards, so divergent improper real
integrals cannot be silently replaced by zero. -/
theorem penalty_eq_zero_of_optimal_reward {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    (γ : ℝ) (φ : ℝ → ℝ) {C δ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ)
    (hopt : reward hℓ f h₀ γ φ = ENNReal.ofReal C) (w : Windows ℓ)
    (hprefix : ∀ v : Windows ℓ, w.val ≤ v.val →
      (windowMass hℓ f h₀ v).rewardPrefix γ φ v.val ≤ ENNReal.ofReal (C - δ)) : δ = 0 := by
  have hu : reward hℓ f h₀ γ φ ≤ ENNReal.ofReal (C - δ) := by
    apply iSup_le
    intro v
    rcases le_total w.val v.val with hwv | hvw
    · exact hprefix v hwv
    · exact (rewardPrefix_mono hℓ f h₀ γ φ hvw).trans (hprefix w le_rfl)
  rw [hopt] at hu
  by_contra hne
  have hpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hne)
  exact (not_lt_of_ge hu) ((ENNReal.ofReal_lt_ofReal_iff hC).2 (by linarith))

/-- Equality at a finite physical endpoint excludes each actual interior
atom, because its exact positive impulse loss persists in every later prefix. -/
theorem optimal_no_atoms {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ))
    (hz : φ 0 = 1)
    (he : ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hopt : reward hℓ f h₀ γ φ = ENNReal.ofReal (feedbackValue γ σ 1))
    (w : Windows ℓ) {x : ℝ} (hx : x ∈ Ioc 0 (w.val : ℝ)) :
    (windowMass hℓ f h₀ w).measure {x} = 0 := by
  obtain ⟨ψ, hcψ, hmψ, hψ₀, hφψ, heψ⟩ :=
    exists_compact_state_extension hℓ f h₀ hc hm hz w (he w)
  by_contra hne
  have hpos : 0 < (windowMass hℓ f h₀ w).measure {x} := bot_lt_iff_ne_bot.2 hne
  let atom : actualAtoms (windowMass hℓ f h₀ w) w.val := ⟨x, hx, hpos⟩
  have hJ := actualAtomLoss_pos _ hcψ hmψ hψ₀ w.val hgraph atom
  have hC := feedbackValue_pos hγ le_rfl (hgraph 1 le_rfl).positive
  have hzero := penalty_eq_zero_of_optimal_reward hℓ f h₀ γ φ hC hJ.le hopt w (by
    intro v hwv
    obtain ⟨χ, hcχ, hmχ, hχ₀, hφχ, heχ⟩ :=
      exists_compact_state_extension hℓ f h₀ hc hm hz v (he v)
    have hμ : (windowMass hℓ f h₀ w).measure.restrict (Ioc 0 (w.val : ℝ)) =
        (windowMass hℓ f h₀ v).measure.restrict (Ioc 0 (w.val : ℝ)) := by
      simpa only [min_eq_left hwv] using windowMass_compatible hℓ f h₀ w v
    have hagree : EqOn ψ χ (Icc 0 (w.val : ℝ)) := fun t ht ↦
      (hφψ ht).symm.trans (hφχ ⟨ht.1, ht.2.trans (show (w.val : ℝ) ≤ v.val from hwv)⟩)
    have hJloc := actualAtomLoss_eq_of_restrict_eq _ _ hcψ hcχ hμ hagree hx γ σ
    have hxv : x ∈ Ioc 0 (v.val : ℝ) := ⟨hx.1, hx.2.trans (show (w.val : ℝ) ≤ v.val from hwv)⟩
    have hposv : 0 < (windowMass hℓ f h₀ v).measure {x} := by
      rw [← singleton_eq_of_restrict_eq _ _ hμ hx]
      exact hpos
    let atomv : actualAtoms (windowMass hℓ f h₀ v) v.val := ⟨x, hxv, hposv⟩
    have hb := (actual_prefix_loss_bounds _ hcχ hmχ hχ₀ v.val heχ hγ hσ hgraph).2.2 atomv
    rw [← hJloc] at hb
    rw [Mass.rewardPrefix_eq_of_eqOn _ γ hφχ,
      actual_rewardPrefix_eq_ofReal_integral _ hγ.le hcχ]
    exact ENNReal.ofReal_le_ofReal (by simpa only [atom, Subtype.coe_mk] using
      (show (∫ t in Ioc 0 (v.val : ℝ),
        (windowMass hℓ f h₀ v).rewardDensity γ χ t) ≤
          feedbackValue γ σ 1 - actualAtomLoss (windowMass hℓ f h₀ w) γ σ ψ x by linarith)))
  exact hJ.ne' hzero

/-- Every compact square loss vanishes for a finite-endpoint optimizer.
The conclusion holds for any genuine extension of the same physical history. -/
theorem optimal_square_zero {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ))
    (hz : φ 0 = 1)
    (he : ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hopt : reward hℓ f h₀ γ φ = ENNReal.ofReal (feedbackValue γ σ 1))
    (w : Windows ℓ) {ψ : ℝ → ℝ} (hφψ : EqOn φ ψ (Icc 0 (w.val : ℝ))) :
    (∫ x in Ioc 0 (w.val : ℝ), actualSquareCost (windowMass hℓ f h₀ w) γ σ ψ x) = 0 := by
  have hδ : 0 ≤ 1 / 2 * (∫ x in Ioc 0 (w.val : ℝ),
      actualSquareCost (windowMass hℓ f h₀ w) γ σ ψ x) :=
    mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioc
      (fun x _ ↦ actualSquareCost_nonneg _ γ σ ψ x))
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
    have hsq := actualSquareCost_eq_ae_of_restrict_eq _ _ hμ hagree γ σ
    have hi := (actual_fundamental_identity _ hcχ hmχ hχ₀ v.val heχ hγ hσ hgraph).1
    have hmono : (∫ x in Ioc 0 (w.val : ℝ),
        actualSquareCost (windowMass hℓ f h₀ w) γ σ ψ x) ≤
        ∫ x in Ioc 0 (v.val : ℝ), actualSquareCost (windowMass hℓ f h₀ v) γ σ χ x := by
      rw [integral_congr_ae hsq]
      exact setIntegral_mono_set hi
        (Eventually.of_forall (fun x ↦ actualSquareCost_nonneg _ γ σ χ x))
        (Eventually.of_forall (fun _ hx ↦ Ioc_subset_Ioc le_rfl
          (show (w.val : ℝ) ≤ v.val from hwv) hx))
    have hb := (actual_prefix_loss_bounds _ hcχ hmχ hχ₀ v.val heχ hγ hσ hgraph).1
    rw [Mass.rewardPrefix_eq_of_eqOn _ γ hφχ,
      actual_rewardPrefix_eq_ofReal_integral _ hγ.le hcχ]
    exact ENNReal.ofReal_le_ofReal (by linarith))
  linarith

end
end krylov.Strings.OptimizerFinite
