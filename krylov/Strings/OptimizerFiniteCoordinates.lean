import krylov.Strings.OptimizerFiniteClock

/-!
Article: main_krylov, apC:eq:state, finite-endpoint coordinate construction.
Use: construct single global physical slope and energy functions, rather than
leaving them as a compatible family of compact reconstructions.
Source: proved exact locality of the positive mass measures and compact state
construction. This includes finite endpoints with divergent cumulative mass.
-/

namespace krylov.Strings.OptimizerFinite
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal

/-- Compatible physical coordinates on compact windows can be glued throughout
the source domain. Compatibility is the only premise; no desired equation or
regularity is smuggled into the construction. -/
theorem exists_glued_coordinate {ℓ : ℝ} (hℓ : 0 < ℓ) (A : Windows ℓ → ℝ → ℝ)
    (hA : ∀ w v : Windows ℓ, EqOn (A w) (A v)
      (Icc 0 ((min w.val v.val : ℝ≥0) : ℝ))) :
    ∃ a : ℝ → ℝ, ∀ w : Windows ℓ, EqOn a (A w) (Icc 0 (w.val : ℝ)) := by
  let windowAt (x : ℝ) (hx : x < ℓ) : Windows ℓ :=
    ⟨⟨(max x 0 + ℓ) / 2, by linarith [le_max_right x 0]⟩,
      by
        change (max x 0 + ℓ) / 2 < ℓ
        have hmax : max x 0 < ℓ := max_lt hx hℓ
        linarith⟩
  let a : ℝ → ℝ := fun x ↦ if hx : x < ℓ then A (windowAt x hx) x else 1
  refine ⟨a, ?_⟩
  intro w x hx
  have hxℓ : x < ℓ := hx.2.trans_lt w.property
  have hbound : x ≤ ((windowAt x hxℓ).val : ℝ) := by
    change x ≤ (max x 0 + ℓ) / 2
    linarith [le_max_left x 0]
  dsimp [a]
  rw [dite_eq_left hxℓ]
  exact hA (windowAt x hxℓ) w ⟨hx.1, by simpa using le_min hbound hx.2⟩

/-- Slopes reconstructed from an arbitrary physical position agree across
mass representatives; no continuity assumption is needed for this equality. -/
theorem slope_compatible {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    (φ : ℝ → ℝ) (w v : Windows ℓ) :
    EqOn (integralSlope (windowMass hℓ f h₀ w).measure φ)
      (integralSlope (windowMass hℓ f h₀ v).measure φ)
      (Icc 0 ((min w.val v.val : ℝ≥0) : ℝ)) := by
  intro x hx
  dsimp [integralSlope]
  rw [Mass.restrict_initial_eq_of_restrict_eq _ _ (windowMass_compatible hℓ f h₀ w v) hx.2]

/-- The same exact locality holds for the energy coordinate. -/
theorem energy_compatible {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    (φ : ℝ → ℝ) (w v : Windows ℓ) :
    EqOn (integralEnergy (windowMass hℓ f h₀ w).measure φ)
      (integralEnergy (windowMass hℓ f h₀ v).measure φ)
      (Icc 0 ((min w.val v.val : ℝ≥0) : ℝ)) := by
  intro x hx
  dsimp [integralEnergy]
  rw [Mass.restrict_initial_eq_of_restrict_eq _ _ (windowMass_compatible hℓ f h₀ w v) hx.2]

/-- Actual global `(φ,p,K)` coordinates of a finite-endpoint string. The
position equation now integrates the single constructed slope `p`, and both
mass coordinates agree with every original compact mass representative.
-/
theorem exists_full_state {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) :
    ∃ φ p K : ℝ → ℝ, ContinuousOn φ (Iio ℓ) ∧ φ 0 = 1 ∧ p 0 = 1 ∧ K 0 = 1 ∧
      MonotoneOn φ (Iio ℓ) ∧ ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ),
        φ x = 1 + ∫ t in Ioc 0 x, p t ∧
        p x = integralSlope (windowMass hℓ f h₀ w).measure φ x ∧
        K x = integralEnergy (windowMass hℓ f h₀ w).measure φ x ∧
        1 ≤ φ x ∧ 1 ≤ p x ∧ 1 ≤ K x ∧ 1 ≤ stateRatio (φ x) (p x) (K x) := by
  obtain ⟨φ, hc, hz, hm, _, he⟩ := exists_state hℓ f h₀
  obtain ⟨p, hp⟩ := exists_glued_coordinate hℓ
    (fun w ↦ integralSlope (windowMass hℓ f h₀ w).measure φ) (slope_compatible hℓ f h₀ φ)
  obtain ⟨K, hK⟩ := exists_glued_coordinate hℓ
    (fun w ↦ integralEnergy (windowMass hℓ f h₀ w).measure φ) (energy_compatible hℓ f h₀ φ)
  let zeroWindow : Windows ℓ := ⟨0, hℓ⟩
  have hp₀ : p 0 = 1 := by
    rw [hp zeroWindow ⟨le_rfl, le_rfl⟩]
    simp [integralSlope]
  have hK₀ : K 0 = 1 := by
    rw [hK zeroWindow ⟨le_rfl, le_rfl⟩]
    simp [integralEnergy]
  refine ⟨φ, p, K, hc, hz, hp₀, hK₀, hm, ?_⟩
  intro w x hx
  have hφx : 1 ≤ φ x := by
    rw [← hz]
    exact hm hℓ (hx.2.trans_lt w.property) hx.1
  refine ⟨?_, hp w hx, hK w hx, hφx, ?_, ?_, ?_⟩
  · rw [he w x hx]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact (hp w ⟨ht.1.le, ht.2.trans hx.2⟩).symm
  · rw [hp w hx]
    have hi : 0 ≤ ∫ t in Ioc 0 x, φ t ∂(windowMass hℓ f h₀ w).measure := by
      apply setIntegral_nonneg measurableSet_Ioc
      intro t ht
      have hφt : φ 0 ≤ φ t := hm hℓ ((ht.2.trans hx.2).trans_lt w.property) ht.1.le
      rw [hz] at hφt
      exact zero_le_one.trans hφt
    dsimp [integralSlope]
    linarith
  · rw [hK w hx]
    exact integralEnergy_one_le _ _ _
  · rw [hp w hx, hK w hx]
    exact state_ratio_ge_one hℓ f h₀ hc hm hz w hx

end
end krylov.Strings.OptimizerFinite
