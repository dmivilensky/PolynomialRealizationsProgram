import krylov.Strings.OptimizerOrbitAttainment

/-!
Article: main_krylov, thm:value, uniqueness interface for the actual optimizer.
Use: identify the constructed global physical state with the closed-loop
vector field for the named separating graph, at every physical position.
Source: the proved graph identity, conserved state ratio and feedback algebra.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- The extended physical position, slope and energy bundled into one feedback state. -/
def constructedFeedbackState (s U : ℝ → ℝ) (x : ℝ) : FeedbackState :=
  (extendedPosition s x, extendedSlope s x, extendedEnergy s U x)

/-- The constructed physical state's ratio is the actual LV ratio at inverse time. -/
theorem constructed_stateRatio {s U : ℝ → ℝ} (hs : Continuous s) (hU : Continuous U)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    {x : ℝ} (hx : 0 ≤ x) :
    stateRatio (extendedPosition s x) (extendedSlope s x) (extendedEnergy s U x) =
      U (inverseClock s x) := by
  obtain ⟨hφ, hP, hK, _⟩ := extended_coordinates_eq (U := U) hs hp hx
  rw [hφ, hP, hK]
  exact (coordinate_ratio hs hU hU₀ hode (inverseClock_nonneg hs hp h₁ hx)).symm

/-- The actual positive physical density is feedback for the named graph. -/
theorem constructed_density_feedback {σ s U : ℝ → ℝ} (hs : Continuous s)
    (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    (hgraph : ∀ t ≥ 0, s t = σ (U t)) {x : ℝ} (hx : 0 ≤ x) :
    extendedDensity s x = feedbackCurveDensity σ (constructedFeedbackState s U) x := by
  have hr := constructed_stateRatio hs hU hp h₁ hU₀ hode hx
  have hg : s (inverseClock s x) = σ (U (inverseClock s x)) :=
    hgraph _ (inverseClock_nonneg hs hp h₁ hx)
  obtain ⟨hφ, hP, _, hv⟩ := extended_coordinates_eq (U := U) hs hp hx
  change extendedDensity s x = feedbackDensity (extendedPosition s x) (extendedSlope s x)
    (Real.sqrt (σ (stateRatio (extendedPosition s x) (extendedSlope s x) (extendedEnergy s U x))))
  rw [hr, ← hg, hφ, hP, hv]
  rfl

/-- The constructed state is a global solution of the article's exact
closed-loop physical ODE for the named graph, not only a smooth string. -/
theorem constructedFeedbackState_hasDerivAt {σ s U : ℝ → ℝ} (hs : Continuous s)
    (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    (hgraph : ∀ t ≥ 0, s t = σ (U t)) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (constructedFeedbackState s U)
      (feedbackField σ (constructedFeedbackState s U x)) x := by
  have hst := extended_smoothStringAt hs hU hp h₁ hU₀ hode hx
  have hv := constructed_density_feedback hs hU hp h₁ hU₀ hode hgraph hx
  have hr := constructed_stateRatio hs hU hp h₁ hU₀ hode hx
  have hg : s (inverseClock s x) = σ (U (inverseClock s x)) :=
    hgraph _ (inverseClock_nonneg hs hp h₁ hx)
  have hσ : 0 < σ (stateRatio (extendedPosition s x) (extendedSlope s x) (extendedEnergy s U x)) := by
    rw [hr, ← hg]
    exact hp _
  obtain ⟨hpRate, hKRate⟩ := feedback_physical_rates (extendedPosition s x) (extendedSlope s x)
    (Real.sqrt (σ (stateRatio (extendedPosition s x) (extendedSlope s x) (extendedEnergy s U x))))
    (σ (stateRatio (extendedPosition s x) (extendedSlope s x) (extendedEnergy s U x)))
    hst.φ_pos.ne' (Real.sqrt_pos.mpr hσ).ne' (Real.sq_sqrt hσ.le)
  have hdp := hst.p_deriv
  have hdK := hst.K_deriv
  rw [hv] at hdp hdK
  change HasDerivAt (extendedSlope s)
    (extendedPosition s x * feedbackDensity (extendedPosition s x) (extendedSlope s x)
      (Real.sqrt (σ (stateRatio (extendedPosition s x) (extendedSlope s x) (extendedEnergy s U x)))) ^ 2) x at hdp
  change HasDerivAt (extendedEnergy s U)
    (extendedPosition s x ^ 2 * feedbackDensity (extendedPosition s x) (extendedSlope s x)
      (Real.sqrt (σ (stateRatio (extendedPosition s x) (extendedSlope s x) (extendedEnergy s U x)))) ^ 2) x at hdK
  rw [mul_comm, hpRate] at hdp
  rw [mul_comm, hKRate] at hdK
  exact hst.φ_deriv.prodMk (hdp.prodMk hdK)

/-- A genuine global physical closed-loop optimizer exists for every
named subcritical separating graph. The trajectory is constructed from the
unconditional global shooting theorem and has the prescribed unit state. -/
theorem exists_actual_global_closedLoop {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G : krylov.LotkaVolterra.SubcriticalGraph γ) :
    ∃ α : ℝ → FeedbackState, α 0 = (1, 1, 1) ∧
      (∀ x ≥ 0, HasDerivAt α (feedbackField G.σ (α x)) x) ∧
      ∀ x ≥ 0, 0 < (α x).1 ∧ 0 < (α x).2.1 ∧ 0 < (α x).2.2 := by
  obtain ⟨s, U, hs, hU, hU₀, hpos, _, _, hode, _, _, _, _, hgraph⟩ :=
    exists_subcritical_data hγ hγ₁
  have hp : ∀ t, 0 < s t := fun t ↦ zero_lt_one.trans (hpos t).1
  have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ (hpos t).1.le
  refine ⟨constructedFeedbackState s U, ?_, ?_, ?_⟩
  · obtain ⟨hφ₀, hp₀, hK₀⟩ := extended_initial (U := U) hs hp
    simp only [constructedFeedbackState, hφ₀, hp₀, hK₀]
  · intro x hx
    exact constructedFeedbackState_hasDerivAt hs hU hp h₁ hU₀ (fun t _ ↦ (hode t).2)
      (fun t _ ↦ hgraph G t) hx
  · intro x hx
    have hst := extended_smoothStringAt hs hU hp h₁ hU₀ (fun t _ ↦ (hode t).2) hx
    exact ⟨hst.φ_pos, hst.p_pos, hst.K_pos⟩

/-- The named feedback equation and genuine mass integral equations hold
for the very same constructed state and mass. -/
theorem constructedMass_closedLoop_state {σ s U : ℝ → ℝ} (hs : Continuous s)
    (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    (hgraph : ∀ t ≥ 0, s t = σ (U t)) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (constructedFeedbackState s U)
        (feedbackField σ (constructedFeedbackState s U x)) x ∧
      extendedPosition s x = 1 + ∫ t in Ioc 0 x, extendedSlope s t ∧
      extendedSlope s x = integralSlope (constructedMass s hs hp h₁).measure (extendedPosition s) x ∧
      extendedEnergy s U x = integralEnergy (constructedMass s hs hp h₁).measure (extendedPosition s) x :=
  ⟨constructedFeedbackState_hasDerivAt hs hU hp h₁ hU₀ hode hgraph hx,
    constructedMass_state hs hU hp h₁ hU₀ hode hx⟩

/-- Endpoint closed-loop construction keeps the actual shooting graph and
physical state together. The graph is the same one that generated the
global orbit, so no post hoc identification is assumed. -/
theorem exists_actual_endpoint_global_closedLoop :
    ∃ e : ℝ → ℝ,
      (∀ r ≥ 1, e r ∈ Icc (1 : ℝ) 3 ∧
        HasDerivAt e (krylov.LotkaVolterra.endpointGraphRate r (e r)) r) ∧
      ∃ α : ℝ → FeedbackState, α 0 = (1, 1, 1) ∧
        (∀ x ≥ 0, HasDerivAt α (feedbackField (fun r ↦ r + e r) (α x)) x) ∧
        ∀ x ≥ 0, 0 < (α x).1 ∧ 0 < (α x).2.1 ∧ 0 < (α x).2.2 := by
  obtain ⟨e, he, s, U, hs, hU, hU₀, hs₂, hode, _, hgraph⟩ := exists_endpoint_data_with_graph
  have hp : ∀ t, 0 < s t := fun t ↦ lt_of_lt_of_le (by norm_num) (hs₂ t)
  have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ by linarith [hs₂ t]
  refine ⟨e, he, constructedFeedbackState s U, ?_, ?_, ?_⟩
  · obtain ⟨hφ₀, hp₀, hK₀⟩ := extended_initial (U := U) hs hp
    simp only [constructedFeedbackState, hφ₀, hp₀, hK₀]
  · intro x hx
    exact constructedFeedbackState_hasDerivAt hs hU hp h₁ hU₀ (fun t ht ↦ (hode t ht).2)
      hgraph hx
  · intro x hx
    have hst := extended_smoothStringAt hs hU hp h₁ hU₀ (fun t ht ↦ (hode t ht).2) hx
    exact ⟨hst.φ_pos, hst.p_pos, hst.K_pos⟩

end
end krylov.Strings.OptimizerQuadratures
