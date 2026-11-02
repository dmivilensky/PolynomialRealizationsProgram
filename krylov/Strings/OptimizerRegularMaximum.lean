import krylov.Strings.OptimizerAllLengths
import krylov.Strings.OptimizerAsymptotics
import krylov.Strings.OptimizerAnalyticFlow
import krylov.Strings.OptimizerMonotone

/-!
Article: main_krylov, thm:value, regularity of the same unique maximizing mass.
Use: assemble actual attainment, uniqueness, analytic positive density, its
RN clock and the mass/shape conclusions for one and the same constructed
Stieltjes mass. The records below collect proved conclusions; none of their
fields is an admissibility hypothesis on competing strings.
Source: the constructed global LV orbits, quadratures and full BV equality
theorem, together with the derived exponential orbit-error estimates.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open krylov.ContinuumControl krylov.LotkaVolterra
open scoped Topology NNReal

/-- Proved regularity of the actual mass, including its chosen continuous
density representative and its RN-defined clock. -/
structure RegularOptimizerDensity (M : Mass) (v : ℝ → ℝ) (s₀ : ℝ) : Prop where
  /-- The chosen square-root density representative is continuous on its real extension. -/
  continuous : Continuous v
  /-- Its values are strictly positive throughout the source physical domain. -/
  positive : ∀ x ≥ 0, 0 < v x
  /-- The density representative is real analytic at every positive physical position. -/
  analytic_pos : ∀ x > 0, AnalyticAt ℝ v x
  /-- At the initial endpoint the actual density has an analytic right germ. -/
  analytic_zero : AnalyticWithinAt ℝ v (Ici 0) 0
  /-- On each compact positive window it represents the actual RN square-root density. -/
  rn_density : ∀ L : ℝ≥0, M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] v
  /-- The actual cumulative mass is its unit origin atom plus the primitive of the squared density. -/
  cumulative : ∀ x ≥ 0, M.cumulative x = 1 + ∫ t in (0 : ℝ)..x, v t ^ 2
  /-- The actual RN-defined type clock is the primitive of this same density representative. -/
  clock : ∀ x ≥ 0, M.typeClock x = ∫ t in (0 : ℝ)..x, v t
  /-- The source type variable reaches arbitrarily large values on the physical half-line. -/
  clock_unbounded : Tendsto M.typeClock atTop atTop
  /-- The initial feedback density is determined by the shooting coordinate. -/
  initial_density : v 0 = 1 / Real.sqrt s₀
  /-- The actual cumulative mass has the stated right derivative after its unit origin atom. -/
  initial_mass_derivative : HasDerivWithinAt M.cumulative s₀⁻¹ (Ici 0) 0

/-- All qualitative continuum conclusions refer to this same actual mass.
Competitors satisfy only the original `IsState` equation. -/
structure ActualRegularMaximum (γ : ℝ) (σ : ℝ → ℝ) (M : Mass) (φ v : ℝ → ℝ) : Prop where
  /-- The actual mass and position satisfy the original source Volterra state equation. -/
  state : IsState M φ
  /-- Its genuine extended reward attains the value determined by the named graph crossing. -/
  value : M.reward γ φ = ENNReal.ofReal (Real.sqrt (σ 1) / (2 * γ))
  /-- All density, initial regularity and clock conclusions refer to this same actual mass. -/
  density : RegularOptimizerDensity M v (σ 1)
  /-- At every source physical position the chosen density obeys the named-graph feedback law. -/
  feedback : ∀ x ≥ 0, v x = actualFeedbackDensity M φ σ x
  /-- Every half-line competitor satisfying the original state equation has no larger reward. -/
  dominates : ∀ N : Mass, ∀ ψ : ℝ → ℝ, IsState N ψ → N.reward γ ψ ≤ M.reward γ φ
  /-- Equality for any such competitor identifies its actual Stieltjes mass with this mass. -/
  unique : ∀ N : Mass, ∀ ψ : ℝ → ℝ, IsState N ψ → N.reward γ ψ = M.reward γ φ → N = M
  /-- For subcritical gamma the actual total mass is finite, with a quantitative upper bound. -/
  finite_mass : γ < 1 → ∃ m : ℝ, 1 ≤ m ∧ m ≤ 1 + 1 / γ ∧ Tendsto M.cumulative atTop (𝓝 m)
  /-- At half gamma the actual total mass equals the initial graph crossing. -/
  half_mass : γ = (1 / 2 : ℝ) → Tendsto M.cumulative atTop (𝓝 (σ 1))
  /-- Subcritical energy and density have positive limiting exponential amplitudes in the actual type clock. -/
  subcritical_shape : γ < 1 → ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    Tendsto (fun x ↦ integralEnergy M.measure φ x ^ (-γ) /
      Real.exp (-(γ * saddleU γ / Real.sqrt (saddleS γ)) * M.typeClock x)) atTop (𝓝 a) ∧
    Tendsto (fun x ↦ v x /
      Real.exp (-((saddleS γ - 1) / Real.sqrt (saddleS γ)) * M.typeClock x)) atTop (𝓝 b)

namespace OptimizerQuadratures

/-- The constructed actual mass has full density regularity, its analytic initial germ and its genuine type clock. -/
theorem constructedMass_regularDensity {γ : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t) :
    RegularOptimizerDensity (constructedMass s hs hp h₁) (extendedDensity s) (s 0) := by
  refine ⟨extendedDensity_continuous hs hp h₁, fun x _ ↦ extendedDensity_pos hp x,
    fun _ hx ↦ analyticAt_extendedDensity hs hp h₁ hode hx,
    analyticWithinAt_extendedDensity_zero hs hU hp h₁ hode,
    constructedMass_typeDensity hs hp h₁, ?_, fun _ hx ↦ constructedMass_typeClock hs hp h₁ hx,
    constructedMass_typeClock_tendsto_atTop hs hp h₁, extendedDensity_initial hs hp,
    constructedMass_right_derivative hs hp h₁⟩
  exact fun _ hx ↦ OptimizerDensity.globalCumulative_eq _ (extendedDensity_continuous hs hp h₁) hx

/-- The constructed density obeys the named-graph law using its actual mass-integral state. -/
theorem constructedMass_feedback {σ s U : ℝ → ℝ} (hs : Continuous s) (hU : Continuous U)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    (hgraph : ∀ t ≥ 0, s t = σ (U t)) {x : ℝ} (hx : 0 ≤ x) :
    extendedDensity s x = actualFeedbackDensity (constructedMass s hs hp h₁) (extendedPosition s) σ x := by
  obtain ⟨_, hP, hK⟩ := constructedMass_state hs hU hp h₁ hU₀ hode hx
  have hh := constructed_density_feedback hs hU hp h₁ hU₀ hode hgraph hx
  change extendedDensity s x = feedbackDensity (extendedPosition s x)
    (integralSlope (constructedMass s hs hp h₁).measure (extendedPosition s) x)
    (Real.sqrt (σ (stateRatio (extendedPosition s x)
      (integralSlope (constructedMass s hs hp h₁).measure (extendedPosition s) x)
      (integralEnergy (constructedMass s hs hp h₁).measure (extendedPosition s) x))))
  rw [← hP, ← hK]
  exact hh

end OptimizerQuadratures

/-- Actual attainment and regularity yield domination and uniqueness through the full BV equality theorem. -/
theorem actualRegularMaximum_of_value {γ : ℝ} (hγ : 0 < γ) {σ : ℝ → ℝ}
    (hσ : ∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt γ σ r)
    {M : Mass} {φ v : ℝ → ℝ} (hstate : IsState M φ)
    (hvalue : M.reward γ φ = ENNReal.ofReal (Real.sqrt (σ 1) / (2 * γ)))
    (hdensity : RegularOptimizerDensity M v (σ 1))
    (hfeedback : ∀ x ≥ 0, v x = actualFeedbackDensity M φ σ x)
    (hfinite : γ < 1 → ∃ m : ℝ, 1 ≤ m ∧ m ≤ 1 + 1 / γ ∧ Tendsto M.cumulative atTop (𝓝 m))
    (hhalf : γ = (1 / 2 : ℝ) → Tendsto M.cumulative atTop (𝓝 (σ 1)))
    (hshape : γ < 1 → ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Tendsto (fun x ↦ integralEnergy M.measure φ x ^ (-γ) /
        Real.exp (-(γ * saddleU γ / Real.sqrt (saddleS γ)) * M.typeClock x)) atTop (𝓝 a) ∧
      Tendsto (fun x ↦ v x /
        Real.exp (-((saddleS γ - 1) / Real.sqrt (saddleS γ)) * M.typeClock x)) atTop (𝓝 b)) :
    ActualRegularMaximum γ σ M φ v := by
  have hopt : M.reward γ φ = ENNReal.ofReal (feedbackValue γ σ 1) := by
    rw [hvalue, feedbackValue_one γ σ (hσ 1 le_rfl).2.positive]
  refine ⟨hstate, hvalue, hdensity, hfeedback, ?_, ?_, hfinite, hhalf, hshape⟩
  · intro N ψ hN
    rw [hopt]
    exact hN.reward_le hγ (fun r hr ↦ (hσ r hr).1.contDiffAt) (fun r hr ↦ (hσ r hr).2)
  · intro N ψ hN heq
    exact hN.mass_unique_of_optimal_reward hstate hγ
      (fun r hr ↦ (hσ r hr).1.contDiffAt) (fun r hr ↦ (hσ r hr).2) (heq.trans hopt) hopt

namespace OptimizerQuadratures

/-- Every named subcritical graph has an actual unique maximizing mass
with all regularity, mass and shape conclusions proved for that same mass. -/
theorem exists_actual_subcritical_regular_maximum {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G : SubcriticalGraph γ) :
    ∃ M : Mass, ∃ φ v : ℝ → ℝ, ActualRegularMaximum γ G.σ M φ v := by
  obtain ⟨s, U, hs, hU, hU₀, hpos, hUone, hcorr, hode, hsinf, hUinf, hexp, hcanonical, hpath⟩ :=
    exists_subcritical_data hγ hγ₁
  have hp : ∀ t, 0 < s t := fun t ↦ zero_lt_one.trans (hpos t).1
  have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ (hpos t).1.le
  have hUp : ∀ t ≥ 0, 0 < U t := fun t _ ↦ (hpos t).2
  have hd := fun t (_ : 0 < t) ↦ hode t
  have hgraph : ∀ r ≥ 1, AnalyticAt ℝ G.σ r ∧ FeedbackGraphAt γ G.σ r :=
    fun r hr ↦ ⟨G.analyticAt hγ hγ₁ (by linarith), subcritical_feedbackGraphAt G hγ hγ₁ (by linarith)⟩
  have htermLV := orbitValue_tendsto_zero_of_finite_state hγ (saddleS_pos hγ hγ₁)
    (saddleU_pos hγ₁) hsinf hUinf (expPrimitive_tendsto_atTop hU hUone)
  have hterm : Tendsto (physicalOrbitValue γ s U) atTop (𝓝 0) :=
    htermLV.comp (inverseClock_tendsto_atTop hs hp h₁)
  obtain ⟨hφ, _, _⟩ := extended_coordinates_continuous hs hU hp h₁
  have hstate : IsState (constructedMass s hs hp h₁) (extendedPosition s) :=
    isState_of_coordinates _ hφ (extended_initial (U := U) hs hp).1 (fun x hx ↦ by
      obtain ⟨hφx, hpx, _⟩ := constructedMass_state hs hU hp h₁ hU₀ (fun t ht ↦ (hd t ht).2) hx
      exact ⟨hφx, hpx⟩)
  have hvalue := constructedMass_reward_allGamma hγ.ne' hs hU hp h₁ hU₀ hUp hd hterm
  rw [hcanonical G] at hvalue
  have hreg := constructedMass_regularDensity hs hU hp h₁ hd
  rw [hcanonical G] at hreg
  have hfeedback : ∀ x ≥ 0, extendedDensity s x =
      actualFeedbackDensity (constructedMass s hs hp h₁) (extendedPosition s) G.σ x :=
    fun _ hx ↦ constructedMass_feedback hs hU hp h₁ hU₀ (fun t ht ↦ (hd t ht).2)
      (fun t _ ↦ hpath G t) hx
  refine ⟨constructedMass s hs hp h₁, extendedPosition s, extendedDensity s,
    actualRegularMaximum_of_value hγ hgraph hstate hvalue hreg hfeedback ?_ ?_ ?_⟩
  · intro _
    apply constructedMass_finite_limit hγ hs hp h₁
    intro t ht
    have hmul := mul_le_mul_of_nonneg_left (hUone t ht) hγ.le
    linarith [(hcorr t).1]
  · intro hhalf
    subst γ
    norm_num [saddleS, saddleU] at hsinf hUinf
    simpa only [hcanonical G] using constructedMass_half_total_mass hs hU hp h₁ hU₀ hd hsinf hUinf
  · intro _
    obtain ⟨C, _, hbound⟩ := hexp
    have hsb : ∀ t ≥ 0, |s t - saddleS γ| ≤ C * Real.exp (-2 * t) := by
      intro t ht
      linarith [hbound t ht, abs_nonneg (U t - saddleU γ)]
    have hUb : ∀ t ≥ 0, |U t - saddleU γ| ≤ C * Real.exp (-2 * t) := by
      intro t ht
      linarith [hbound t ht, abs_nonneg (s t - saddleS γ)]
    have hsF : 1 ≤ saddleS γ := by
      have hrel := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
      nlinarith [mul_pos hγ (saddleU_pos hγ₁)]
    obtain ⟨a, b, ha, hb, hK, hv⟩ := constructedMass_exponential_amplitudes
      (γ := γ) hs hU hp h₁ hsF hsinf hsb hUb
    refine ⟨a, b, ha, hb, ?_, hv⟩
    apply hK.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [← (constructedMass_state hs hU hp h₁ hU₀ (fun t ht ↦ (hd t ht).2) hx).2.2]

/-- The named endpoint graph generates an actual unique optimizer with all density and clock conclusions. -/
theorem exists_actual_endpoint_regular_maximum {σ : ℝ → ℝ}
    (hσ : ∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt 1 σ r)
    (hb : ∀ r ≥ 1, r + 1 < σ r ∧ σ r < r + 3)
    (hd : ∀ r ≥ 1, HasDerivAt σ
      (2 * σ r * (σ r - 1 - r) / (r * (σ r + 1 - r))) r) :
    ∃ M : Mass, ∃ φ v : ℝ → ℝ, ActualRegularMaximum 1 σ M φ v := by
  obtain ⟨e, he, s, U, hs, hU, hU₀, hs₂, hode, hc, hgraph⟩ := exists_endpoint_data_with_graph
  have hp : ∀ t, 0 < s t := fun t ↦ lt_of_lt_of_le (by norm_num) (hs₂ t)
  have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ by linarith [hs₂ t]
  have hcorr : ∀ t ≥ 0, 1 ≤ U t ∧ U t + 1 ≤ s t ∧ s t ≤ 4 * U t := by
    intro t ht
    have hexp : 1 ≤ Real.exp (2 * t) := Real.one_le_exp_iff.mpr (by positivity)
    exact ⟨hexp.trans (hc t ht).2.2.2, (hc t ht).1.le, (hc t ht).2.2.1⟩
  have hUinf : Tendsto U atTop atTop := by
    apply tendsto_atTop_mono' atTop
      ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht ↦ (hc t ht).2.2.2))
    exact Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hcross : s 0 = σ 1 := by
    have hh := hgraph 0 le_rfl
    rw [hU₀] at hh
    rw [endpoint_graph_eq_of_gap hb hd he 1 le_rfl]
    exact hh
  obtain ⟨hφ, _, _⟩ := extended_coordinates_continuous hs hU hp h₁
  have hstate : IsState (constructedMass s hs hp h₁) (extendedPosition s) :=
    isState_of_coordinates _ hφ (extended_initial (U := U) hs hp).1 (fun x hx ↦ by
      obtain ⟨hφx, hpx, _⟩ := constructedMass_state hs hU hp h₁ hU₀ (fun t ht ↦ (hode t ht).2) hx
      exact ⟨hφx, hpx⟩)
  have hvalue := constructedMass_reward hs hU hp h₁ hU₀ hode hcorr hUinf
  rw [hcross] at hvalue
  have hreg := constructedMass_regularDensity (γ := 1) hs hU hp h₁ (by simpa only [one_mul] using hode)
  rw [hcross] at hreg
  have hpath : ∀ t ≥ 0, s t = σ (U t) := by
    intro t ht
    exact (hgraph t ht).trans (endpoint_graph_eq_of_gap hb hd he _ (hcorr t ht).1).symm
  have hfeedback : ∀ x ≥ 0, extendedDensity s x =
      actualFeedbackDensity (constructedMass s hs hp h₁) (extendedPosition s) σ x :=
    fun _ hx ↦ constructedMass_feedback hs hU hp h₁ hU₀ (fun t ht ↦ (hode t ht).2) hpath hx
  refine ⟨constructedMass s hs hp h₁, extendedPosition s, extendedDensity s,
    actualRegularMaximum_of_value (by norm_num) hσ hstate ?_ hreg hfeedback ?_ ?_ ?_⟩
  · simpa only [mul_one] using hvalue
  · intro h
    norm_num at h
  · intro h
    norm_num at h
  · intro h
    norm_num at h

end OptimizerQuadratures

/-- Coherent actual regularity and shape for the same unique maximizing
mass, for the complete source range of gamma. -/
theorem exists_actual_regular_maximum {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) :
    ∃ σ : ℝ → ℝ,
      (∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt γ σ r) ∧
      ∃ M : Mass, ∃ φ v : ℝ → ℝ, ActualRegularMaximum γ σ M φ v := by
  rcases eq_or_lt_of_le hγ₁ with rfl | hlt
  · obtain ⟨σ, ε, hε, ha, hb⟩ := exists_analytic_endpoint_graph
    have hgraph : ∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt 1 σ r := by
      intro r hr
      have hh := ha r (by linarith)
      refine ⟨hh.1, hh.2.1, hh.1.differentiableAt, ?_⟩
      rw [hh.2.2.2.deriv]
      have hr₀ : r ≠ 0 := by linarith
      have hden : σ r + 1 - r ≠ 0 := hh.2.2.1.ne'
      field_simp
    refine ⟨σ, hgraph, ?_⟩
    exact OptimizerQuadratures.exists_actual_endpoint_regular_maximum hgraph
      (fun r hr ↦ ⟨(hb r hr).1, (hb r hr).2.1⟩)
      (fun r hr ↦ (ha r (by linarith)).2.2.2)
  · obtain ⟨G⟩ := exists_subcriticalGraph hγ hlt
    exact ⟨G.σ, fun r hr ↦ ⟨G.analyticAt hγ hlt (by linarith),
      subcritical_feedbackGraphAt G hγ hlt (by linarith)⟩,
      OptimizerQuadratures.exists_actual_subcritical_regular_maximum hγ hlt G⟩

end
end krylov.Strings
