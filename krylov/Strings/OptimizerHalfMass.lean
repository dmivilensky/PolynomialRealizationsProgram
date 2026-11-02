import krylov.Strings.OptimizerMassBounds

/-!
Article: main_krylov, thm:value, exact total mass at gamma=1/2.
Use: supply one actual optimizing Stieltjes string whose total mass equals
its shooting coordinate and whose initial density is its reciprocal.
Source: actual global shooting construction and the proved half mass balance.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

/-- A single genuinely constructed half-gamma string has both the exact
reward and exact total mass. This is the string needed by the later
principal-measure atom-at-zero identification. -/
theorem exists_actual_half_mass_attainment :
    ∃ s₀ : ℝ, 1 < s₀ ∧
      (∀ G : krylov.LotkaVolterra.SubcriticalGraph (1 / 2), s₀ = G.σ 1) ∧
      ∃ M : Mass, ∃ φ : ℝ → ℝ,
      Continuous φ ∧ φ 0 = 1 ∧
      (∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t) ∧
      Tendsto M.typeClock atTop atTop ∧
      HasDerivWithinAt M.cumulative s₀⁻¹ (Ici 0) 0 ∧
      M.reward (1 / 2) φ = ENNReal.ofReal (Real.sqrt s₀) ∧
      Tendsto M.cumulative atTop (𝓝 s₀) := by
  obtain ⟨s, U, hs, hU, hU₀, hpos, hUone, _, hode, hsinf, hUinf, _, hcanonical, _⟩ :=
    exists_subcritical_data (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hp : ∀ t, 0 < s t := fun t ↦ zero_lt_one.trans (hpos t).1
  have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ (hpos t).1.le
  have hUp : ∀ t ≥ 0, 0 < U t := fun t _ ↦ (hpos t).2
  have hd := fun t (_ : 0 < t) ↦ hode t
  have htermLV := krylov.ContinuumControl.orbitValue_tendsto_zero_of_finite_state
    (by norm_num : (0 : ℝ) < 1 / 2)
    (krylov.LotkaVolterra.saddleS_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num))
    (krylov.LotkaVolterra.saddleU_pos (by norm_num : (1 / 2 : ℝ) < 1))
    hsinf hUinf (expPrimitive_tendsto_atTop hU hUone)
  have hterm : Tendsto (physicalOrbitValue (1 / 2) s U) atTop (𝓝 0) :=
    htermLV.comp (inverseClock_tendsto_atTop hs hp h₁)
  obtain ⟨hφ, _, _⟩ := extended_coordinates_continuous hs hU hp h₁
  have hφ₀ := (extended_initial (U := U) hs hp).1
  refine ⟨s 0, (hpos 0).1, hcanonical, constructedMass s hs hp h₁, extendedPosition s, hφ, hφ₀,
    ?_, constructedMass_typeClock_tendsto_atTop hs hp h₁,
    constructedMass_right_derivative hs hp h₁, ?_, ?_⟩
  · intro x hx
    obtain ⟨hφx, _, _⟩ := constructedMass_state hs hU hp h₁ hU₀
      (fun t ht ↦ (hd t ht).2) hx
    rw [hφx]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (constructedMass_state hs hU hp h₁ hU₀ (fun t ht ↦ (hd t ht).2) ht.1.le).2.1
  · have hr := constructedMass_reward_allGamma (by norm_num : (1 / 2 : ℝ) ≠ 0)
      hs hU hp h₁ hU₀ hUp hd hterm
    norm_num at hr ⊢
    exact hr
  · apply constructedMass_half_total_mass hs hU hp h₁ hU₀ hd
    · norm_num [krylov.LotkaVolterra.saddleS] at hsinf
      exact hsinf
    · norm_num [krylov.LotkaVolterra.saddleU] at hUinf
      exact hUinf

end
end krylov.Strings.OptimizerQuadratures
