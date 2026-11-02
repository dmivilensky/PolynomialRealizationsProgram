import krylov.Cost.FrobeniusDesign
import krylov.Cost.FiniteThreshold
import krylov.Asymptotics.SharpLimit

/-!
Article: main_krylov, cor:threshold and the scaling after prop:HS.
Use: the actual critical FC tolerance and sharp physical Hilbert--Schmidt
coefficient inherit the proved design limits, including simultaneous finite
cycle regimes. These are limits of the real optimized quantities.
Source: the exact design/FC and design/HS identities and continuous inversion
and square root, with the actual hyperbolic condition-number conversion.
-/

namespace krylov.Cost
noncomputable section
open Real Filter Set krylov.Design krylov.Asymptotics
open scoped Topology

/-- The actual critical tolerance has the printed kappa^-1/2 scale, with
its exact constant, whenever the actual half-power design has limit a. -/
theorem criticalTolerance_sqrt_kappa_tendsto {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} {M : α → ℕ} {a : ℝ}
    (ha : a ≠ 0) (hκ : Tendsto (fun i ↦ (I i).kappa) l atTop)
    (hV : Tendsto (fun i ↦ designSpacing (I i) * optimalValue (I i) (M i) (fun _ ↦ 1) (1 / 2)) l (𝓝 a)) :
    Tendsto (fun i ↦ criticalTolerance (I i) (M i) * sqrt (I i).kappa) l (𝓝 (2 / a)) := by
  have hc := criticalTolerance_scaled_tendsto I M ha hV
  have hh := hc.mul (spacing_mul_sqrt_kappa_tendsto hκ)
  have hl : a⁻¹ * 2 = 2 / a := by ring
  rw [hl] at hh
  apply hh.congr
  intro i
  have hp := (designSpacing_pos (I i)).ne'
  field_simp

/-- The sharp physical Frobenius coefficient has its exact theta^-1/2
scale, directly from the actual gamma-one design optimum. -/
theorem hsWorstCoefficient_sqrt_spacing_tendsto {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} {M : α → ℕ} {a : ℝ}
    (hV : Tendsto (fun i ↦ designSpacing (I i) * optimalValue (I i) (M i) (fun _ ↦ 1) 1) l (𝓝 a)) :
    Tendsto (fun i ↦ sqrt (designSpacing (I i)) * hsWorstCoefficient (I i) (M i)) l (𝓝 (sqrt (a / 2))) := by
  have hh := (hV.div_const 2).sqrt
  apply hh.congr
  intro i
  rw [hsWorstCoefficient_eq_design, ← sqrt_mul (designSpacing_pos (I i)).le]
  congr 1
  ring

/-- The square root of the actual spacing/condition-number conversion
gives the exact kappa^1/4 conversion needed by the HS coefficient. -/
theorem sqrt_spacing_sqrt_sqrt_kappa_tendsto {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} (hκ : Tendsto (fun i ↦ (I i).kappa) l atTop) :
    Tendsto (fun i ↦ sqrt (designSpacing (I i)) * sqrt (sqrt (I i).kappa)) l (𝓝 (sqrt 2)) := by
  have hh := (spacing_mul_sqrt_kappa_tendsto hκ).sqrt
  apply hh.congr
  intro i
  exact sqrt_mul (designSpacing_pos (I i)).le _

/-- The printed order kappa^1/4 is an actual positive finite limit for
the sharp physical HS coefficient, with the continuum constant retained. -/
theorem hsWorstCoefficient_quarter_kappa_tendsto {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} {M : α → ℕ} {a : ℝ}
    (hκ : Tendsto (fun i ↦ (I i).kappa) l atTop)
    (hV : Tendsto (fun i ↦ designSpacing (I i) * optimalValue (I i) (M i) (fun _ ↦ 1) 1) l (𝓝 a)) :
    Tendsto (fun i ↦ hsWorstCoefficient (I i) (M i) / sqrt (sqrt (I i).kappa)) l
      (𝓝 (sqrt (a / 2) / sqrt 2)) := by
  have hh := (hsWorstCoefficient_sqrt_spacing_tendsto hV).div
    (sqrt_spacing_sqrt_sqrt_kappa_tendsto hκ) (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  apply hh.congr
  intro i
  exact mul_div_mul_left _ _ (sqrt_pos.mpr (designSpacing_pos (I i))).ne'

/-- The source FC threshold scale is attained by the same actually
constructed half-power continuum graph. No design-limit hypothesis remains. -/
theorem exists_half_threshold_scaling :
    ∃ σ : ℝ → ℝ, 0 < σ 1 ∧
      ∀ {α : Type} {l : Filter α} {I : α → chebyshev1.SpectralInterval} {n : α → ℕ},
      Tendsto (fun i ↦ (I i).kappa) l atTop →
      Tendsto (fun i ↦ (n i : ℝ) * designSpacing (I i)) l atTop →
      Tendsto (fun i ↦ criticalTolerance (I i) (n i - 1) * sqrt (I i).kappa) l
        (𝓝 (2 / sqrt (σ 1))) := by
  obtain ⟨σ, _, hg, hl, hn⟩ := exists_sharp_recovery_graph
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hs := (hg 1 le_rfl).positive
  refine ⟨σ, hs, ?_⟩
  intro α l I n hκ hcycle
  have hv := preterminal_optimalValue_scaled_tendsto hκ hcycle
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (show 0 ≤ graphBound (1 / 2) by norm_num [graphBound]) hg hl hn
  have hf : krylov.ContinuumControl.feedbackValue (1 / 2) σ 1 = sqrt (σ 1) := by
    rw [krylov.ContinuumControl.feedbackValue_one _ _ hs]
    norm_num
  rw [hf] at hv
  exact criticalTolerance_sqrt_kappa_tendsto (sqrt_pos.mpr hs).ne' hκ hv

/-- The true sharp total-HS response has the printed quarter-power scale
on every simultaneous growing cycle, for a positive constructed continuum
constant. No desired asymptotic is supplied as an input. -/
theorem exists_hs_quarter_scaling :
    ∃ a : ℝ, 0 < a ∧
      ∀ {α : Type} {l : Filter α} {I : α → chebyshev1.SpectralInterval} {n : α → ℕ},
      Tendsto (fun i ↦ (I i).kappa) l atTop →
      Tendsto (fun i ↦ (n i : ℝ) * designSpacing (I i)) l atTop →
      Tendsto (fun i ↦ hsWorstCoefficient (I i) (n i - 1) / sqrt (sqrt (I i).kappa)) l
        (𝓝 (sqrt (a / 2) / sqrt 2)) := by
  obtain ⟨σ, _, hg, hl, hn⟩ := exists_sharp_recovery_graph
    (by norm_num : (0 : ℝ) < 1) le_rfl
  have hf := krylov.ContinuumControl.feedbackValue_pos (by norm_num : (0 : ℝ) < 1)
    le_rfl (hg 1 le_rfl).positive
  refine ⟨_, hf, ?_⟩
  intro α l I n hκ hcycle
  exact hsWorstCoefficient_quarter_kappa_tendsto hκ
    (preterminal_optimalValue_scaled_tendsto hκ hcycle (by norm_num : (0 : ℝ) < 1) le_rfl
      (by norm_num [graphBound] : 0 ≤ graphBound 1) hg hl hn)

end
end krylov.Cost
