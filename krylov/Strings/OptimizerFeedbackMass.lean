import krylov.Strings.OptimizerDensityMass
import krylov.Strings.FeedbackSmoothBridge
import krylov.Strings.FeedbackInitialDensity

/-!
Article: main_krylov, thm:value, actual local feedback string construction.
Use: turn a generated Picard–Lindelöf feedback trajectory into an actual
Stieltjes mass, its mass-integral state and its genuine Radon–Nikodym type clock.
Source: existing positive feedback existence, compact continuous extension and
the proved continuous-density mass/RN bridge. No feedback trajectory or mass
state is assumed as a field of an optimizer object.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- The generated feedback ODE is an actual local physical string, including
the measure, all state integrals and the RN-defined type clock. The only graph
hypotheses are C¹ regularity and positivity at the initial crossing; global
orbit existence and global optimality are separate obligations.
-/
theorem optimizer_exists_local_mass {σ : ℝ → ℝ}
    (hσ : ContDiffAt ℝ 1 σ 1) (hσpos : 0 < σ 1) :
    ∃ L : ℝ≥0, 0 < L ∧ ∃ α : ℝ → FeedbackState, ∃ M : Mass,
      α 0 = (1, 1, 1) ∧
      HasDerivWithinAt M.cumulative (σ 1)⁻¹ (Ici 0) 0 ∧
      (M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] feedbackCurveDensity σ α) ∧
      ∀ x ∈ Icc 0 (L : ℝ),
        krylov.ContinuumControl.SmoothStringAt
          (fun u ↦ (α u).1) (fun u ↦ (α u).2.1) (fun u ↦ (α u).2.2)
          (feedbackCurveDensity σ α) x ∧
        M.cumulative x = 1 + ∫ t in (0 : ℝ)..x, feedbackCurveDensity σ α t ^ 2 ∧
        (α x).1 = 1 + ∫ t in Ioc 0 x, (α t).2.1 ∧
        (α x).2.1 = integralSlope M.measure (fun u ↦ (α u).1) x ∧
        (α x).2.2 = integralEnergy M.measure (fun u ↦ (α u).1) x ∧
        M.typeClock x = ∫ t in (0 : ℝ)..x, feedbackCurveDensity σ α t := by
  obtain ⟨α, hα₀, ε, hε, hd⟩ := feedback_local_positive_solution hσ hσpos
  have hcα₀ := (hd 0 (by constructor <;> linarith)).1.continuousAt
  have hK₀ : (α 0).2.2 ≠ 0 := by simp [hα₀]
  have hratio₀ : ContinuousAt
      (fun x ↦ stateRatio (α x).1 (α x).2.1 (α x).2.2) 0 := by
    dsimp [stateRatio]
    fun_prop
  have hnearσ : ∀ᶠ x in 𝓝 (0 : ℝ),
      ContDiffAt ℝ 1 σ (stateRatio (α x).1 (α x).2.1 (α x).2.2) := by
    apply hratio₀.tendsto.eventually
    simpa only [hα₀, stateRatio, one_mul, div_one] using hσ.eventually (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnearσ
  let L : ℝ≥0 := ⟨min ε δ / 2, by positivity⟩
  have hL : 0 < (L : ℝ) := by change 0 < min ε δ / 2; positivity
  have hLe : (L : ℝ) < ε := by
    change min ε δ / 2 < ε
    linarith [min_le_left ε δ, lt_min hε hδ]
  have hLd : (L : ℝ) < δ := by
    change min ε δ / 2 < δ
    linarith [min_le_right ε δ, lt_min hε hδ]
  have hxe {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) : x ∈ Ioo (-ε) ε :=
    ⟨by linarith [hx.1], hx.2.trans_lt hLe⟩
  have hσx {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) :
      ContDiffAt ℝ 1 σ (stateRatio (α x).1 (α x).2.1 (α x).2.2) := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    exact hx.2.trans_lt hLd
  have hvcont : ContinuousOn (feedbackCurveDensity σ α) (Icc 0 (L : ℝ)) := by
    intro x hx
    obtain ⟨hode, hφ, hp, hK, hs⟩ := hd x (hxe hx)
    have hαc := hode.continuousAt
    have hφn := hφ.ne'
    have hKn := hK.ne'
    have hr : ContinuousAt
        (fun u ↦ stateRatio (α u).1 (α u).2.1 (α u).2.2) x := by
      dsimp [stateRatio]
      fun_prop
    have hsg : ContinuousAt
        (fun u ↦ σ (stateRatio (α u).1 (α u).2.1 (α u).2.2)) x :=
      (hσx hx).continuousAt.tendsto.comp hr.tendsto
    have ht : Real.sqrt (σ (stateRatio (α x).1 (α x).2.1 (α x).2.2)) ≠ 0 :=
      (Real.sqrt_pos.mpr hs).ne'
    have hden := mul_ne_zero hφn ht
    apply ContinuousAt.continuousWithinAt
    unfold feedbackCurveDensity feedbackDensity
    fun_prop
  let vc : C(Window L, ℝ) := ⟨fun x ↦ feedbackCurveDensity σ α x,
    hvcont.comp_continuous continuous_subtype_val (fun x ↦ x.property)⟩
  let v : ℝ → ℝ := IccExtend L.property vc
  have hvc : Continuous v := vc.continuous.Icc_extend'
  have hveq : EqOn v (feedbackCurveDensity σ α) (Icc 0 (L : ℝ)) := by
    intro x hx
    exact IccExtend_of_mem L.property vc hx
  have hvpos : ∀ x ∈ Icc 0 (L : ℝ), 0 < v x := by
    intro x hx
    rw [hveq hx]
    obtain ⟨_, hφ, hp, _, hs⟩ := hd x (hxe hx)
    exact feedbackDensity_pos hφ hp (Real.sqrt_pos.mpr hs)
  have hsmooth : ∀ x ∈ Icc 0 (L : ℝ), krylov.ContinuumControl.SmoothStringAt
      (fun u ↦ (α u).1) (fun u ↦ (α u).2.1) (fun u ↦ (α u).2.2) v x := by
    intro x hx
    obtain ⟨hode, hφ, hp, hK, hs⟩ := hd x (hxe hx)
    have h := feedback_solution_smoothStringAt hode hφ hp hK hs
    refine ⟨h.φ_pos, h.p_pos, h.K_pos, h.φ_deriv, ?_, ?_⟩
    · simpa only [hveq hx] using h.p_deriv
    · simpa only [hveq hx] using h.K_deriv
  let M := OptimizerDensity.mass v hvc L
  have hv₀ : v 0 ^ 2 = (σ 1)⁻¹ := by
    rw [hveq ⟨le_rfl, L.property⟩]
    simpa only [feedbackCurveDensity, hα₀, stateRatio, one_mul, div_one] using
      feedback_initial_mass_density hσpos
  have hMder : HasDerivWithinAt M.cumulative (σ 1)⁻¹ (Ici 0) 0 := by
    rw [← hv₀]
    exact OptimizerDensity.cumulative_right_derivative v hvc L hL
  have htype : M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] feedbackCurveDensity σ α := by
    filter_upwards [OptimizerDensity.typeDensity_eq_abs_ae v hvc L,
      ae_restrict_mem measurableSet_Ioc] with x hx hxm
    have hxclosed : x ∈ Icc 0 (L : ℝ) := ⟨hxm.1.le, hxm.2⟩
    exact hx.trans ((abs_of_pos (hvpos x hxclosed)).trans (hveq hxclosed))
  refine ⟨L, hL, α, M, hα₀, hMder, htype, ?_⟩
  intro x hx
  have hφ₀ : (α 0).1 = 1 := by simp [hα₀]
  have hp₀ : (α 0).2.1 = 1 := by simp [hα₀]
  have hK₀' : (α 0).2.2 = 1 := by simp [hα₀]
  obtain ⟨hφeq, hpeq, hKeq⟩ := OptimizerDensity.state_integral_equations v hvc L
    hφ₀ hp₀ hK₀' hsmooth hx
  obtain ⟨hode, hφ, hp, hK, hs⟩ := hd x (hxe hx)
  refine ⟨feedback_solution_smoothStringAt hode hφ hp hK hs, ?_, hφeq, hpeq, hKeq, ?_⟩
  · rw [OptimizerDensity.cumulative_eq v hvc L hx]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    change v t ^ 2 = feedbackCurveDensity σ α t ^ 2
    rw [hveq ⟨ht.1, ht.2.trans hx.2⟩]
  · rw [OptimizerDensity.typeClock_eq_integral v hvc L (fun t ht ↦ (hvpos t ht).le) hx]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    exact hveq ⟨ht.1, ht.2.trans hx.2⟩

end
end krylov.Strings
