import krylov.Asymptotics.RecoveryTypeClock
import krylov.Asymptotics.RecoveryReward
import krylov.ContinuumControl.SmoothIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: main_krylov, thm:limit, continuum recovery state in type time.
Use: construct actual C¹ type-time data by inverting a positive physical
density and composing the genuine physical string state. The type reward is
proved equal to the physical reward by change of variables.
Source: the ordinary chain rule, FTC and mathlib's interval substitution.
-/
namespace krylov.Asymptotics
noncomputable section
open Set Real MeasureTheory
open krylov.ContinuumControl

/-- Compact type-time state data. In this file these are constructed from
the actual physical string, rather than postulated for a recovery sequence. -/
structure RecoveryState (Y : ℝ) where
  density : ℝ → ℝ
  position : ℝ → ℝ
  slope : ℝ → ℝ
  energy : ℝ → ℝ
  density_pos : ∀ y ∈ Icc 0 Y, 0 < density y
  density_C1 : ContDiffOn ℝ 1 density (Icc 0 Y)
  position_C1 : ContDiffOn ℝ 1 position (Icc 0 Y)
  slope_C1 : ContDiffOn ℝ 1 slope (Icc 0 Y)
  energy_C1 : ContDiffOn ℝ 1 energy (Icc 0 Y)
  energy_one_le : ∀ y ∈ Icc 0 Y, 1 ≤ energy y
  position_zero : position 0 = 1
  slope_zero : slope 0 = 1
  energy_zero : energy 0 = 1
  position_derivative : ∀ y ∈ Icc 0 Y,
    HasDerivWithinAt position ((density y)⁻¹ * slope y) (Icc 0 Y) y
  slope_derivative : ∀ y ∈ Icc 0 Y,
    HasDerivWithinAt slope (density y * position y) (Icc 0 Y) y
  energy_derivative : ∀ y ∈ Icc 0 Y,
    HasDerivWithinAt energy (density y * position y ^ 2) (Icc 0 Y) y

theorem recoveryTypeInverse_clock {v : ℝ → ℝ} {X x : ℝ}
    (hc : Continuous v) (hv : ∀ x, 0 < v x) (hx : x ∈ Icc 0 X) :
    recoveryTypeInverse v X (recoveryTypeClock v x) = x := by
  exact krylov.Strings.TypeChange.inverse_clock
    ((recoveryTypeClock_strictMono hc hv).strictMonoOn _)
    (show x ∈ Icc (-1) (X + 1) from ⟨by linarith [hx.1], by linarith [hx.2]⟩)

/-- The actual physical-to-type construction, including both endpoint
equations and compact C¹ regularity of every coordinate. -/
def physicalRecoveryState {v φ p K : ℝ → ℝ} {X : ℝ} (hX : 0 < X)
    (hcv : Continuous v) (hpos : ∀ x, 0 < v x)
    (hvC1 : ContDiffOn ℝ 1 v (Ici 0))
    (hcφ : Continuous φ) (hcp : Continuous p) (hcK : Continuous K)
    (hφ₀ : φ 0 = 1) (hp₀ : p 0 = 1) (hK₀ : K 0 = 1)
    (hode : ∀ x ≥ 0, SmoothStringAt φ p K v x) : RecoveryState (recoveryTypeClock v X) := by
  have hφC1 : ContDiffOn ℝ 1 φ (Icc 0 X) :=
    contDiffOn_one_of_continuous_derivative (uniqueDiffOn_Icc hX)
      (fun x hx ↦ (hode x hx.1).φ_deriv.hasDerivWithinAt) hcp.continuousOn
  have hpC1 : ContDiffOn ℝ 1 p (Icc 0 X) :=
    contDiffOn_one_of_continuous_derivative (uniqueDiffOn_Icc hX)
      (fun x hx ↦ (hode x hx.1).p_deriv.hasDerivWithinAt) (hcφ.mul (hcv.pow 2)).continuousOn
  have hKC1 : ContDiffOn ℝ 1 K (Icc 0 X) :=
    contDiffOn_one_of_continuous_derivative (uniqueDiffOn_Icc hX)
      (fun x hx ↦ (hode x hx.1).K_deriv.hasDerivWithinAt) ((hcφ.pow 2).mul (hcv.pow 2)).continuousOn
  have hKmono : MonotoneOn K (Icc 0 X) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 X) hcK.continuousOn
      (fun x hx ↦ (hode x (interior_subset hx).1).K_deriv.hasDerivWithinAt)
      (fun _ _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
  refine ⟨recoveryTypePullback v X v, recoveryTypePullback v X φ,
    recoveryTypePullback v X p, recoveryTypePullback v X K,
    fun y _hy ↦ hpos _,
    recoveryTypePullback_contDiffOn hcv hpos hX (hvC1.mono (fun _ hx ↦ hx.1)),
    recoveryTypePullback_contDiffOn hcv hpos hX hφC1,
    recoveryTypePullback_contDiffOn hcv hpos hX hpC1,
    recoveryTypePullback_contDiffOn hcv hpos hX hKC1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hh := hKmono (show (0 : ℝ) ∈ Icc 0 X from ⟨le_rfl, hX.le⟩)
      (recoveryTypeInverse_mem hcv hpos hX hy) (recoveryTypeInverse_mem hcv hpos hX hy).1
    simpa only [hK₀, recoveryTypePullback] using hh
  · simpa only [recoveryTypePullback, recoveryTypeInverse_zero hcv hpos hX] using hφ₀
  · simpa only [recoveryTypePullback, recoveryTypeInverse_zero hcv hpos hX] using hp₀
  · simpa only [recoveryTypePullback, recoveryTypeInverse_zero hcv hpos hX] using hK₀
  · intro y hy
    have hx := recoveryTypeInverse_mem hcv hpos hX hy
    convert ((hode _ hx.1).φ_deriv.comp y (recoveryTypeInverse_derivative hcv hpos hX hy)).hasDerivWithinAt using 1
    · rfl
    · dsimp [recoveryTypePullback]; ring
  · intro y hy
    have hx := recoveryTypeInverse_mem hcv hpos hX hy
    convert ((hode _ hx.1).p_deriv.comp y (recoveryTypeInverse_derivative hcv hpos hX hy)).hasDerivWithinAt using 1
    · rfl
    · dsimp [recoveryTypePullback]; field_simp [(hpos _).ne']
  · intro y hy
    have hx := recoveryTypeInverse_mem hcv hpos hX hy
    convert ((hode _ hx.1).K_deriv.comp y (recoveryTypeInverse_derivative hcv hpos hX hy)).hasDerivWithinAt using 1
    · rfl
    · dsimp [recoveryTypePullback]; field_simp [(hpos _).ne']

/-- The reward of this actual type state equals the true physical reward;
this is a change of variables, not a formal identification of derivatives. -/
theorem physicalRecoveryState_reward {v φ p K : ℝ → ℝ} {X γ : ℝ} (hX : 0 < X)
    (hcv : Continuous v) (hpos : ∀ x, 0 < v x)
    (hvC1 : ContDiffOn ℝ 1 v (Ici 0))
    (hcφ : Continuous φ) (hcp : Continuous p) (hcK : Continuous K)
    (hφ₀ : φ 0 = 1) (hp₀ : p 0 = 1) (hK₀ : K 0 = 1)
    (hode : ∀ x ≥ 0, SmoothStringAt φ p K v x) :
    let R := physicalRecoveryState hX hcv hpos hvC1 hcφ hcp hcK hφ₀ hp₀ hK₀ hode
    (∫ y in 0..recoveryTypeClock v X, R.energy y ^ (-γ)) = ∫ x in 0..X, K x ^ (-γ) * v x := by
  let R := physicalRecoveryState hX hcv hpos hvC1 hcφ hcp hcK hφ₀ hp₀ hK₀ hode
  have hg : ContinuousOn (fun y ↦ R.energy y ^ (-γ)) (Icc 0 (recoveryTypeClock v X)) :=
    R.energy_C1.continuousOn.rpow_const (fun y hy ↦ Or.inl (by have := R.energy_one_le y hy; linarith))
  have himage : recoveryTypeClock v '' uIcc 0 X ⊆ Icc 0 (recoveryTypeClock v X) := by
    rintro y ⟨x, hx, rfl⟩
    rw [uIcc_of_le hX.le] at hx
    constructor
    · simpa only [recoveryTypeClock_zero] using (recoveryTypeClock_strictMono hcv hpos).monotone hx.1
    · exact (recoveryTypeClock_strictMono hcv hpos).monotone hx.2
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (fun x (_hx : x ∈ uIcc 0 X) ↦ recoveryTypeClock_derivative hcv x)
    hcv.continuousOn (hg.mono himage)
  rw [recoveryTypeClock_zero] at hsub
  change (∫ y in 0..recoveryTypeClock v X, R.energy y ^ (-γ)) = _
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc 0 X := by simpa only [uIcc_of_le hX.le] using hx
  dsimp [R, physicalRecoveryState, recoveryTypePullback, Function.comp_def]
  rw [recoveryTypeInverse_clock hcv hpos hx']

end
end krylov.Asymptotics
