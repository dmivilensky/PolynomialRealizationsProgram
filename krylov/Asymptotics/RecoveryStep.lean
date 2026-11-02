import krylov.Asymptotics.RecoveryString
import krylov.Asymptotics.EulerStability

/-!
Article: main_krylov, lower bound in thm:limit.
Use: the actual split drift/impulse map is uniformly stable with a
`1+O(h)` factor. The recovery string's true position/slope is exactly its
constructed nonautonomous evolution.
Source: the product maximum norm, triangle inequality and exact recurrence.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Set

/-- One true split step: first drift by `h*a`, then impulse by `h*b`. -/
def driftImpulseStep (h a b : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  let φ := z.1 + h * a * z.2
  (φ, z.2 + h * b * φ)

/-- The true split step has a uniform first-order Lipschitz factor whenever
the density and reciprocal midpoint density are bounded. -/
theorem driftImpulseStep_stable {h a b V : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haV : a ≤ V) (hbV : b ≤ V)
    (z w : ℝ × ℝ) :
    ‖driftImpulseStep h a b z - driftImpulseStep h a b w‖ ≤
      (1 + (V + V ^ 2) * h) * ‖z - w‖ := by
  have hV : 0 ≤ V := ha.trans haV
  let D := ‖z - w‖
  have hD : 0 ≤ D := norm_nonneg _
  have h₁ : |z.1 - w.1| ≤ D := by
    simpa only [D, Real.norm_eq_abs, Prod.fst_sub] using norm_fst_le (z - w)
  have h₂ : |z.2 - w.2| ≤ D := by
    simpa only [D, Real.norm_eq_abs, Prod.snd_sub] using norm_snd_le (z - w)
  have hha : 0 ≤ h * a := mul_nonneg hh ha
  have hhb : 0 ≤ h * b := mul_nonneg hh hb
  have hφ : |(z.1 + h * a * z.2) - (w.1 + h * a * w.2)| ≤ (1 + h * V) * D := by
    calc
      _ = |(z.1 - w.1) + h * a * (z.2 - w.2)| := by congr 1; ring
      _ ≤ |z.1 - w.1| + |h * a * (z.2 - w.2)| := abs_add_le _ _
      _ = |z.1 - w.1| + h * a * |z.2 - w.2| := by rw [abs_mul, abs_of_nonneg hha]
      _ ≤ D + h * V * D := by gcongr
      _ = (1 + h * V) * D := by ring
  have hp : |(z.2 + h * b * (z.1 + h * a * z.2)) -
      (w.2 + h * b * (w.1 + h * a * w.2))| ≤ D + h * V * ((1 + h * V) * D) := by
    calc
      _ = |(z.2 - w.2) + h * b * ((z.1 + h * a * z.2) - (w.1 + h * a * w.2))| := by congr 1; ring
      _ ≤ |z.2 - w.2| + |h * b * ((z.1 + h * a * z.2) - (w.1 + h * a * w.2))| := abs_add_le _ _
      _ = |z.2 - w.2| + h * b * |(z.1 + h * a * z.2) - (w.1 + h * a * w.2)| := by
        rw [abs_mul, abs_of_nonneg hhb]
      _ ≤ D + h * V * ((1 + h * V) * D) := by gcongr
  have hhSq : h * h ≤ h := by nlinarith
  have hterm := mul_le_mul_of_nonneg_right hhSq (mul_nonneg (sq_nonneg V) hD)
  change max |(z.1 + h * a * z.2) - (w.1 + h * a * w.2)|
    |(z.2 + h * b * (z.1 + h * a * z.2)) - (w.2 + h * b * (w.1 + h * a * w.2))| ≤ _
  apply max_le
  · nlinarith [mul_nonneg (mul_nonneg (sq_nonneg V) hh) hD]
  · nlinarith only [hp, hterm]

/-- The density-sampled step used by the genuine recovery string. -/
def recoveryStep (v : ℝ → ℝ) (h : ℝ) (j : ℕ) : (ℝ × ℝ) → ℝ × ℝ :=
  driftImpulseStep h (v (((j : ℝ) + 1 / 2) * h))⁻¹ (v (((j : ℝ) + 1) * h))

/-- The constructed recovery string has exactly the split evolution used in
its numerical consistency proof. -/
theorem recoveryString_pair_evolution (v : ℝ → ℝ) {Y h : ℝ} (hh : 0 < h) (N : ℕ)
    (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y) (j : ℕ) :
    let S := recoveryString v hh N hNY hv
    (S.φ j, S.p j) = evolution (recoveryStep v h) (1, 1) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [evolution]
    rw [← ih]
    dsimp [recoveryStep, driftImpulseStep]
    apply Prod.ext
    · rw [recoveryString_position_step]
      simp only [div_eq_mul_inv]
    · rw [recoveryString_slope_step, recoveryString_position_step]
      simp only [div_eq_mul_inv]

end
end krylov.Asymptotics
