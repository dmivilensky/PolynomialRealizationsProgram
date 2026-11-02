import krylov.Asymptotics.RecoveryStep
import krylov.Asymptotics.TaylorIncrement

/-!
Article: main_krylov, lower bound in thm:limit, quadratic local defect.
Use: prove consistency of the actual drift/impulse map from real Taylor
increment bounds and real coefficient variation bounds. The density samples
are at the printed midpoint/right endpoint; the second update uses the
already drifted position.
Source: the triangle inequality and the proved Taylor increment estimate.
-/
namespace krylov.Asymptotics
noncomputable section
open Real

/-- A quadratic local error for the actual split step. All hypotheses are
bounds on the genuine reference increments and density samples; the desired
split-step defect is derived. -/
theorem driftImpulseStep_defect {h a₀ b₀ a b φ p φ₁ p₁ V M L D : ℝ}
    (hh : 0 ≤ h) (hV : 0 ≤ V) (hM : 0 ≤ M) (hL : 0 ≤ L) (_hD : 0 ≤ D)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haV : a ≤ V) (hbV : b ≤ V)
    (hφ : |φ| ≤ M) (hp : |p| ≤ M)
    (haLip : |a - a₀| ≤ L * h) (hbLip : |b - b₀| ≤ L * h)
    (hφinc : |φ₁ - φ - h * a₀ * p| ≤ D * h ^ 2)
    (hpinc : |p₁ - p - h * b₀ * φ| ≤ D * h ^ 2) :
    ‖driftImpulseStep h a b (φ, p) - (φ₁, p₁)‖ ≤
      ((L + V ^ 2) * M + D) * h ^ 2 := by
  have hφerr : |(φ + h * a * p) - φ₁| ≤ (L * M + D) * h ^ 2 := by
    calc
      _ = |h * (a - a₀) * p - (φ₁ - φ - h * a₀ * p)| := by congr 1; ring
      _ ≤ |h * (a - a₀) * p| + |φ₁ - φ - h * a₀ * p| := by simpa only [Real.norm_eq_abs] using norm_sub_le (h * (a - a₀) * p) (φ₁ - φ - h * a₀ * p)
      _ ≤ L * M * h ^ 2 + D * h ^ 2 := by
        apply add_le_add _ hφinc
        rw [abs_mul, abs_mul, abs_of_nonneg hh]
        calc
          h * |a - a₀| * |p| ≤ h * (L * h) * M := by gcongr
          _ = L * M * h ^ 2 := by ring
      _ = (L * M + D) * h ^ 2 := by ring
  have hperr : |(p + h * b * (φ + h * a * p)) - p₁| ≤ ((L + V ^ 2) * M + D) * h ^ 2 := by
    calc
      _ = |h * (b - b₀) * φ + h ^ 2 * b * a * p - (p₁ - p - h * b₀ * φ)| := by congr 1; ring
      _ ≤ |h * (b - b₀) * φ + h ^ 2 * b * a * p| + |p₁ - p - h * b₀ * φ| := by simpa only [Real.norm_eq_abs] using norm_sub_le (h * (b - b₀) * φ + h ^ 2 * b * a * p) (p₁ - p - h * b₀ * φ)
      _ ≤ (|h * (b - b₀) * φ| + |h ^ 2 * b * a * p|) + |p₁ - p - h * b₀ * φ| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (L * M * h ^ 2 + V ^ 2 * M * h ^ 2) + D * h ^ 2 := by
        apply add_le_add _ hpinc
        apply add_le_add
        · rw [abs_mul, abs_mul, abs_of_nonneg hh]
          calc
            h * |b - b₀| * |φ| ≤ h * (L * h) * M := by gcongr
            _ = L * M * h ^ 2 := by ring
        · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg h),
            abs_of_nonneg ha, abs_of_nonneg hb]
          calc
            h ^ 2 * b * a * |p| ≤ h ^ 2 * V * V * M := by gcongr
            _ = V ^ 2 * M * h ^ 2 := by ring
      _ = ((L + V ^ 2) * M + D) * h ^ 2 := by ring
  change max |(φ + h * a * p) - φ₁| |(p + h * b * (φ + h * a * p)) - p₁| ≤ _
  apply max_le _ hperr
  exact hφerr.trans (by nlinarith [mul_nonneg (mul_nonneg (sq_nonneg V) hM) (sq_nonneg h)])

end
end krylov.Asymptotics
