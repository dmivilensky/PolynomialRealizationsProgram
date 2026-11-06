import nesterov.Flow.Damping
import nesterov.Flow.Model

/-!
Article: §3 and Appendix B, the quadratic branch of the damping trade-off.
Use: retain the explicit monotonicity and rationalized formula stated in the
proof of Corollary `damping`, including the critically damped endpoint.
-/

namespace nesterov.Flow
noncomputable section
open scoped InnerProductSpace

theorem cQ_strictMonoOn_underdamped {m : ℝ} (hm : 0 ≤ m) :
    StrictMonoOn (fun θ : ℝ => cQ θ m) (Set.Icc 0 (2 * Real.sqrt m)) := by
  intro θ₁ hθ₁ θ₂ hθ₂ hlt
  change cQ θ₁ m < cQ θ₂ m
  rw [cQ_eq_half (by nlinarith [hθ₁.1, hθ₁.2, Real.sq_sqrt hm, Real.sqrt_nonneg m]),
    cQ_eq_half (by nlinarith [hθ₂.1, hθ₂.2, Real.sq_sqrt hm, Real.sqrt_nonneg m])]
  linarith

theorem cQ_strictAntiOn_overdamped {m : ℝ} (hm : 0 < m) :
    StrictAntiOn (fun θ : ℝ => cQ θ m) (Set.Ici (2 * Real.sqrt m)) := by
  intro θ₁ hθ₁ θ₂ hθ₂ hlt
  change 2 * Real.sqrt m ≤ θ₁ at hθ₁
  change 2 * Real.sqrt m ≤ θ₂ at hθ₂
  have hs := Real.sq_sqrt hm.le
  have hsp := Real.sqrt_pos.mpr hm
  have hθ₁pos : 0 < θ₁ := by linarith [hθ₁]
  have hθ₂pos : 0 < θ₂ := by linarith
  have hroot₁ := delta_cQ_eq_zero (θ := θ₁) (m := m) (by nlinarith [hθ₁])
  have hroot₂ := delta_cQ_eq_zero (θ := θ₂) (m := m) (by nlinarith [hθ₂])
  have hq₂pos := cQ_pos hθ₂pos hm
  have hq₁bound := cQ_le_sqrt hθ₁pos hm
  have hq₂bound := cQ_le_sqrt hθ₂pos hm
  by_contra hh
  have hle : cQ θ₁ m ≤ cQ θ₂ m := le_of_not_gt hh
  have hprod : (cQ θ₂ m - cQ θ₁ m) * (cQ θ₁ m + cQ θ₂ m - θ₁) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [hθ₁])
  have hpos : 0 < (θ₂ - θ₁) * cQ θ₂ m := mul_pos (sub_pos.mpr hlt) hq₂pos
  dsimp [delta] at hroot₁ hroot₂
  nlinarith only [hroot₁, hroot₂, hprod, hpos]

theorem cQ_antitoneOn_overdamped {m : ℝ} (hm : 0 < m) :
    AntitoneOn (fun θ : ℝ => cQ θ m) (Set.Ici (2 * Real.sqrt m)) :=
  (cQ_strictAntiOn_overdamped hm).antitoneOn

theorem cQ_overdamped_formula {θ m : ℝ} (hm : 0 ≤ m)
    (hθ : 2 * Real.sqrt m ≤ θ) :
    cQ θ m = (θ - Real.sqrt (θ ^ 2 - 4 * m)) / 2 := by
  have hs := Real.sq_sqrt hm
  have hsn := Real.sqrt_nonneg m
  unfold cQ
  split_ifs with h
  · have he : θ ^ 2 - 4 * m = 0 := by nlinarith
    rw [he, Real.sqrt_zero, sub_zero]
  · rfl

theorem cQ_reciprocal_formula {θ m : ℝ} (hm : 0 < m)
    (hθ : 2 * Real.sqrt m ≤ θ) :
    cQ θ m = 2 * m / (θ + Real.sqrt (θ ^ 2 - 4 * m)) := by
  have hs := Real.sq_sqrt hm.le
  have hsp := Real.sqrt_pos.mpr hm
  have hsn := Real.sqrt_nonneg (θ ^ 2 - 4 * m)
  have hd : 0 ≤ θ ^ 2 - 4 * m := by nlinarith
  have hsd := Real.sq_sqrt hd
  have hden : θ + Real.sqrt (θ ^ 2 - 4 * m) ≠ 0 := by linarith
  rw [cQ_overdamped_formula hm.le hθ]
  apply (eq_div_iff hden).mpr
  nlinarith

/-- The precise nonlinear constant at critical quadratic damping. -/
theorem cF_critical {m : ℝ} (hm : 0 < m) :
    cF (2 * Real.sqrt m) m = 2 * Real.sqrt m / 3 :=
  cF_eq_third_of_damping_le_optimal (by positivity) hm (critical_le_nonlinear_optimal hm.le)

/-- Convexity excludes an effective homogeneous degree below one wherever
the convex remainder is strictly positive. -/
theorem homogeneous_degree_ge_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {m : ℝ} {f : E → ℝ}
    (hf : Objective m f) (x : E) {r : ℝ}
    (hpos : 0 < remainder m f x)
    (heuler : ⟪remainderGradient m f x, x⟫_ℝ = r * remainder m f x) : 1 ≤ r := by
  have hh := hf.remainder_support_nonneg x
  rw [heuler] at hh
  nlinarith

theorem nonlinear_optimal_rate_ratio {m : ℝ} (hm : 0 < m) :
    Real.sqrt (m / 2) / Real.sqrt m = 1 / Real.sqrt 2 := by
  rw [Real.sqrt_div hm.le]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hm)]

theorem nonlinear_optimal_damping_ratio {m : ℝ} (hm : 0 < m) :
    (3 * Real.sqrt (m / 2)) / (2 * Real.sqrt m) = 3 / (2 * Real.sqrt 2) := by
  rw [Real.sqrt_div hm.le]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hm)]

end
end nesterov.Flow
