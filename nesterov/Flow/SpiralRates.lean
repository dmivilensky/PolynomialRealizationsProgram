import nesterov.Flow.SmoothSpiral
import nesterov.Flow.Decay

/-!
Article: Theorem `flow`(c,d), exponents of the smooth spiral witnesses.
Use: all three logarithmic exponents are evaluated on actual objective
values and mechanical energies, rather than on prescribed abstract jets.
-/

noncomputable section

namespace nesterov.Flow

variable {J : Type*} [Fintype J]

theorem Spectrum.smooth_spiral_exponents (ν : Spectrum J) {θ m c : ℝ}
    {f : EuclideanSpace ℂ J → ℝ} (hf : Objective m f)
    (hvalue : ∀ t : ℝ, 0 ≤ t → f (ν.orbit c t) =
      ν.orbitValue θ m c t + m / 2 * ‖ν.orbit c t‖ ^ 2)
    (hvelocity : ∀ t : ℝ, ‖ν.velocity c t‖ = Real.exp (-c * t) * ‖ν.velocity c 0‖) :
    decayExponent (ν.orbit c) (ν.velocity c) = (c : EReal) ∧
      observableExponent (fun t => f (ν.orbit c t)) = ((2 * c : ℝ) : EReal) ∧
      observableExponent (fun t => energy f (ν.orbit c t) (ν.velocity c t)) = ((2 * c : ℝ) : EReal) := by
  have hnorm0 : ‖ν.orbit c 0‖ = 1 := by simp [ν.orbit_norm]
  have hfp : 0 < f (ν.orbit c 0) := by
    have hh := hf.quadratic_lower (ν.orbit c 0)
    rw [hnorm0] at hh
    nlinarith [hf.m_pos]
  have hval (t : ℝ) (ht : 0 ≤ t) :
      f (ν.orbit c t) = f (ν.orbit c 0) * Real.exp (-(2 * c) * t) := by
    rw [hvalue t ht, hvalue 0 le_rfl]
    dsimp [Spectrum.orbitValue]
    rw [ν.orbit_norm_sq, ν.orbit_norm_sq]
    simp only [mul_zero, Real.exp_zero, one_mul]
    have he : -2 * c * t = -(2 * c) * t := by ring
    rw [he]
    ring
  refine ⟨?_, observableExponent_exact_exp hfp hval, ?_⟩
  · apply observableExponent_exact_exp (show 0 < 1 + ‖ν.velocity c 0‖ by positivity)
    intro t _
    rw [ν.orbit_norm, hvelocity]
    ring
  · have henergy : 0 < energy f (ν.orbit c 0) (ν.velocity c 0) := by
      dsimp [energy]
      positivity
    apply observableExponent_exact_exp henergy
    intro t ht
    dsimp [energy]
    rw [hval t ht, hvelocity t, mul_pow]
    have he : Real.exp (-c * t) ^ 2 = Real.exp (-(2 * c) * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring

/-- The strict program realizes all three sharp exponents with a finite
global smoothness constant on the same finite-dimensional objective. -/
theorem Spectrum.exists_smooth_spiral_with_exponents (ν : Spectrum J) {θ m c ε : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hct : c ≤ θ / 2) (h : ν.StrictProgram θ m c ε) :
    ∃ (L : ℝ) (f : EuclideanSpace ℂ J → ℝ), m < L ∧
      polyak.CenteredSmoothStronglyConvex m L f ∧ IsSolution θ f (ν.orbit c) (ν.velocity c) ∧
      decayExponent (ν.orbit c) (ν.velocity c) = (c : EReal) ∧
      observableExponent (fun t => f (ν.orbit c t)) = ((2 * c : ℝ) : EReal) ∧
      observableExponent (fun t => energy f (ν.orbit c t) (ν.velocity c t)) = ((2 * c : ℝ) : EReal) := by
  obtain ⟨L, f, hL, hf, hsol, hvalues, _, hvelocity⟩ := ν.exists_smooth_spiral hm hc hct h
  obtain ⟨hstate, hvalue, henergy⟩ := ν.smooth_spiral_exponents
    (of_centeredSmoothStronglyConvex hf) hvalues hvelocity
  exact ⟨L, f, hL, hf, hsol, hstate, hvalue, henergy⟩

end nesterov.Flow
