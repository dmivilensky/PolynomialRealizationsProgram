import nesterov.Flow.SpiralOperator
import nesterov.Flow.Model
import Mathlib.Topology.Algebra.Order.Field

/-!
Article: §3, the nearly conical profile of the mixed-spiral witnesses.
Use: identify the exact homogeneity ratio along the entire orbit and prove
both limits stated in the discussion following the interpolation program.
-/

noncomputable section

namespace nesterov.Flow

open Filter
open scoped Topology InnerProductSpace

/-- The ratio of the radial derivative of the convex remainder to its value,
as a function of the second frequency moment. -/
def profileRatio (θ m c Z : ℝ) : ℝ :=
  2 * c * (Z - delta θ m c) / ((θ - c) * Z - c * delta θ m c)

variable {J : Type*} [Fintype J]

theorem Spectrum.orbitValue_moment (ν : Spectrum J) (θ m c t : ℝ) :
    ν.orbitValue θ m c t = Real.exp (-2 * c * t) *
      (((θ - c) * (∑ j, ν.weight j * ν.frequency j ^ 2) - c * delta θ m c) / (2 * c)) := by
  unfold Spectrum.orbitValue
  congr 1
  simp only [atomValue, ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ν.weight_sum, one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem Spectrum.radialDerivative_moment (ν : Spectrum J) (θ m c t : ℝ) :
    ⟪ν.forcedGradient θ m c t, ν.orbit c t⟫_ℝ = Real.exp (-2 * c * t) *
      ((∑ j, ν.weight j * ν.frequency j ^ 2) - delta θ m c) := by
  rw [ν.minimizer_inner]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ν.weight_sum, one_mul]

/-- The radial ratio is independent of time, for the actual prescribed
gradient and remainder values of the spiral, including mixed frequencies. -/
theorem Spectrum.radialRatio_eq (ν : Spectrum J) (θ m c t : ℝ) :
    ⟪ν.forcedGradient θ m c t, ν.orbit c t⟫_ℝ / ν.orbitValue θ m c t =
      profileRatio θ m c (∑ j, ν.weight j * ν.frequency j ^ 2) := by
  rw [ν.radialDerivative_moment, ν.orbitValue_moment]
  rw [mul_div_mul_left _ _ (Real.exp_ne_zero _), div_div_eq_mul_div]
  unfold profileRatio
  ring

theorem Spectrum.secondMoment_ge_scale (ν : Spectrum J) {γ₀ : ℝ} (hγ₀ : 0 ≤ γ₀)
    (hfreq : ∀ j, γ₀ ≤ ν.frequency j) :
    γ₀ ^ 2 ≤ ∑ j, ν.weight j * ν.frequency j ^ 2 := by
  calc
    γ₀ ^ 2 = ∑ j, ν.weight j * γ₀ ^ 2 := by
      rw [← Finset.sum_mul, ν.weight_sum, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (sq_le_sq₀ hγ₀ (ν.frequency_nonneg j) |>.mpr (hfreq j))
        (ν.weight_nonneg j)

/-- As the frequency moment grows, the orbit has the effective homogeneity
degree 2c/(θ-c). -/
theorem profileRatio_tendsto {θ m c : ℝ} (hθc : c < θ) :
    Tendsto (profileRatio θ m c) atTop (𝓝 (2 * c / (θ - c))) := by
  have hzero : Tendsto (fun Z : ℝ => delta θ m c / Z) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hh : Tendsto (fun Z : ℝ => 2 * c * (1 - delta θ m c / Z) /
      (θ - c - c * (delta θ m c / Z))) atTop
      (𝓝 (2 * c * (1 - 0) / (θ - c - c * 0))) :=
    ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hzero)).div
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hzero))
    (show θ - c - c * 0 ≠ 0 by linarith : θ - c - c * (0 : ℝ) ≠ 0))
  have he : (fun Z : ℝ => 2 * c * (1 - delta θ m c / Z) /
      (θ - c - c * (delta θ m c / Z))) =ᶠ[atTop] profileRatio θ m c := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Z hZ
    unfold profileRatio
    field_simp [ne_of_gt hZ]
  simpa only [mul_zero, sub_zero, mul_one] using hh.congr' he

/-- The effective degree tends to one at the nonlinear decay ceiling. -/
theorem effectiveDegree_tendsto_one {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun c : ℝ => 2 * c / (θ - c)) (𝓝 (θ / 3)) (𝓝 1) := by
  have hh : Tendsto (fun c : ℝ => 2 * c / (θ - c)) (𝓝 (θ / 3))
      (𝓝 (2 * (θ / 3) / (θ - θ / 3))) := (tendsto_const_nhds.mul tendsto_id).div
    (tendsto_const_nhds.sub tendsto_id)
    (show θ - θ / 3 ≠ 0 by linarith : θ - θ / 3 ≠ 0)
  have he : 2 * (θ / 3) / (θ - θ / 3) = 1 :=
    (div_eq_iff (by linarith : θ - θ / 3 ≠ 0)).mpr (by ring)
  rwa [he] at hh

/-- The frequency limit applies to the literal radial ratio along the
orbits, at any selected times. -/
theorem Spectrum.radialRatio_tendsto {A : Type*} {l : Filter A}
    (ν : A → Spectrum J) (θ m c : ℝ) (hθc : c < θ) (t : A → ℝ)
    (hmoment : Tendsto (fun a => ∑ j, (ν a).weight j * (ν a).frequency j ^ 2) l atTop) :
    Tendsto (fun a => ⟪(ν a).forcedGradient θ m c (t a), (ν a).orbit c (t a)⟫_ℝ /
      (ν a).orbitValue θ m c (t a)) l (𝓝 (2 * c / (θ - c))) := by
  simpa only [Spectrum.radialRatio_eq, Function.comp_def] using
    (profileRatio_tendsto (m := m) hθc).comp hmoment

/-- Euler homogeneity makes the coefficient in the Lyapunov identity
exactly rθ-(r+2)c, as stated in the explanation of the nonlinear ceiling. -/
theorem homogeneous_dissipation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {m : ℝ} {f : H → ℝ} (_hf : Objective m f)
    (x : H) (θ c r : ℝ)
    (heuler : ⟪remainderGradient m f x, x⟫_ℝ = r * remainder m f x) :
    (θ - c) * (⟪remainderGradient m f x, x⟫_ℝ - remainder m f x) +
      (θ - 3 * c) * remainder m f x = (r * θ - (r + 2) * c) * remainder m f x := by
  rw [heuler]
  ring

end nesterov.Flow
