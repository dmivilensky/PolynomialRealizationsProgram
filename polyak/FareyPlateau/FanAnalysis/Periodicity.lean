import polyak.FareyPlateau.FanAnalysis.Constraint
import polyak.FareyPlateau.Fan.Geometry
import Mathlib.Algebra.Order.ToIntervalMod

/-! Exact phase-circle reduction for the full fan constraint. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Set

theorem constraint_periodic (k : ℕ) (z : ℝ) (a c : ℝ → ℝ) (δ θ : ℝ) (l : ℤ) :
    constraint ((k : ℝ) - 1) z a c δ (θ + l * (2 * Real.pi)) =
      constraint ((k : ℝ) - 1) z a c δ θ := by
  unfold constraint
  have hnear : θ + l * (2 * Real.pi) - a δ = (θ - a δ) + l * (2 * Real.pi) := by ring
  have hfar : ((k : ℝ) - 1) * (θ + l * (2 * Real.pi)) + c δ =
      (((k : ℝ) - 1) * θ + c δ) + (((k : ℤ) - 1) * l : ℤ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [hnear, hfar, Real.cos_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]

theorem phase_representative (θ : ℝ) :
    ∃ x ∈ Icc (-Real.pi) Real.pi, ∃ l : ℤ, θ = x + l * (2 * Real.pi) := by
  let x := toIcoMod (by positivity : 0 < 2 * Real.pi) (-Real.pi) θ
  have hx := toIcoMod_mem_Ico (by positivity : 0 < 2 * Real.pi) (-Real.pi) θ
  have he := toIcoMod_add_toIcoDiv_zsmul (by positivity : 0 < 2 * Real.pi) (-Real.pi) θ
  refine ⟨x, ⟨hx.1, by linarith [hx.2]⟩, toIcoDiv (by positivity : 0 < 2 * Real.pi) (-Real.pi) θ, ?_⟩
  simpa only [zsmul_eq_mul] using he.symm

theorem companion_cosine (P : Fan.Data) (n : ℤ) (c : ℝ) :
    Real.cos ((n : ℝ) * P.far - c) =
      Real.cos (((P.k : ℝ) - 1) * ((n : ℝ) * P.near) + c) := by
  have he : (n : ℝ) * P.far - c =
      -(((P.k : ℝ) - 1) * ((n : ℝ) * P.near) + c) +
        ((n * P.j : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    linear_combination (n : ℝ) * P.resonance
  rw [he, Real.cos_add_int_mul_two_pi, Real.cos_neg]

end polyak.FareyPlateau.FanAnalysis
