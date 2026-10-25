import polyak.FareyPlateau.FanAnalysis.AnglePath
import polyak.FareyPlateau.FanAnalysis.ConstraintJets

/-! The fan quadratic limits with the actual tuning phase and the literal
quadratic shift s* - e delta^2. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels ModeLocking Set Filter
open scoped Topology

namespace Actual
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

def nearAngle (e : ℝ) : ℝ → ℝ := anglePath q A.edgeShift A.frequency 1 e
def farAngle (e : ℝ) : ℝ → ℝ := anglePath q A.edgeShift A.frequency (-((k : ℝ) - 1)) e
def first : ℝ := Geometry.shiftedFirst q A.edgeShift A.frequency
def second : ℝ := Geometry.shiftedSecond q A.edgeShift A.frequency

theorem frequency_interior : (A.frequency : ℝ) ∈ Ioo 0 Real.pi :=
  ⟨Edge.atom_pos A.numerator_pos (by have := A.period_ge; omega) A.numerator_lt.le,
    Edge.atom_lt_pi (by have := A.period_ge; omega) A.numerator_lt⟩

theorem inverse_radius : 1 / (1 + (Geometry.cotangent q A.frequency + A.edgeShift)^2) =
    (Real.sin (Real.pi / k))^2 := by
  have hc := Geometry.cot_shiftedAngle q A.edgeShift (frequency_interior A)
  rw [show Geometry.shiftedAngle q A.edgeShift A.frequency = Real.pi / k from
    Edge.phase_at_shift q A.period_ge (frequency_interior A)] at hc
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
  have hs : Real.sin (Real.pi / k) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity)
      ((div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos]))).ne'
  change Real.cos (Real.pi / k) / Real.sin (Real.pi / k) = Geometry.cotangent q A.frequency + A.edgeShift at hc
  rw [← hc]
  have hn : 1 + (Real.cos (Real.pi / k) / Real.sin (Real.pi / k))^2 ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi / k)]

theorem near_analytic (e : ℝ) : AnalyticAt ℝ (nearAngle A e) 0 :=
  analyticAt_anglePath q A.edgeShift A.frequency 1 e (frequency_interior A)

theorem far_analytic (e : ℝ) : AnalyticAt ℝ (farAngle A e) 0 :=
  analyticAt_anglePath q A.edgeShift A.frequency (-((k : ℝ) - 1)) e (frequency_interior A)

theorem near_value (e : ℝ) : nearAngle A e 0 = Real.pi / k := by
  rw [nearAngle, anglePath_value q A.edgeShift A.frequency 1 e (frequency_interior A)]
  exact Edge.phase_at_shift q A.period_ge (frequency_interior A)

theorem far_value (e : ℝ) : farAngle A e 0 = Real.pi / k := by
  rw [farAngle, anglePath_value q A.edgeShift A.frequency _ e (frequency_interior A)]
  exact Edge.phase_at_shift q A.period_ge (frequency_interior A)

theorem near_first (e : ℝ) : deriv (nearAngle A e) 0 = first A := by
  simpa only [nearAngle, mul_one, first] using
    anglePath_first q A.edgeShift A.frequency 1 e (frequency_interior A)

theorem far_first (e : ℝ) : deriv (farAngle A e) 0 = -((k : ℝ) - 1) * first A := by
  rw [farAngle, anglePath_first q A.edgeShift A.frequency _ e (frequency_interior A)]
  unfold first
  ring

theorem near_second (e : ℝ) : deriv^[2] (nearAngle A e) 0 = second A + 2 * e * (Real.sin (Real.pi / k))^2 := by
  rw [nearAngle, anglePath_second q A.edgeShift A.frequency 1 e (frequency_interior A)]
  simp only [one_pow, mul_one]
  rw [div_eq_mul_inv, ← one_div, inverse_radius A]
  rfl

theorem far_second (e : ℝ) : deriv^[2] (farAngle A e) 0 =
    ((k : ℝ) - 1)^2 * second A + 2 * e * (Real.sin (Real.pi / k))^2 := by
  rw [farAngle, anglePath_second q A.edgeShift A.frequency _ e (frequency_interior A),
    neg_sq, div_eq_mul_inv, ← one_div, inverse_radius A]
  unfold second
  ring

theorem first_actual : first A = deriv (TwoLag.phase q A.edgeShift) A.frequency := by
  have he : TwoLag.phase q A.edgeShift =ᶠ[𝓝 (A.frequency : ℝ)] Geometry.shiftedAngle q A.edgeShift := by
    filter_upwards [isOpen_Ioo.mem_nhds (frequency_interior A)] with x hx
    exact Geometry.jointAngle_actual q A.edgeShift ⟨hx.1.le, hx.2.le⟩
  rw [he.deriv_eq, (Geometry.hasDerivAt_shiftedAngle q A.edgeShift (frequency_interior A)).deriv]
  rfl

theorem second_actual : second A = deriv^[2] (TwoLag.phase q A.edgeShift) A.frequency := by
  have he : TwoLag.phase q A.edgeShift =ᶠ[𝓝 (A.frequency : ℝ)] Geometry.shiftedAngle q A.edgeShift := by
    filter_upwards [isOpen_Ioo.mem_nhds (frequency_interior A)] with x hx
    exact Geometry.jointAngle_actual q A.edgeShift ⟨hx.1.le, hx.2.le⟩
  change _ = deriv (deriv (TwoLag.phase q A.edgeShift)) A.frequency
  rw [he.deriv.deriv_eq]
  change second A = deriv^[2] (Geometry.shiftedAngle q A.edgeShift) A.frequency
  rw [Geometry.deriv2_shiftedAngle q A.edgeShift (frequency_interior A)]
  rfl

theorem near_zero_limit (e z y : ℝ) :
    Tendsto (fun δ => scaledConstraint ((k : ℝ) - 1) z 0 y (nearAngle A e) (farAngle A e) δ / (2 * δ^2))
      (𝓝[≠] 0) (𝓝 (((k : ℝ) - 1) * k * Real.cos (Real.pi / k) / 4 *
        (y^2 - 2 * first A * y) - Real.sin (Real.pi / k) / 2 * z * y)) := by
  simpa only [sub_add_cancel] using zero_constraint_limit (near_analytic A e) (far_analytic A e)
    (near_value A e) (far_value A e) (near_first A e) (far_first A e) y

theorem near_edge_limit (e z y : ℝ) :
    Tendsto (fun δ => scaledConstraint ((k : ℝ) - 1) z (2 * Real.pi / k) y
      (nearAngle A e) (farAngle A e) δ / (2 * δ^2)) (𝓝[≠] 0)
      (𝓝 (Fan.quadratic (((k : ℝ) - 1) * k * Real.cos (Real.pi / k) / 4) (Real.sin (Real.pi / k) / 2)
        ((k : ℝ) * ((k : ℝ) - 1) * second A + 2 * k * (Real.sin (Real.pi / k))^2 * e)
        (2 * first A) z y)) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by have := A.period_ge; omega)
  have he : -((k : ℝ) - 1) * (2 * Real.pi / k) - Real.pi / k = Real.pi / k + (-1 : ℤ) * (2 * Real.pi) := by
    push_cast
    field_simp
    ring
  have hs₁ : Real.sin (2 * Real.pi / k - Real.pi / k) = Real.sin (Real.pi / k) := by
    rw [show 2 * Real.pi / (k : ℝ) - Real.pi / k = Real.pi / k by ring]
  have hc₁ : Real.cos (2 * Real.pi / k - Real.pi / k) = Real.cos (Real.pi / k) := by
    rw [show 2 * Real.pi / (k : ℝ) - Real.pi / k = Real.pi / k by ring]
  have hs₂ : Real.sin (-((k : ℝ) - 1) * (2 * Real.pi / k) - Real.pi / k) = Real.sin (Real.pi / k) := by
    rw [he, Real.sin_add_int_mul_two_pi]
  have hc₂ : Real.cos (-((k : ℝ) - 1) * (2 * Real.pi / k) - Real.pi / k) = Real.cos (Real.pi / k) := by
    rw [he, Real.cos_add_int_mul_two_pi]
  simpa only [sub_add_cancel] using edge_constraint_limit (z := z) (near_analytic A e) (far_analytic A e)
    (near_value A e) (far_value A e) (near_first A e) (far_first A e)
    (near_second A e) (far_second A e) hs₁ hc₁ hs₂ hc₂ y

end Actual
end polyak.FareyPlateau.FanAnalysis
