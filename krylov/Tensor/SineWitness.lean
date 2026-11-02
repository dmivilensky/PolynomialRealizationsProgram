import krylov.Tensor.CubicUncurrying
import krylov.Functions.HarmonicCubic

/-!
Article: main_krylov, thm:Hp, its genuine harmonic lower-bound witness.
Use: construct twice the imaginary harmonic cubic on a real orthonormal
plane, with its true diagonal budget and exact first-direction slice.
Source: the elementary identity |z^3|^2=|z|^6 and Bessel's inequality.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Fix the iterated operator-space instance for the explicit curried formula.
local instance sineWitnessCurriedNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ)

/-- The continuous trilinear form of the actual harmonic sine witness.
Article: main_krylov, thm:Hp. -/
def sineForm (φ ψ : E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (2 : ℝ) • (coordinateTriple φ φ ψ + coordinateTriple φ ψ φ +
    coordinateTriple ψ φ φ - coordinateTriple ψ ψ ψ)

/-- Exact evaluation of the genuine harmonic form.
Article: main_krylov, thm:Hp. Proof: evaluate the actual continuous coordinates. -/
theorem sineForm_apply (φ ψ : E →L[ℝ] ℝ) (x y z : E) :
    sineForm φ ψ x y z = 2 * (φ x * (φ y * ψ z) + φ x * (ψ y * φ z) +
      ψ x * (φ y * φ z) - ψ x * (ψ y * ψ z)) := rfl

/-- Twice the imaginary part of the cube of two genuine linear coordinates.
Article: main_krylov, thm:Hp, the printed lower witness. -/
def sineCubic (φ ψ : E →L[ℝ] ℝ) : SymmetricCubic E where
  form := sineForm φ ψ
  swap₁ := by
    intro x y z
    rw [sineForm_apply, sineForm_apply]
    ring
  swap₂ := by
    intro x y z
    rw [sineForm_apply, sineForm_apply]
    ring

/-- Exact true evaluation of the lower-bound tensor.
Article: main_krylov, thm:Hp. Proof: the four actual coordinate monomials. -/
theorem sineCubic_apply (φ ψ : E →L[ℝ] ℝ) (x y z : E) :
    (sineCubic φ ψ).form x y z =
      2 * (φ x * φ y * ψ z + φ x * ψ y * φ z + ψ x * φ y * φ z - ψ x * ψ y * ψ z) := by
  change sineForm φ ψ x y z = _
  rw [sineForm_apply]
  ring

/-- The imaginary harmonic cubic has its sharp unit-disk upper bound.
Article: main_krylov, thm:Hp.
Proof: the squared complementary real harmonic is the nonnegative gap. -/
theorem sine_cubic_disk_bound (c s : ℝ) (hcs : c ^ 2 + s ^ 2 ≤ 1) :
    |3 * c ^ 2 * s - s ^ 3| ≤ 1 := by
  have he : (3*c^2*s-s^3)^2 + (c^3-3*c*s^2)^2 = (c^2+s^2)^3 := by ring
  have hc : (c^2+s^2)^3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ c^2+s^2) hcs 3
  apply abs_le.mpr
  constructor <;> nlinarith only [he, hc, sq_nonneg (c^3-3*c*s^2),
    sq_nonneg (3*c^2*s-s^3+1), sq_nonneg (3*c^2*s-s^3-1)]

/-- The true harmonic tensor meets the original diagonal budget two.
Article: main_krylov, thm:Hp.
Proof: actual orthonormal coordinates contract by Bessel; apply the harmonic disk bound. -/
theorem sineCubic_diagonal_bound (e h : E) (he : ‖e‖ = 1) (hh : ‖h‖ = 1)
    (heh : inner ℝ e h = 0) :
    ∀ x : E, ‖x‖ = 1 → |(sineCubic (innerSL ℝ e) (innerSL ℝ h)).form x x x| ≤ 2 := by
  intro x hx
  have hcoords := orthonormal_pair_coordinates e h x he hh heh
  rw [hx, one_pow] at hcoords
  have hb := sine_cubic_disk_bound (inner ℝ e x) (inner ℝ h x) hcoords
  rw [sineCubic_apply]
  change |2 * (inner ℝ e x * inner ℝ e x * inner ℝ h x +
    inner ℝ e x * inner ℝ h x * inner ℝ e x + inner ℝ h x * inner ℝ e x * inner ℝ e x -
    inner ℝ h x * inner ℝ h x * inner ℝ h x)| ≤ 2
  have heq : inner ℝ e x * inner ℝ e x * inner ℝ h x +
      inner ℝ e x * inner ℝ h x * inner ℝ e x + inner ℝ h x * inner ℝ e x * inner ℝ e x -
      inner ℝ h x * inner ℝ h x * inner ℝ h x = 3 * (inner ℝ e x)^2 * inner ℝ h x - (inner ℝ h x)^3 := by ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

/-- The true oldest-direction slice of the witness is the printed rank-two cross form.
Article: main_krylov, thm:Hp.
Proof: evaluate the genuine tensor at its actual unit first direction. -/
theorem sineCubic_first_slice (e h : E) (he : ‖e‖ = 1) (heh : inner ℝ h e = 0) (y z : E) :
    (sineCubic (innerSL ℝ e) (innerSL ℝ h)).form e y z =
      2 * (inner ℝ e y * inner ℝ h z + inner ℝ h y * inner ℝ e z) := by
  rw [sineCubic_apply]
  simp only [innerSL_apply_apply, real_inner_self_eq_norm_sq, he, one_pow, heh,
    one_mul, zero_mul, add_zero, sub_zero]

end
end krylov.Tensor
