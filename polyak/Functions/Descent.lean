import polyak.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Article: Appendix A, proof of normalization and necessity of interpolation.
Use: the descent inequality and cocoercivity from genuine first derivatives.
-/

namespace polyak

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: descent inequality. Proof: compare the function along a line with
its quadratic upper model, whose derivative dominates the line derivative. -/
theorem descent_inequality {f : E → ℝ} {g : E → E} {K : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ K * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪g x, y - x⟫_ℝ + K / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let φ : ℝ → ℝ := fun s =>
    f (x + s • d) - f x - s * ⟪g x, d⟫_ℝ - K / 2 * s ^ 2 * ‖d‖ ^ 2
  have hline (s : ℝ) : HasDerivAt (fun t : ℝ => x + t • d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have hφ (s : ℝ) : HasDerivAt φ
      (⟪g (x + s • d) - g x, d⟫_ℝ - K * s * ‖d‖ ^ 2) s := by
    have hf := (hg (x + s • d)).hasFDerivAt.comp_hasDerivAt s (hline s)
    have hp := (((hasDerivAt_id s).pow 2).const_mul (K / 2)).mul_const (‖d‖ ^ 2)
    convert ((hf.sub_const (f x)).sub ((hasDerivAt_id s).mul_const ⟪g x, d⟫_ℝ)).sub hp using 1
    · rfl
    · simp only [InnerProductSpace.toDual_apply_apply, inner_sub_left, id_eq]
      ring
  have hmono : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun s _ => (hφ s).continuousAt.continuousWithinAt)
      (fun s _ => (hφ s).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [(hφ s).deriv]
    have hs0 : 0 ≤ s := (interior_subset hs).1
    have hdist := hLip (x + s • d) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0] at hdist
    have hinner := (real_inner_le_norm (g (x + s • d) - g x) d).trans
      (mul_le_mul_of_nonneg_right hdist (norm_nonneg d))
    nlinarith [sq_nonneg ‖d‖]
  have h := hmono (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
  simp [φ, d] at h
  linarith

omit [CompleteSpace E] in
/-- Article: convex smooth interpolation inequality. Proof: take one descent
step for f minus the tangent at y, and use its global minimum at y. -/
theorem convex_descent_gap {f : E → ℝ} {g : E → E} {K : ℝ} (hK : 0 < K)
    (hlower : ∀ x y, f x + ⟪g x, y - x⟫_ℝ ≤ f y)
    (hupper : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫_ℝ + K / 2 * ‖y - x‖ ^ 2)
    (x y : E) : ‖g x - g y‖ ^ 2 ≤ 2 * K * (f x - f y - ⟪g y, x - y⟫_ℝ) := by
  let d := g x - g y
  let z := x + (-1 / K) • d
  have h := (hlower y z).trans (hupper x z)
  have hz : z - y = x - y + (-1 / K) • d := by dsimp [z]; abel
  have hx : z - x = (-1 / K) • d := by simp [z]
  rw [hz, hx, inner_add_right, inner_smul_right, inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have hd : ⟪g x, d⟫_ℝ - ⟪g y, d⟫_ℝ = ‖d‖ ^ 2 := by
    rw [← inner_sub_left, ← real_inner_self_eq_norm_sq]
  have hscaled := mul_le_mul_of_nonneg_left h (le_of_lt hK)
  field_simp [ne_of_gt hK] at hscaled
  dsimp [d] at hd ⊢
  nlinarith

omit [CompleteSpace E] in
/-- Article: cocoercivity of a convex K-smooth gradient. Proof: add the two
convex descent gaps; this proof uses no second derivatives. -/
theorem cocoercive_of_quadratic_bounds {f : E → ℝ} {g : E → E} {K : ℝ} (hK : 0 < K)
    (hlower : ∀ x y, f x + ⟪g x, y - x⟫_ℝ ≤ f y)
    (hupper : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫_ℝ + K / 2 * ‖y - x‖ ^ 2)
    (x y : E) : ‖g x - g y‖ ^ 2 ≤ K * ⟪g x - g y, x - y⟫_ℝ := by
  have hxy := convex_descent_gap hK hlower hupper x y
  have hyx := convex_descent_gap hK hlower hupper y x
  rw [norm_sub_rev (g y) (g x)] at hyx
  have hi : ⟪g x - g y, x - y⟫_ℝ =
      -(⟪g y, x - y⟫_ℝ + ⟪g x, y - x⟫_ℝ) := by
    simp only [inner_sub_left, inner_sub_right]; ring
  rw [hi]
  nlinarith

omit [CompleteSpace E] in
/-- Article: the reflected cocoercive gradient is nonexpansive.
Proof: expand one squared Hilbert norm. -/
theorem norm_reflection_le {K : ℝ} (hK : 0 < K) (d r : E)
    (h : ‖r‖ ^ 2 ≤ K * ⟪r, d⟫_ℝ) : ‖d - (2 / K) • r‖ ≤ ‖d‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hi : ⟪d, r⟫_ℝ = ⟪r, d⟫_ℝ := real_inner_comm _ _
  rw [hi]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hK)).mp
  field_simp [ne_of_gt hK]
  nlinarith

end polyak
