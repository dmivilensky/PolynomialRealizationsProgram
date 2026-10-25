import polyak.Functions.Normalization
import Mathlib.Analysis.Convex.Deriv

/-!
Article: μ-strong convexity in the original class.
Use: connect the first-order class interface to mathlib's standard convexity.
-/

namespace polyak

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Article: global supporting tangents imply convexity. Proof: use the tangent
at a convex combination and average the two supporting inequalities. -/
theorem convexOn_of_supporting_tangents {f : E → ℝ} {g : E → E}
    (h : ∀ x y, f x + ⟪g x, y - x⟫_ℝ ≤ f y) : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (h z x) ha
  have hy := mul_le_mul_of_nonneg_left (h z y) hb
  have hi : a * ⟪g z, x - z⟫_ℝ + b * ⟪g z, y - z⟫_ℝ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have hz : a • (x - z) + b • (y - z) = 0 := by
      dsimp [z]
      have hb' : b = 1 - a := by linarith
      rw [hb']
      module
    rw [hz, inner_zero_right]
  change f z ≤ a * f x + b * f y
  have hz : (a + b) * f z = f z := by rw [hab, one_mul]
  nlinarith

/-- Article: convex differentiable functions lie above every actual tangent.
Proof: restrict convexity to a real affine line and use the derivative/secant
inequality at the line's origin. -/
theorem supporting_tangents_of_convexOn {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (hc : ConvexOn ℝ Set.univ f) (x y : E) :
    f x + ⟪g x, y - x⟫_ℝ ≤ f y := by
  let d := y - x
  let φ : ℝ → ℝ := fun s => f (x + s • d)
  have hφ : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ a b ha hb hab
    have h := hc.2 (Set.mem_univ (x + s • d)) (Set.mem_univ (x + t • d)) ha hb hab
    change f (x + (a * s + b * t) • d) ≤ a * f (x + s • d) + b * f (x + t • d)
    convert h using 1
    congr 1
    have hb' : b = 1 - a := by linarith
    rw [hb']
    module
  have hline : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hd : HasDerivAt φ ⟪g x, d⟫_ℝ 0 := by
    have hx : x + (0 : ℝ) • d = x := by simp
    have h := (hg (x + (0 : ℝ) • d)).hasFDerivAt.comp_hasDerivAt 0 hline
    simpa only [φ, Function.comp_def, hx, InnerProductSpace.toDual_apply_apply] using h
  have h := hφ.le_slope_of_hasDerivAt (by trivial) (by trivial) (by norm_num : (0 : ℝ) < 1) hd
  simp [slope_def_field, φ, d] at h
  linarith

/-- Article: strong convexity of differentiable functions is precisely the
strong tangent inequality. Proof: subtract the quadratic and use the two
supporting-tangent characterizations above. -/
theorem strongConvexOn_iff_tangent_lower {f : E → ℝ} {μ : ℝ}
    (hf : Differentiable ℝ f) :
    StrongConvexOn Set.univ μ f ↔
      ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  rw [strongConvexOn_iff_convex]
  have hg (x : E) : HasGradientAt (reducedFunction μ f) (gradient f x - μ • x) x := by
    convert hasGradientAt_quadratic_add (hf x).hasGradientAt (-μ) 1 using 1
    · funext y; dsimp [reducedFunction]; ring
    · module
  have heq (x y : E) :
      reducedFunction μ f x + ⟪gradient f x - μ • x, y - x⟫_ℝ ≤ reducedFunction μ f y ↔
      f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
    dsimp [reducedFunction]
    simp only [inner_sub_left, inner_smul_left, inner_sub_right, norm_sub_sq_real,
      real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
    have hi : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := real_inner_comm _ _
    rw [hi]
    constructor <;> intro h <;> nlinarith
  constructor
  · intro hc x y
    exact (heq x y).mp (supporting_tangents_of_convexOn hg hc x y)
  · intro ht
    exact convexOn_of_supporting_tangents (fun x y => (heq x y).mpr (ht x y))

/-- Article: the class really implies the standard μ-strong convexity predicate.
Use: downstream theorems can consume mathlib convexity directly. -/
theorem SmoothStronglyConvex.strongConvexOn {f : E → ℝ} {μ L : ℝ}
    (hf : SmoothStronglyConvex μ L f) : StrongConvexOn Set.univ μ f :=
  (strongConvexOn_iff_tangent_lower hf.differentiable).mpr hf.tangent_lower

/-- Article: exact identification with the standard original class.
Use: accept the article's differentiability, strong convexity and Lipschitz
gradient hypotheses without strengthening their regularity. -/
theorem smoothStronglyConvex_iff_standard {f : E → ℝ} {μ L : ℝ} :
    SmoothStronglyConvex μ L f ↔
      0 < μ ∧ μ < L ∧ Differentiable ℝ f ∧ StrongConvexOn Set.univ μ f ∧
        ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := by
  constructor
  · intro hf
    exact ⟨hf.mu_pos, hf.mu_lt_L, hf.differentiable, hf.strongConvexOn, hf.grad_lipschitz⟩
  · rintro ⟨hμ, hμL, hd, hc, hl⟩
    exact ⟨hμ, hμL, hd, (strongConvexOn_iff_tangent_lower hd).mp hc, hl⟩

end polyak
