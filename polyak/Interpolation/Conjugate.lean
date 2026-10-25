import polyak.Interpolation.Epigraph
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Article: Appendix A, differentiability of the conjugate H*.
Use: a genuine everywhere differentiable convex extension and its sharp
cocoercive gradient, obtained from the unbounded-table epigraph construction.
Proof: the unique dual optimizer supplies a quadratic sandwich. A remainder
of order ‖h‖² is little-o of ‖h‖, so it is an actual Fréchet derivative.
-/

noncomputable section

open Filter Set Asymptotics
open scoped Topology

namespace polyak.Interpolation

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: differentiability in the conjugate construction.
Use: turn a global quadratic sandwich into a genuine first derivative.
Proof: a quadratic remainder is little-o of the increment. -/
theorem hasGradientAt_of_quadratic_sandwich {f : E → ℝ} {g : E → E}
    (hlower : ∀ x y, f x + inner ℝ (g x) (y - x) ≤ f y)
    (hupper : ∀ x y, f y ≤ f x + inner ℝ (g x) (y - x) + ‖y - x‖ ^ 2)
    (x : E) : HasGradientAt f (g x) x := by
  rw [hasGradientAt_iff_isLittleO]
  have hbig : (fun y => f y - f x - inner ℝ (g x) (y - x)) =O[𝓝 x]
      (fun y => ‖y - x‖ ^ 2) := by
    apply isBigO_iff.mpr
    refine ⟨1, Eventually.of_forall fun y => ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y - x‖), one_mul]
    exact abs_le.mpr ⟨by nlinarith [hlower x y, sq_nonneg ‖y - x‖], by linarith [hupper x y]⟩
  exact hbig.trans_isLittleO (isLittleO_pow_sub_sub x (m := 2) (by decide))

omit [CompleteSpace E] in
/-- Article: uniqueness of the dual minimizer. Use: the chosen gradient is intrinsic.
Proof: the strong support estimate forces distance zero between two minima. -/
theorem min_height_unique {x G : I → E} {F : I → ℝ} {u : E} {p q : E × ℝ}
    (hp : p ∈ shiftedEpigraph x G F u)
    (hmin : ∀ r ∈ shiftedEpigraph x G F u, p.2 ≤ r.2)
    (hq : q ∈ shiftedEpigraph x G F u)
    (hqmin : ∀ r ∈ shiftedEpigraph x G F u, q.2 ≤ r.2) : p = q := by
  have h := min_height_strong hp hmin q hq
  have he : p.2 = q.2 := le_antisymm (hmin q hq) (hqmin p hp)
  have hz : ‖p.1 - q.1‖ = 0 := by nlinarith [sq_nonneg ‖p.1 - q.1‖]
  exact Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp hz)) he

omit [CompleteSpace E] in
/-- Article: the Fenchel conjugate in (extension).
Use: the conjugate is defined by all epigraph affine minorants, permitting
infinite values of the original supremum away from its domain. -/
def conjugateValueSet (x G : I → E) (F : I → ℝ) (u : E) : Set ℝ :=
  {v | ∃ y r, (y, r) ∈ shiftedEpigraph x G F 0 ∧ v = inner ℝ u y - r}

omit [CompleteSpace E] in
/-- Article: H* is the conjugate in (extension).
Use: identify the epigraph minimum construction with the exact Fenchel supremum.
Proof: shift epigraph heights by the linear form; the minimizing point attains
the supremum and its minimality bounds every other affine value. -/
theorem min_height_conjugate_isLUB {x G : I → E} {F : I → ℝ} {u : E} {p : E × ℝ}
    (hp : p ∈ shiftedEpigraph x G F u)
    (hmin : ∀ q ∈ shiftedEpigraph x G F u, p.2 ≤ q.2) :
    IsLUB (conjugateValueSet x G F u) (-p.2) := by
  have hatt : -p.2 ∈ conjugateValueSet x G F u := by
    refine ⟨p.1, p.2 + inner ℝ u p.1, ?_, by ring⟩
    intro i
    have hi := hp i
    simp only [inner_zero_left, sub_zero]
    linarith
  constructor
  · rintro v ⟨y, r, hmem, rfl⟩
    have hs : (y, r - inner ℝ u y) ∈ shiftedEpigraph x G F u := by
      intro i
      have hi := hmem i
      simp only [inner_zero_left, sub_zero] at hi
      dsimp only
      linarith
    have hi := hmin _ hs
    dsimp only at hi
    linarith
  · intro b hb
    exact hb hatt

/-- Article: Appendix A, conjugate interpolation.
Use: arbitrary-set, unbounded Hilbert-space data produce one global actual function.
Proof: minimize every shifted quadratic epigraph; transfer optimizers between
shifts, use sharp strong support, and identify each prescribed datum. -/
theorem exists_convex_interpolant {x G : I → E} {F : I → ℝ}
    (h : ConvexTableFeasible x G F) (star : I)
    (hx : x star = 0) (hG : G star = 0) (hF : F star = 0) :
    ∃ (f : E → ℝ) (g : E → E),
      (∀ u, HasGradientAt f (g u) u) ∧
      (∀ u v, f u + inner ℝ (g u) (v - u) ≤ f v) ∧
      (∀ u v, f v ≤ f u + inner ℝ (g u) (v - u) + ‖v - u‖ ^ 2) ∧
      (∀ u v, ‖g u - g v‖ ^ 2 ≤ 2 * inner ℝ (g u - g v) (u - v)) ∧
      (∀ i, f (x i) = F i ∧ g (x i) = G i) := by
  choose p hp hmin using shiftedEpigraph_hasMin h star hx hG hF
  let f : E → ℝ := fun u => -(p u).2
  let g : E → E := fun u => (p u).1
  have hshift (u v : E) :
      ((p v).1, (p v).2 + inner ℝ (v - u) (p v).1) ∈ shiftedEpigraph x G F u := by
    intro i
    have hh := hp v i
    simp only [inner_sub_left]
    linarith
  have hstrong (u v : E) : f u + inner ℝ (g u) (v - u) +
      (1 / 4 : ℝ) * ‖g u - g v‖ ^ 2 ≤ f v := by
    have hh := min_height_strong (hp v) (hmin v) _ (hshift v u)
    dsimp only at hh
    rw [norm_sub_rev (p v).1 (p u).1] at hh
    simp only [inner_sub_left] at hh
    dsimp [f, g]
    simp only [inner_sub_right]
    rw [real_inner_comm (p u).1 u, real_inner_comm (p u).1 v] at hh
    linarith
  have hlower (u v : E) : f u + inner ℝ (g u) (v - u) ≤ f v := by
    have hh := hstrong u v
    nlinarith [sq_nonneg ‖g u - g v‖]
  have hupper (u v : E) : f v ≤ f u + inner ℝ (g u) (v - u) + ‖v - u‖ ^ 2 := by
    have hh := hstrong v u
    rw [norm_sub_rev (g v) (g u)] at hh
    have hin : inner ℝ (g v - g u) (v - u) ≤ ‖g v - g u‖ * ‖v - u‖ :=
      real_inner_le_norm _ _
    rw [norm_sub_rev (g v) (g u)] at hin
    simp only [inner_sub_left, inner_sub_right] at hh hin ⊢
    nlinarith [sq_nonneg (‖g u - g v‖ - 2 * ‖v - u‖)]
  refine ⟨f, g, hasGradientAt_of_quadratic_sandwich hlower hupper, hlower, hupper, ?_, ?_⟩
  · intro u v
    have hu := hstrong u v
    have hv := hstrong v u
    rw [norm_sub_rev (g v) (g u)] at hv
    simp only [inner_sub_left, inner_sub_right] at hu hv ⊢
    linarith
  · intro i
    have hle := hmin (x i) _ (shiftedEpigraph_datum h (x i) i)
    have hge := hp (x i) i
    rw [quadraticTerm_eq] at hge
    dsimp only at hle
    have hz : ‖(p (x i)).1 - G i‖ = 0 := by
      nlinarith [sq_nonneg ‖(p (x i)).1 - G i‖]
    have he : (p (x i)).1 = G i := sub_eq_zero.mp (norm_eq_zero.mp hz)
    refine ⟨?_, he⟩
    dsimp [f]
    nlinarith [sq_nonneg ‖(p (x i)).1 - G i‖]

end polyak.Interpolation
