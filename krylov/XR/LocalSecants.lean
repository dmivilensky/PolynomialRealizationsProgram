import krylov.XR.ExecutionQueryBounds
import krylov.XR.MemoryObservations

/-!
Article: main_krylov, G1 and proof of thm:grow, genuine positive secants.
Use: derive actual relative secant errors and strict observed curvature
from the true local Hessian. Every sufficiently late nonzero accepted step
therefore really is appended by the original algorithm. Source: the genuine
derivative mean-value estimate on the convex local ball and SPD coercivity.
-/

namespace krylov.XR
noncomputable section
open Set Metric krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual local gradient differences inherit the true Hessian error,
with no abstract secant-operator field or query-bound assumption. -/
theorem local_secant_error (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (center : E) (radius : ℝ) (epsilon : ℝ≥0)
    (hG : ∀ z ∈ ball center radius, HasFDerivAt G (H z) z)
    (hH : ∀ z ∈ ball center radius, ‖H z - Q‖ ≤ (epsilon : ℝ))
    (a b : E) (ha : a ∈ ball center radius) (hb : b ∈ ball center radius) :
    ‖G b - G a - Q (b - a)‖ ≤ (epsilon : ℝ) * ‖b - a‖ := by
  have hLip := gradient_error_lipschitzOn_of_hessian G H Q (ball center radius)
    (convex_ball center radius) hG hH
  have h := hLip.norm_sub_le hb ha
  have he : (G b - Q b) - (G a - Q a) = G b - G a - Q (b - a) := by rw [map_sub]; abel
  rwa [he] at h

/-- A genuine small relative secant error preserves strict positive
curvature; the positivity test of appendPositive is therefore derived. -/
theorem positive_secant_of_reference_error (Q : E →L[ℝ] E) (mu epsilon : ℝ)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (Q v))
    (he : epsilon < mu) (s y : E) (hs : s ≠ 0) (herr : ‖y - Q s‖ ≤ epsilon * ‖s‖) :
    0 < inner ℝ s y := by
  have hinner := (abs_real_inner_le_norm s (y - Q s)).trans
    (mul_le_mul_of_nonneg_left herr (norm_nonneg s))
  rw [inner_sub_right] at hinner
  have hlow := (abs_le.mp hinner).1
  have hpos := hpositive s
  have hstrict : 0 < (mu - epsilon) * ‖s‖ ^ 2 :=
    mul_pos (sub_pos.mpr he) (sq_pos_of_pos (norm_pos_iff.mpr hs))
  nlinarith

/-- Actual local strong monotonicity makes the known local critical point
the unique critical point in its ball. Thus G1's x_k≠x* really implies
nonzero observed gradients on the local tail. -/
theorem local_gradient_ne_zero (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (center : E) (radius : ℝ) (hradius : 0 < radius) (epsilon : ℝ≥0) (mu : ℝ)
    (hG : ∀ z ∈ ball center radius, HasFDerivAt G (H z) z)
    (hH : ∀ z ∈ ball center radius, ‖H z - Q‖ ≤ (epsilon : ℝ))
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (Q v))
    (he : (epsilon : ℝ) < mu) (hzero : G center = 0)
    (x : E) (hx : x ∈ ball center radius) (hne : x ≠ center) : G x ≠ 0 := by
  have herr := local_secant_error G H Q center radius epsilon hG hH center x (mem_ball_self hradius) hx
  have hp := positive_secant_of_reference_error Q mu epsilon hpositive he (x - center)
    (G x - G center) (sub_ne_zero.mpr hne) herr
  intro hz
  rw [hz, hzero, sub_self, inner_zero_right] at hp
  exact hp.false

/-- Every actual nonstationary gradient-related trial has a nonzero
physical step at every positive backtracking length. -/
theorem gradientRelated_step_ne_zero (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (g u : E) (hg : g ≠ 0) (hu : GradientRelated c₁ c₂ g u)
    (t : ℝ) (ht : 0 < t) : t • u ≠ 0 := by
  have hs : inner ℝ g u < 0 := hu.1.trans_lt (by
    have hn := mul_pos hc₁ (sq_pos_of_pos (norm_pos_iff.mpr hg))
    nlinarith)
  have hune : u ≠ 0 := by intro hz; rw [hz, inner_zero_right] at hs; exact hs.false
  exact smul_ne_zero ht.ne' hune

/-- The real cached trial pair passes its actual strict curvature test
as soon as its two genuine endpoints lie in the local Hessian ball. -/
theorem observedTrialPair_positive_local (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (center : E) (radius : ℝ) (epsilon : ℝ≥0) (mu : ℝ)
    (hG : ∀ z ∈ ball center radius, HasFDerivAt G (H z) z)
    (hH : ∀ z ∈ ball center radius, ‖H z - Q‖ ≤ (epsilon : ℝ))
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (Q v)) (he : (epsilon : ℝ) < mu)
    (S : State E) (hcache : S.gradient = G S.point) (s : E) (hs : s ≠ 0)
    (ha : S.point ∈ ball center radius) (hb : S.point + s ∈ ball center radius) :
    positivePair (observedTrialPair f G S s) := by
  have herr := local_secant_error G H Q center radius epsilon hG hH S.point (S.point + s) ha hb
  simp only [add_sub_cancel_left] at herr
  change 0 < inner ℝ s (G (S.point + s) - S.gradient)
  rw [hcache]
  exact positive_secant_of_reference_error Q mu epsilon hpositive he s _ hs herr

end
end krylov.XR
