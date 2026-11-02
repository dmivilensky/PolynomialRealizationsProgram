import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Article: main_krylov, s4:eq:K and apD:lemmas, the second-order scalar maximum.
Use: provide the actual maximizing parameter, including zero budgets, before
using the sharp constant in operator and information bounds.
Source: elementary constrained quadratic optimization; the proof uses a
nonnegative sum of squares rather than differentiation at an endpoint.
-/

namespace krylov.Correction
noncomputable section

/-- The complementary coordinate of the scalar maximizing direction.
Use: the zero-total-budget branch is defined without an inverse denominator.
Article: main_krylov, apD:lemmas, c=(√(w²+8W²)−w)/(4W). -/
def maximizingComplement (W w : ℝ) : ℝ :=
  if W = 0 then 0 else (Real.sqrt (w^2 + 8*W^2) - w)/(4*W)

/-- The cross-action coordinate of the scalar maximizing direction.
Use: construct an attaining parameter in the closed unit interval.
Article: main_krylov, apD:lemmas, a=√(1−c²). -/
def maximizingCross (W w : ℝ) : ℝ :=
  Real.sqrt (1 - maximizingComplement W w ^ 2)

/-- The attained second-order correction constant, defined also at zero budgets.
Use: its variational characterization below identifies it with the article's K.
Article: main_krylov, s4:eq:K, K(W,w). -/
def sharpConstant (W w : ℝ) : ℝ :=
  W * maximizingCross W w * (W * maximizingComplement W w + w)

/-- The explicit complementary coordinate is positive and solves its quadratic equation.
Use: justify every denominator and the admissibility of the maximizing direction.
Article: main_krylov, apD:lemmas, W−2Wc²−wc=0.
Proof: the square root is strictly larger than w; squaring its defining
identity yields the quadratic, whose nonnegative coefficients bound c². -/
theorem maximizingComplement_spec {W w : ℝ} (hW : 0 < W) (hw : 0 ≤ w) :
    0 < maximizingComplement W w ∧
      2 * W * maximizingComplement W w ^ 2 + w * maximizingComplement W w = W ∧
      maximizingComplement W w ^ 2 ≤ 1/2 := by
  -- The positive square-root gap justifies division before the quadratic identity is used.
  let s := Real.sqrt (w^2 + 8*W^2)
  have hs : s^2 = w^2 + 8*W^2 := Real.sq_sqrt (by positivity)
  have hsw : w < s := by
    have hn : 0 ≤ s := Real.sqrt_nonneg _
    nlinarith [sq_pos_of_pos hW]
  have hc : maximizingComplement W w = (s-w)/(4*W) := by
    simp only [maximizingComplement, ne_of_gt hW, ↓reduceIte, s]
  have hp : 0 < maximizingComplement W w := by rw [hc]; positivity
  have he : 2*W*maximizingComplement W w^2+w*maximizingComplement W w=W := by
    rw [hc]
    field_simp
    nlinarith
  refine ⟨hp,he,?_⟩
  nlinarith [mul_nonneg hw hp.le]

/-- A stationary point in the first quadrant maximizes the bilinear objective on the unit circle.
Use: a reusable algebraic optimization argument for all nonnegative budgets.
Article: main_krylov, apD:lemmas, scalar maximization of K.
Proof: the objective gap is a sum of two squares with coefficients ell−W and W. -/
theorem circle_objective_max {W w a₀ c₀ ell a c : ℝ}
    (hW : 0 ≤ W) (hell : W ≤ ell)
    (hn₀ : a₀^2+c₀^2=1) (hn : a^2+c^2=1)
    (ha : ell*a₀=W*c₀+w) (hc : ell*c₀=W*a₀) :
    a*(W*c+w) ≤ a₀*(W*c₀+w) := by
  -- Compare both points on the circle through the positive quadratic remainder.
  have he : 2*(a₀*(W*c₀+w)-a*(W*c+w)) =
      (ell-W)*((a-a₀)^2+(c-c₀)^2)+W*((a-a₀)-(c-c₀))^2 := by
    linear_combination -ell*hn + ell*hn₀ + 2*(a-a₀)*ha + 2*(c-c₀)*hc
  have hp := add_nonneg
    (mul_nonneg (sub_nonneg.mpr hell) (add_nonneg (sq_nonneg (a-a₀)) (sq_nonneg (c-c₀))))
    (mul_nonneg hW (sq_nonneg ((a-a₀)-(c-c₀))))
  linarith

/-- The constructed scalar direction lies in the unit quarter-circle and attains the global maximum.
Use: eliminate the scalar supremum without assuming existence of an optimizer.
Article: main_krylov, s4:eq:K and apD:lemmas.
Proof: solve the explicit quadratic for c, form a=√(1−c²), and apply the
sum-of-squares circle bound with ell=(Wc+w)/a; the zero budget is separate. -/
theorem sharpConstant_variational {W w : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w) :
    maximizingCross W w ∈ Set.Icc (0 : ℝ) 1 ∧
      sharpConstant W w = W * maximizingCross W w *
        (W * Real.sqrt (1-maximizingCross W w^2)+w) ∧
      ∀ a ∈ Set.Icc (0 : ℝ) 1,
        W*a*(W*Real.sqrt (1-a^2)+w) ≤ sharpConstant W w := by
  -- Treat the zero-budget endpoint before normalizing the positive-budget stationary point.
  by_cases hz : W=0
  · subst W
    simp [sharpConstant,maximizingCross,maximizingComplement]
  have hWp : 0<W := lt_of_le_of_ne hW (Ne.symm hz)
  obtain ⟨hc,he,hc₂⟩ := maximizingComplement_spec hWp hw
  let c := maximizingComplement W w
  let a₀ := maximizingCross W w
  have hcs : 0 ≤ 1-c^2 := by dsimp only [c]; linarith
  have ha₀ : 0 < a₀ := Real.sqrt_pos.mpr (by dsimp only [c] at hcs ⊢; linarith)
  have ha₂ : a₀^2=1-c^2 := Real.sq_sqrt hcs
  have hac : c ≤ a₀ := by
    dsimp only [c] at ha₂ ⊢
    nlinarith
  have ha₁ : a₀ ≤ 1 := by nlinarith [sq_nonneg c]
  have hroot : Real.sqrt (1-a₀^2)=c := by
    rw [show 1-a₀^2=c^2 by linarith, Real.sqrt_sq hc.le]
  refine ⟨⟨ha₀.le,ha₁⟩,?_,?_⟩
  · change W*a₀*(W*c+w)=W*a₀*(W*Real.sqrt (1-a₀^2)+w)
    rw [hroot]
  intro a ha
  let b := Real.sqrt (1-a^2)
  have hb : b^2=1-a^2 := Real.sq_sqrt (by nlinarith [ha.1,ha.2])
  let ell := (W*c+w)/a₀
  have hella : ell*a₀=W*c+w := div_mul_cancel₀ _ ha₀.ne'
  have hellc : ell*c=W*a₀ := by
    apply (mul_right_cancel₀ ha₀.ne')
    calc ell*c*a₀ = (ell*a₀)*c := by ring
         _ = (W*c+w)*c := by rw [hella]
         _ = W*a₀*a₀ := by dsimp only [c] at ha₂ ⊢; nlinarith
  have hellW : W ≤ ell := by
    have hp : W*c ≤ W*a₀ := mul_le_mul_of_nonneg_left hac hW
    rw [← hellc] at hp
    nlinarith
  have hm := circle_objective_max hW hellW (by linarith : a₀^2+c^2=1)
    (by linarith : a^2+b^2=1) hella hellc
  simpa only [mul_assoc,sharpConstant,a₀,c,b] using mul_le_mul_of_nonneg_left hm hW

/-- Both explicit maximizing coordinates are nonnegative and lie on the unit circle.
Use: instantiate concrete planar attaining matrices, also for a zero total budget.
Article: main_krylov, apD:lemmas, the maximizing pair (c,a).
Proof: the zero-budget formula is explicit; otherwise the proved quadratic
equation bounds c² and the defining nonnegative square root supplies a². -/
theorem maximizing_coordinates {W w : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w) :
    0 ≤ maximizingComplement W w ∧ 0 ≤ maximizingCross W w ∧
      maximizingComplement W w^2+maximizingCross W w^2=1 := by
  -- The explicit zero-budget branch also lies on the unit circle.
  by_cases hz : W=0
  · subst W
    simp [maximizingComplement,maximizingCross]
  obtain ⟨hc,_,hc₂⟩ := maximizingComplement_spec (lt_of_le_of_ne hW (Ne.symm hz)) hw
  refine ⟨hc.le,Real.sqrt_nonneg _,?_⟩
  have hs := Real.sq_sqrt (show 0 ≤ 1-maximizingComplement W w^2 by linarith)
  change maximizingComplement W w^2+(Real.sqrt (1-maximizingComplement W w^2))^2=1
  linarith

end
end krylov.Correction
