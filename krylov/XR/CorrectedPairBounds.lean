import krylov.XR.CorrectedDefect

/-!
Article: main_krylov, cor:xrF and apH:impl, observable corrected diagonals.
Use: control the dimensionless covector split only after multiplying by
its genuine step length. Thus arbitrarily small retained steps cause no
loss in the actual normalized value-diagonal estimate.
Source: observed positive curvature, Cauchy--Schwarz and the true cubic
scalar-defect bound; no split bound is a policy assumption.
-/

namespace krylov.XR
noncomputable section
open krylov.Methods
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine model-metric split has a uniform physically scaled bound,
without imposing a lower bound on the length of its observed step. -/
theorem pair_model_split_scaled_bound (a : PairObservation E) (x : E)
    (mu upper : ℝ) (hmu : 0 < mu) (hupper : 0 ≤ upper) (hs : a.step ≠ 0)
    (hphi : a.anchorPairing = inner ℝ a.image (x - a.anchor))
    (hcoerc : mu * ‖a.step‖ ^ 2 ≤ inner ℝ a.step a.image)
    (hy : ‖a.image‖ ≤ upper * ‖a.step‖) :
    |a.anchorPairing / inner ℝ a.step a.image - 1 / 2| * ‖a.step‖ ≤
      (upper / mu) * ‖x - a.anchor‖ + ‖a.step‖ / 2 := by
  have hn : 0 < ‖a.step‖ := norm_pos_iff.mpr hs
  have hq : 0 < inner ℝ a.step a.image := (mul_pos hmu (sq_pos_of_pos hn)).trans_le hcoerc
  have hp : |a.anchorPairing| ≤ upper * ‖a.step‖ * ‖x - a.anchor‖ := by
    rw [hphi]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
  have hd : 0 ≤ upper / mu * ‖x - a.anchor‖ := by positivity
  have hb : |a.anchorPairing| * ‖a.step‖ ≤
      (upper / mu * ‖x - a.anchor‖) * inner ℝ a.step a.image := by
    calc
      _ ≤ (upper * ‖a.step‖ * ‖x - a.anchor‖) * ‖a.step‖ :=
        mul_le_mul_of_nonneg_right hp hn.le
      _ = (upper / mu * ‖x - a.anchor‖) * (mu * ‖a.step‖ ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoerc hd
  have hdiv : (|a.anchorPairing| / inner ℝ a.step a.image) * ‖a.step‖ ≤
      upper / mu * ‖x - a.anchor‖ := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hq).2 hb
  have ht := mul_le_mul_of_nonneg_right
    (abs_sub (a.anchorPairing / inner ℝ a.step a.image) (1 / 2 : ℝ)) hn.le
  rw [abs_div, abs_of_pos hq] at ht
  norm_num at ht
  linarith

/-- True cubic endpoint defects give a vanishing normalized value term,
uniformly over arbitrarily short observed pairs and oblique splits. -/
theorem pair_value_term_bound (a : PairObservation E) (x : E)
    (mu upper L : ℝ) (hmu : 0 < mu) (hupper : 0 ≤ upper) (hL : 0 ≤ L)
    (hs : a.step ≠ 0) (hphi : a.anchorPairing = inner ℝ a.image (x - a.anchor))
    (hcoerc : mu * ‖a.step‖ ^ 2 ≤ inner ℝ a.step a.image)
    (hy : ‖a.image‖ ≤ upper * ‖a.step‖)
    (hdelta : |a.valueDefect| ≤ L * ‖a.step‖ ^ 3 / 2) :
    |12 * (a.anchorPairing / inner ℝ a.step a.image - 1 / 2) * a.valueDefect| ≤
      (6 * L * ((upper / mu) * ‖x - a.anchor‖ + ‖a.step‖ / 2)) * ‖a.step‖ ^ 2 := by
  have hspl := pair_model_split_scaled_bound a x mu upper hmu hupper hs hphi hcoerc hy
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
  calc
    _ ≤ (12 * |a.anchorPairing / inner ℝ a.step a.image - 1 / 2|) *
        (L * ‖a.step‖ ^ 3 / 2) := mul_le_mul_of_nonneg_left hdelta (by positivity)
    _ = (6 * L * (|a.anchorPairing / inner ℝ a.step a.image - 1 / 2| * ‖a.step‖)) *
        ‖a.step‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hspl (by positivity)) (sq_nonneg _)

/-- The exact oversized-term safeguard never enlarges the observed value
diagonal, including before the local branch becomes inactive. -/
theorem storedValueTerm_abs_le (W : List (PairObservation E)) (i : Fin W.length) :
    |storedValueTerm W i| ≤ |12 * storedSplit W i * (W.get i).valueDefect| := by
  classical
  unfold storedValueTerm
  dsimp only
  split
  · simpa only [abs_zero] using abs_nonneg (12 * storedSplit W i * (W.get i).valueDefect)
  · exact le_rfl

end
end krylov.XR
