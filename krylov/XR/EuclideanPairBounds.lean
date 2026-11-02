import krylov.XR.EuclideanModel
import krylov.XR.CorrectedPairBounds

/-!
Article: main_krylov, cor:xrF, genuine Euclidean value-diagonal bound.
Use: retain the squared-step normalization even for arbitrarily short
actual observations. The Euclidean projection needs no curvature bound.
Source: Cauchy--Schwarz and the proved scalar trapezoid remainder.
-/
namespace krylov.XR
noncomputable section
open krylov.Methods
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A Euclidean split is controlled after multiplication by its actual
step length, without a lower bound on that length. -/
theorem pair_euclidean_split_scaled_bound (a : PairObservation E) (x : E)
    (hs : a.step≠0) :
    |inner ℝ a.step (x-a.anchor)/‖a.step‖^2-1/2| *‖a.step‖≤
      ‖x-a.anchor‖+‖a.step‖/2 := by
  let b : PairObservation E:={a with image:=a.step,anchorPairing:=inner ℝ a.step (x-a.anchor)}
  have hh:=pair_model_split_scaled_bound b x 1 1 (by norm_num) (by norm_num) hs rfl
    (by simp only [b,real_inner_self_eq_norm_sq,one_mul];exact le_rfl)
    (by simp only [b,one_mul];exact le_rfl)
  simpa only [b,real_inner_self_eq_norm_sq,div_one,one_mul] using hh

/-- Actual cubic endpoint defects give the Euclidean diagonal the same
vanishing relative scale, with no short-step or supplied split premise. -/
theorem pair_euclidean_value_term_bound (a : PairObservation E) (x : E)
    (L : ℝ) (hL : 0≤L) (hs : a.step≠0)
    (hdelta : |a.valueDefect| ≤L*‖a.step‖^3/2) :
    |12*(inner ℝ a.step (x-a.anchor)/‖a.step‖^2-1/2)*a.valueDefect| ≤
      (6*L*(‖x-a.anchor‖+‖a.step‖/2))*‖a.step‖^2 := by
  have hspl:=pair_euclidean_split_scaled_bound a x hs
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<12)]
  calc
    _ ≤ (12*|inner ℝ a.step (x-a.anchor)/‖a.step‖^2-1/2|)*(L*‖a.step‖^3/2) :=
      mul_le_mul_of_nonneg_left hdelta (by positivity)
    _ = (6*L*(|inner ℝ a.step (x-a.anchor)/‖a.step‖^2-1/2| *‖a.step‖))*‖a.step‖^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hspl (by positivity)) (sq_nonneg _)

/-- The literal oversized-term gate cannot enlarge a true value term. -/
theorem euclideanStoredValueTerm_abs_le (x : E) (W : List (PairObservation E)) (i : Fin W.length) :
    |euclideanStoredValueTerm x W i| ≤|12*euclideanStoredSplit x W i*(W.get i).valueDefect| := by
  classical
  unfold euclideanStoredValueTerm
  dsimp only
  split
  · simpa only [abs_zero] using abs_nonneg (12*euclideanStoredSplit x W i*(W.get i).valueDefect)
  · exact le_rfl

end
end krylov.XR
