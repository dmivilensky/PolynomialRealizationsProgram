import krylov.Convergence.SS1FSource

/-!
Article: main_krylov, thm:ss1F and cor:xrF.
Use: a genuine local function source controls the whole actually computed
corrected matrix, for arbitrary rectangular physical windows. The budget
vanishes with the actual window radius and includes no model-limit premise.
Source: sharp true secants, actual anchored value diagonals, and finite
spectral/Frobenius comparison.
-/

namespace krylov.Convergence
noncomputable section
open Set krylov.Functions
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] {p : ℕ}

/-- A common actual source radius budget for normalized corrected data. -/
def valueWindowBudget (L₂ L₃ B C r : ℝ) : ℝ :=
  L₂*r+2*B*C*r+L₃*(13/3+2*C)*r^2

theorem valueWindowBudget_nonneg {L₂ L₃ B C r : ℝ}
    (hL₂ : 0≤L₂) (hL₃ : 0≤L₃) (hB : 0≤B) (hC : 0≤C) (hr : 0≤r) :
    0≤valueWindowBudget L₂ L₃ B C r := by
  dsimp only [valueWindowBudget]
  positivity

/- Bounding the genuine endpoint and current radii bounds the exact
diagonal source polynomial, with no bound on the dimensionless split. -/
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem value_diagonal_radius_bound {L₂ L₃ B C r : ℝ}
    (hL₂ : 0≤L₂) (hL₃ : 0≤L₃) (hB : 0≤B) (hC : 0≤C) (hr : 0≤r)
    (a s x : E) (ha : ‖a‖≤r) (hb : ‖a+s‖≤r) (hx : ‖x‖≤r) :
    L₂*‖x‖+B*C*‖x-(a+s)‖+L₃*((1/12:ℝ)*‖s‖^2+
      (1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+(1/2:ℝ)*‖x-(a+s)‖^2)≤
      valueWindowBudget L₂ L₃ B C r := by
  have hs : ‖s‖≤2*r := by
    have hh := norm_sub_le (a+s) a
    simp only [add_sub_cancel_left] at hh
    exact hh.trans (by linarith only [ha,hb])
  have hd : ‖x-(a+s)‖≤2*r := (norm_sub_le _ _).trans (by linarith only [hx,hb])
  have hs₂ : ‖s‖^2≤4*r^2 := by nlinarith only [hs,norm_nonneg s,hr]
  have hd₂ : ‖x-(a+s)‖^2≤4*r^2 := by nlinarith only [hd,norm_nonneg (x-(a+s)),hr]
  have hprod : ‖x-(a+s)‖*‖s‖≤4*r^2 := by
    have hh := mul_le_mul hd hs (norm_nonneg s) (by positivity : 0≤2*r)
    nlinarith only [hh]
  have hp : (1/12:ℝ)*‖s‖^2+(1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+
      (1/2:ℝ)*‖x-(a+s)‖^2≤(13/3+2*C)*r^2 := by
    have hh := mul_le_mul_of_nonneg_left hprod (show 0≤(1/2:ℝ)*(1+C) by positivity)
    nlinarith only [hs₂,hd₂,hh]
  have hfirst := mul_le_mul_of_nonneg_left hx hL₂
  have hsecond := mul_le_mul_of_nonneg_left hd (mul_nonneg hB hC)
  have hthird := mul_le_mul_of_nonneg_left hp hL₃
  dsimp only [valueWindowBudget]
  nlinarith only [hfirst,hsecond,hthird]

/-- Every actual function-value window on a small source ball has a small
genuine normalized corrected matrix error. The physical dimension and
number of stored pairs are independent. -/
theorem ss1F_source_normalized_error_bound
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S) {L₂ L₃ : ℝ≥0}
    (hH : LipschitzOnWith L₂ H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h:E,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    (a s : Fin p → E) (l : Fin p → ℝ) (x : E)
    (ha : ∀ i,a i∈S) (hb : ∀ i,a i+s i∈S) (hx : x∈S)
    {r C B : ℝ} (hr : 0≤r) (hC : 0≤C) (hB : 0≤B)
    (har : ∀ i,‖a i‖≤r) (hbr : ∀ i,‖a i+s i‖≤r) (hxr : ‖x‖≤r)
    (hs : ∀ i,s i≠0)
    (hbudget : ∀ i,∀ h:E,‖h‖=1 → |(T (a i+s i)).form h h h|≤B)
    (hw : ∀ i,‖splitRemainder (a i) (s i) x (l i)‖≤C*‖x-(a i+s i)‖) :
    ‖ss1FNormalizedError f G a s l‖≤p*valueWindowBudget L₂ L₃ B C r := by
  have hε := valueWindowBudget_nonneg L₂.coe_nonneg L₃.coe_nonneg hB hC hr
  have hraw : (L₂:ℝ)*r≤valueWindowBudget L₂ L₃ B C r := by
    dsimp only [valueWindowBudget]
    have hrest : 0≤2*B*C*r+(L₃:ℝ)*(13/3+2*C)*r^2 := by positivity
    linarith only [hrest]
  apply ss1FNormalizedError_norm f G a s l hs hε
  · intro i
    apply (unitWindow_image_error s (fun j=>G (a j+s j)-G (a j)) hs ?_ i).trans hraw
    intro j
    have hh := secant_image_endpoint_bound G H S hS h₀ hH hG (a j) (a j+s j) (ha j) (hb j)
    rw [hH₀,ContinuousLinearMap.id_apply,add_sub_cancel_left] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    nlinarith [har j,hbr j,L₂.coe_nonneg]
  · intro i
    exact (ss1F_source_diagonal_bound f G H T S hS h₀ hH hH₀ hf hG hT hLip
      (a i) (s i) x (ha i) (hb i) hx (l i) C B hB (hbudget i) (hw i)).trans
      (mul_le_mul_of_nonneg_right (value_diagonal_radius_bound L₂.coe_nonneg L₃.coe_nonneg
        hB hC hr (a i) (s i) x (har i) (hbr i) hxr) (sq_nonneg _))

end
end krylov.Convergence
