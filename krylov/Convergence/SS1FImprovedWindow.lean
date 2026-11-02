import krylov.Convergence.SS1FWindowBounds

/-!
Article: main_krylov, thm:ss1F, improved age separation of actual F data.
Use: the oldest raw image is absent from every off-diagonal error. After
its measured diagonal is corrected, the whole actual matrix depends on the
newer radius to first order and on the oldest radius only quadratically.
Source: the actual anchored diagonal estimate and the newer-column selector.
-/

namespace krylov.Convergence
noncomputable section
open Set krylov.Functions
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] {n : ℕ}

/-- The actual value-data budget after separating the oldest anchor from
all newer endpoints. -/
def improvedValueWindowBudget (L₂ L₃ B C r₀ r₁ : ℝ) : ℝ :=
  (L₂+2*B*C+L₃*(4+2*C))*r₁+(L₃/3)*r₀^2

theorem improvedValueWindowBudget_nonneg {L₂ L₃ B C r₀ r₁ : ℝ}
    (hL₂ : 0≤L₂) (hL₃ : 0≤L₃) (hB : 0≤B) (hC : 0≤C) (hr₁ : 0≤r₁) :
    0 ≤ improvedValueWindowBudget L₂ L₃ B C r₀ r₁ := by
  dsimp only [improvedValueWindowBudget]
  positivity

/- The actual diagonal source polynomial has a newer first-order radius
and only an oldest second-order radius. -/
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem value_diagonal_improved_radius_bound {L₂ L₃ B C r₀ r₁ : ℝ}
    (hL₂ : 0≤L₂) (hL₃ : 0≤L₃) (hB : 0≤B) (hC : 0≤C)
    (hr₁ : 0≤r₁) (horder : r₁≤r₀) (hsmall : r₀≤1)
    (a s x : E) (ha : ‖a‖≤r₀) (hb : ‖a+s‖≤r₁) (hx : ‖x‖≤r₁) :
    L₂*‖x‖+B*C*‖x-(a+s)‖+L₃*((1/12:ℝ)*‖s‖^2+
      (1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+(1/2:ℝ)*‖x-(a+s)‖^2)≤
      improvedValueWindowBudget L₂ L₃ B C r₀ r₁ := by
  have hr₀ : 0≤r₀ := hr₁.trans horder
  have hs : ‖s‖≤2*r₀ := by
    have hh := norm_sub_le (a+s) a
    simp only [add_sub_cancel_left] at hh
    exact hh.trans (by linarith only [ha,hb,horder])
  have hd : ‖x-(a+s)‖≤2*r₁ := (norm_sub_le _ _).trans (by linarith only [hx,hb])
  have hs₂ : ‖s‖^2≤4*r₀^2 := by nlinarith only [hs,norm_nonneg s,hr₀]
  have hd₂ : ‖x-(a+s)‖^2≤4*r₁^2 := by nlinarith only [hd,norm_nonneg (x-(a+s)),hr₁]
  have hprod : ‖x-(a+s)‖*‖s‖≤4*r₀*r₁ := by
    have hh := mul_le_mul hd hs (norm_nonneg s) (by positivity : 0≤2*r₁)
    nlinarith only [hh]
  have hcross : r₀*r₁≤r₁ := by nlinarith only [hsmall,hr₁]
  have hnew₂ : r₁^2≤r₁ := by nlinarith only [hr₁,horder,hsmall]
  have hcross' : ‖x-(a+s)‖*‖s‖≤4*r₁ := hprod.trans (by linarith only [hcross])
  have hnew₂' : ‖x-(a+s)‖^2≤4*r₁ := hd₂.trans (by linarith only [hnew₂])
  have hp : (1/12:ℝ)*‖s‖^2+(1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+
      (1/2:ℝ)*‖x-(a+s)‖^2≤r₀^2/3+(4+2*C)*r₁ := by
    have hh := mul_le_mul_of_nonneg_left hcross' (show 0≤(1/2:ℝ)*(1+C) by positivity)
    nlinarith only [hs₂,hnew₂',hh]
  have hfirst := mul_le_mul_of_nonneg_left hx hL₂
  have hsecond := mul_le_mul_of_nonneg_left hd (mul_nonneg hB hC)
  have hthird := mul_le_mul_of_nonneg_left hp hL₃
  dsimp only [improvedValueWindowBudget]
  nlinarith only [hfirst,hsecond,hthird]

/-- The genuine corrected model has the improved first-newer plus
second-oldest error budget, for actual values, gradients and split policy.
No convergence or desired model expansion is assumed. -/
theorem ss1F_source_improved_error_bound
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S) {L₂ L₃ : ℝ≥0}
    (hH : LipschitzOnWith L₂ H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h:E,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    (a s : Fin (n+1) → E) (l : Fin (n+1) → ℝ) (x : E)
    (ha : ∀ i,a i∈S) (hb : ∀ i,a i+s i∈S) (hx : x∈S)
    {r₀ r₁ C B : ℝ} (hr₁ : 0≤r₁) (horder : r₁≤r₀) (hsmall : r₀≤1)
    (hC : 0≤C) (hB : 0≤B) (har : ∀ i,‖a i‖≤r₀)
    (hnew : ∀ i,i≠0 → ‖a i‖≤r₁) (hbr : ∀ i,‖a i+s i‖≤r₁) (hxr : ‖x‖≤r₁)
    (hs : ∀ i,s i≠0)
    (hbudget : ∀ i,∀ h:E,‖h‖=1 → |(T (a i+s i)).form h h h|≤B)
    (hw : ∀ i,‖splitRemainder (a i) (s i) x (l i)‖≤C*‖x-(a i+s i)‖) :
    ‖ss1FNormalizedError f G a s l‖≤((n+1:ℕ):ℝ)*improvedValueWindowBudget L₂ L₃ B C r₀ r₁ := by
  have hε := improvedValueWindowBudget_nonneg (r₀:=r₀) L₂.coe_nonneg L₃.coe_nonneg hB hC hr₁
  have hraw : (L₂:ℝ)*r₁ ≤ improvedValueWindowBudget L₂ L₃ B C r₀ r₁ := by
    dsimp only [improvedValueWindowBudget]
    have hh : 0≤(2*B*C+(L₃:ℝ)*(4+2*C))*r₁+((L₃:ℝ)/3)*r₀^2 := by positivity
    nlinarith only [hh]
  apply ss1FNormalizedError_newer_image_norm f G a s l hs hε
  · intro i hi
    change ‖‖s i‖⁻¹ • (G (a i+s i)-G (a i))-‖s i‖⁻¹ • s i‖≤_
    rw [←smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    have hh := secant_image_endpoint_bound G H S hS h₀ hH hG (a i) (a i+s i) (ha i) (hb i)
    rw [hH₀,ContinuousLinearMap.id_apply,add_sub_cancel_left] at hh
    have hh' : ‖G (a i+s i)-G (a i)-s i‖≤(L₂:ℝ)*r₁*‖s i‖ := hh.trans
      (mul_le_mul_of_nonneg_right (by nlinarith [hnew i hi,hbr i,L₂.coe_nonneg]) (norm_nonneg _))
    apply ((mul_le_mul_of_nonneg_left hh' (inv_nonneg.mpr (norm_nonneg _))).trans_eq ?_).trans hraw
    field_simp [norm_ne_zero_iff.mpr (hs i)]
  · intro i
    exact (ss1F_source_diagonal_bound f G H T S hS h₀ hH hH₀ hf hG hT hLip
      (a i) (s i) x (ha i) (hb i) hx (l i) C B hB (hbudget i) (hw i)).trans
      (mul_le_mul_of_nonneg_right (value_diagonal_improved_radius_bound L₂.coe_nonneg L₃.coe_nonneg
        hB hC hr₁ horder hsmall (a i) (s i) x (har i) (hbr i) hxr) (sq_nonneg _))

end
end krylov.Convergence
