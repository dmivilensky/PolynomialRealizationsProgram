import krylov.Convergence.SS1FModel

/-!
Article: main_krylov, thm:ss1F and cor:xrF.
Use: derive actual corrected diagonal budgets from genuine function,
gradient, Hessian and third variation. In particular, the F-model perturbation
is a conclusion from the real values and splits, not an oracle assumption.
Source: the exact anchored trapezoid remainder and sharp genuine secant FTC.
-/

namespace krylov.Convergence
noncomputable section
open Set krylov.Functions
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/- The actual current Hessian diagonal differs from its limiting canonical
quadratic by the original Hessian Lipschitz budget. -/
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem source_hessian_diagonal_bound (H : E → E →L[ℝ] E) (S : Set E)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (h₀ : (0:E)∈S) (x s : E) (hx : x∈S) :
    |gradientHessian H x s s-‖s‖^2|≤(L:ℝ)*‖x‖*‖s‖^2 := by
  have he : gradientHessian H x s s-‖s‖^2=inner ℝ ((H x-H 0) s) s := by
    simp only [gradientHessian,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
      _root_.sub_apply,inner_sub_left,hH₀,ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
  have hnorm : ‖H x-H 0‖≤(L:ℝ)*‖x‖ := by
    simpa only [sub_zero] using hH.norm_sub_le hx h₀
  rw [he]
  calc
    _ ≤ ‖(H x-H 0) s‖*‖s‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜:=ℝ) ((H x-H 0) s) s
    _ ≤ (‖H x-H 0‖*‖s‖)*‖s‖ := mul_le_mul_of_nonneg_right
      ((H x-H 0).le_opNorm s) (norm_nonneg _)
    _ ≤ ((L:ℝ)*‖x‖*‖s‖)*‖s‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg s)) (norm_nonneg s)
    _ = _ := by ring

/- The actual corrected curvature has its full local source budget against
the true limiting identity, with no model-error premise. -/
omit [CompleteSpace E] in
theorem ss1F_source_diagonal_bound (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (T : E → SymmetricCubic E) (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    {L₂ L₃ : ℝ≥0} (hH : LipschitzOnWith L₂ H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L₃:ℝ)*‖p-q‖)
    (a s x : E) (ha : a∈S) (hb : a+s∈S) (hx : x∈S)
    (l C B : ℝ) (hB : 0≤B)
    (hbudget : ∀ h:E,‖h‖=1 → |(T (a+s)).form h h h|≤B)
    (hw : ‖splitRemainder a s x l‖≤C*‖x-(a+s)‖) :
    |correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-‖s‖^2|≤
      ((L₂:ℝ)*‖x‖+B*C*‖x-(a+s)‖+(L₃:ℝ)*((1/12:ℝ)*‖s‖^2+
        (1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+(1/2:ℝ)*‖x-(a+s)‖^2))*‖s‖^2 := by
  have hh := ss1F_corrected_diagonal_bound f (gradientDifferential G) (gradientHessian H)
    T S hS hf (fun z hz=>gradientDifferential_hasFDerivAt G H z (hG z hz)) hT
    L₃ hLip a s x ha hb hx l C B hB hbudget hw
  have hid : correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-‖s‖^2=
      (correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-gradientHessian H x s s)+
      (gradientHessian H x s s-‖s‖^2) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add hh
    (source_hessian_diagonal_bound H S hH hH₀ h₀ x s hx)).trans_eq (by ring))

/-- The actual function-value diagonal perturbation is small on a shrinking
source window. This is the raw data estimate needed by the XR-F gate. -/
theorem ss1F_source_value_perturbation_bound (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (T : E → SymmetricCubic E) (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    {L₂ L₃ : ℝ≥0} (hH : LipschitzOnWith L₂ H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L₃:ℝ)*‖p-q‖)
    (a s x : E) (ha : a∈S) (hb : a+s∈S) (hx : x∈S)
    (l C B : ℝ) (hB : 0≤B)
    (hbudget : ∀ h:E,‖h‖=1 → |(T (a+s)).form h h h|≤B)
    (hw : ‖splitRemainder a s x l‖≤C*‖x-(a+s)‖) :
    |12*l*segmentValueDefect f (fun z=>innerSL ℝ (G z)) a s|≤
      ((L₂:ℝ)/2*(‖a‖+‖a+s‖)+(L₂:ℝ)*‖x‖+B*C*‖x-(a+s)‖+
        (L₃:ℝ)*((1/12:ℝ)*‖s‖^2+(1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+
          (1/2:ℝ)*‖x-(a+s)‖^2))*‖s‖^2 := by
  have hh := ss1F_source_diagonal_bound f G H T S hS h₀ hH hH₀ hf hG hT hLip
    a s x ha hb hx l C B hB hbudget hw
  have hsec := secant_image_endpoint_bound G H S hS h₀ hH hG a (a+s) ha hb
  rw [hH₀,ContinuousLinearMap.id_apply,add_sub_cancel_left] at hsec
  have hraw : |(gradientDifferential G (a+s)-gradientDifferential G a) s-‖s‖^2|≤
      (L₂:ℝ)/2*(‖a‖+‖a+s‖)*‖s‖^2 := by
    have he : (gradientDifferential G (a+s)-gradientDifferential G a) s-‖s‖^2=
        inner ℝ (G (a+s)-G a-s) s := by
      simp only [gradientDifferential,_root_.sub_apply,innerSL_apply_apply,inner_sub_left,
        real_inner_self_eq_norm_sq]
    rw [he]
    exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans
      ((mul_le_mul_of_nonneg_right hsec (norm_nonneg s)).trans_eq (by ring))
  have he : 12*l*segmentValueDefect f (fun z=>innerSL ℝ (G z)) a s=
      ((gradientDifferential G (a+s)-gradientDifferential G a) s-‖s‖^2)-
      (correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-‖s‖^2) := by
    dsimp only [correctedValueDiagonal,gradientDifferential]
    ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hraw hh).trans_eq (by ring))

end
end krylov.Convergence
