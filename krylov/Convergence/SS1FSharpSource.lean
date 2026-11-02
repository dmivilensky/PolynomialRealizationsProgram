import krylov.Convergence.SecantThirdVariation
import krylov.Convergence.SS1FSource

/-!
Article: main_krylov, thm:ss1F, sharp original third-order source budgets.
Use: preserve T3, rather than an auxiliary Hessian Lipschitz constant, in
the actual observed corrected diagonal. In particular the estimates remain
valid with T3=0. Source: Banach's proved mixed tensor bound, the genuine
quadratic Hessian Taylor remainder, and the sharp anchored 1/12 kernel.
-/

namespace krylov.Convergence
noncomputable section
open Set krylov.Functions krylov.Tensor
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual canonical Hessian diagonal has the precise T3-linear and
L3-quadratic source budget. -/
theorem source_hessian_cubic_diagonal_bound (H : E → E →L[ℝ] E)
    (T : E → SymmetricCubic E) (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L:ℝ)*‖p-q‖)
    {B : ℝ} (_hB : 0≤B) (hbudget : ∀ h:E,‖h‖=1 → |(T 0).form h h h|≤B)
    (x s : E) (hx : x∈S) :
    |gradientHessian H x s s-‖s‖^2|≤(B*‖x‖+(L:ℝ)/2*‖x‖^2)*‖s‖^2 := by
  have ht := hessian_diagonal_taylor_remainder (gradientHessian H) (fun z=>(T z).form)
    S hS hT L (thirdVariationLipschitzOn_of_diagonal T L S hLip) 0 x s h₀ hx
  have hzero : gradientHessian H 0 s s=‖s‖^2 := by
    simp only [gradientHessian,ContinuousLinearMap.comp_apply,hH₀,ContinuousLinearMap.id_apply,
      innerSL_apply_apply,real_inner_self_eq_norm_sq]
  rw [hzero,sub_zero] at ht
  have hb := cubic_diagonal_bound (T 0) B hbudget x s s
  have he : gradientHessian H x s s-‖s‖^2=
      (gradientHessian H x s s-‖s‖^2-(T 0).form x s s)+(T 0).form x s s := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add ht hb).trans_eq (by ring))

/- The endpoint tensor's actual spectral budget is its original limiting
budget plus the genuine Lipschitz displacement. -/
omit [FiniteDimensional ℝ E] in
theorem source_third_endpoint_budget (T : E → SymmetricCubic E) (S : Set E)
    (h₀ : (0:E)∈S) (L : ℝ≥0)
    (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L:ℝ)*‖p-q‖)
    {B : ℝ} (hbudget : ∀ h:E,‖h‖=1 → |(T 0).form h h h|≤B)
    (b : E) (hb : b∈S) (h : E) (hh : ‖h‖=1) :
    |(T b).form h h h|≤B+(L:ℝ)*‖b‖ := by
  have hl := hLip b hb 0 h₀ h hh
  rw [sub_zero] at hl
  have he : (T b).form h h h=((T b).form h h h-(T 0).form h h h)+(T 0).form h h h := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hl (hbudget h hh)).trans_eq (by ring))

/-- The genuine observed corrected diagonal has the original sharp T3 and
L3/12 coefficients. No auxiliary L2 term is present in this estimate. -/
theorem ss1F_sharp_source_diagonal_bound (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (T : E → SymmetricCubic E) (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L:ℝ)*‖p-q‖)
    {B : ℝ} (hB : 0≤B) (hbudget : ∀ h:E,‖h‖=1 → |(T 0).form h h h|≤B)
    (a s x : E) (ha : a∈S) (hb : a+s∈S) (hx : x∈S) (l C : ℝ)
    (hw : ‖splitRemainder a s x l‖≤C*‖x-(a+s)‖) :
    |correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-‖s‖^2|≤
      (B*‖x‖+(L:ℝ)/2*‖x‖^2+(B+(L:ℝ)*‖a+s‖)*C*‖x-(a+s)‖+
        (L:ℝ)*((1/12:ℝ)*‖s‖^2+(1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+
          (1/2:ℝ)*‖x-(a+s)‖^2))*‖s‖^2 := by
  have hd := ss1F_corrected_diagonal_bound f (gradientDifferential G) (gradientHessian H)
    T S hS hf (fun z hz=>gradientDifferential_hasFDerivAt G H z (hG z hz)) hT L hLip
    a s x ha hb hx l C (B+(L:ℝ)*‖a+s‖) (by positivity)
    (source_third_endpoint_budget T S h₀ L hLip hbudget (a+s) hb) hw
  have hh := source_hessian_cubic_diagonal_bound H T S hS h₀ hH₀ hT L hLip hB hbudget x s hx
  have he : correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-‖s‖^2=
      (correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-gradientHessian H x s s)+
      (gradientHessian H x s s-‖s‖^2) := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hd hh).trans_eq (by ring))

end
end krylov.Convergence
