import krylov.Convergence.SecantThirdVariation
import krylov.Convergence.SS1FSource
import krylov.Functions.TrapezoidContinuous

/-!
Article: main_krylov, thm:ss1F, merely continuous third derivatives.
Use: bound the actual corrected model on a genuine source window without
assuming a Lipschitz third derivative or a bound on the split coefficient.
Source: the anchored continuous-D3 trapezoid modulus and the actual (S)
remainder; sharp Riesz/tensor bounds retain the original scalar budget.
-/

namespace krylov.Convergence
noncomputable section
open Set krylov.Functions
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] {p : ℕ}

local instance continuousScalarBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜:=ℝ) (𝕜₂:=ℝ) (E:=E) (F:=E →L[ℝ] ℝ)
local instance continuousScalarBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜:=ℝ) (𝕜₂:=ℝ) (E:=E) (F:=E →L[ℝ] ℝ)
local instance continuousScalarTrilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜:=ℝ) (𝕜₂:=ℝ) (E:=E) (F:=E →L[ℝ] E →L[ℝ] ℝ)
local instance continuousScalarTrilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜:=ℝ) (𝕜₂:=ℝ) (E:=E) (F:=E →L[ℝ] E →L[ℝ] ℝ)

/-- A source-derived finite corrected-diagonal bound under continuous D3.
It is stable for arbitrarily short observed segments and unbounded splits. -/
theorem ss1F_continuous_source_diagonal_bound
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hc : ContinuousOn (fun z=>(T z).form) S)
    {η B : ℝ} (hη : 0≤η) (hB : 0≤B)
    (hmod : ThirdVariationOscillationOn (fun z=>(T z).form) η S)
    (hbudget : ∀ z∈S,∀ u v w,|(T z).form u v w|≤B*‖u‖*‖v‖*‖w‖)
    (a s x : E) (ha : a∈S) (hb : a+s∈S) (hx : x∈S)
    (l C : ℝ) (hw : ‖splitRemainder a s x l‖≤C*‖x-(a+s)‖) :
    |correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-‖s‖^2|≤
      (B*‖x‖+B*C*‖x-(a+s)‖+η*(‖s‖+(2+C)*‖x-(a+s)‖))*‖s‖^2 := by
  have hH := hessian_lipschitz_of_third_spectral_bound H T S hS hT hB (by
    intro z hz u hu
    simpa only [hu,mul_one] using hbudget z hz u u u)
  have hh := anchored_trapezoid_split_continuous f (gradientDifferential G)
    (gradientHessian H) (fun z=>(T z).form) S hS hf
    (fun z hz=>gradientDifferential_hasFDerivAt G H z (hG z hz)) hT hc η hη hmod
    a s x ha hb hx l C B hB hw (hbudget (a+s) hb)
  have hid : correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-‖s‖^2=
      (correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-gradientHessian H x s s)+
      (gradientHessian H x s s-‖s‖^2) := by ring
  rw [hid]
  have hh' : |correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s l-gradientHessian H x s s|≤
      (B*C*‖x-(a+s)‖+η*(‖s‖+(2+C)*‖x-(a+s)‖))*‖s‖^2 := hh
  have hd := source_hessian_diagonal_bound H S hH hH₀ h₀ x s hx
  rw [Real.coe_toNNReal _ hB] at hd
  exact (abs_add_le _ _).trans ((add_le_add hh' hd).trans_eq (by ring))

/-- Continuous-D3 source data control the whole actually observed value
model on an arbitrary rectangular window. -/
theorem ss1F_continuous_normalized_error_bound
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hc : ContinuousOn (fun z=>(T z).form) S)
    {η B : ℝ} (hη : 0≤η) (hB : 0≤B)
    (hmod : ThirdVariationOscillationOn (fun z=>(T z).form) η S)
    (hbudget : ∀ z∈S,∀ u v w,|(T z).form u v w|≤B*‖u‖*‖v‖*‖w‖)
    (a s : Fin p → E) (l : Fin p → ℝ) (x : E)
    (ha : ∀ i,a i∈S) (hb : ∀ i,a i+s i∈S) (hx : x∈S)
    {r C : ℝ} (hr : 0≤r) (hC : 0≤C)
    (har : ∀ i,‖a i‖≤r) (hbr : ∀ i,‖a i+s i‖≤r) (hxr : ‖x‖≤r)
    (hs : ∀ i,s i≠0)
    (hw : ∀ i,‖splitRemainder (a i) (s i) x (l i)‖≤C*‖x-(a i+s i)‖) :
    ‖ss1FNormalizedError f G a s l‖≤p*(B+2*B*C+2*η*(3+C))*r := by
  have hH := hessian_lipschitz_of_third_spectral_bound H T S hS hT hB (by
    intro z hz u hu
    simpa only [hu,mul_one] using hbudget z hz u u u)
  have hε : 0≤(B+2*B*C+2*η*(3+C))*r := by positivity
  apply (ss1FNormalizedError_norm f G a s l hs hε ?_ ?_).trans_eq (by ring)
  · intro i
    apply (unitWindow_image_error s (fun j=>G (a j+s j)-G (a j)) hs ?_ i).trans
      (show B*r≤(B+2*B*C+2*η*(3+C))*r by nlinarith [mul_nonneg (by positivity : 0≤2*B*C+2*η*(3+C)) hr])
    intro j
    have hh := secant_image_endpoint_bound G H S hS h₀ hH hG (a j) (a j+s j) (ha j) (hb j)
    rw [hH₀,ContinuousLinearMap.id_apply,add_sub_cancel_left,Real.coe_toNNReal _ hB] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    nlinarith only [har j,hbr j,hB]
  · intro i
    have hh := ss1F_continuous_source_diagonal_bound f G H T S hS h₀ hH₀ hf hG hT hc
      hη hB hmod hbudget (a i) (s i) x (ha i) (hb i) hx (l i) C (hw i)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hstep : ‖s i‖≤2*r := by
      have hh := norm_sub_le (a i+s i) (a i)
      simp only [add_sub_cancel_left] at hh
      linarith only [hh,har i,hbr i]
    have hdist : ‖x-(a i+s i)‖≤2*r := (norm_sub_le _ _).trans (by linarith only [hxr,hbr i])
    have h₁ := mul_le_mul_of_nonneg_left hxr hB
    have h₂ := mul_le_mul_of_nonneg_left hdist (mul_nonneg hB hC)
    have h₃ := mul_le_mul_of_nonneg_left hdist (show 0≤2+C by positivity)
    have h₄ := mul_le_mul_of_nonneg_left (add_le_add hstep h₃) hη
    nlinarith only [h₁,h₂,h₄]

/-- The oldest raw image disappears from every off-diagonal. The true
continuous-D3 correction therefore leaves only a newer first-order radius
and an arbitrarily small oscillation times the oldest radius. -/
theorem ss1F_continuous_newer_error_bound
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hc : ContinuousOn (fun z=>(T z).form) S)
    {η B : ℝ} (hη : 0≤η) (hB : 0≤B)
    (hmod : ThirdVariationOscillationOn (fun z=>(T z).form) η S)
    (hbudget : ∀ z∈S,∀ u v w,|(T z).form u v w|≤B*‖u‖*‖v‖*‖w‖)
    (a s : Fin (p+1) → E) (l : Fin (p+1) → ℝ) (x : E)
    (ha : ∀ i,a i∈S) (hb : ∀ i,a i+s i∈S) (hx : x∈S)
    {r₀ r₁ C : ℝ} (hr₁ : 0≤r₁) (hC : 0≤C)
    (har : ∀ i,‖a i‖≤r₀) (hnew : ∀ i,i≠0 → ‖a i‖≤r₁)
    (hbr : ∀ i,‖a i+s i‖≤r₁) (hxr : ‖x‖≤r₁)
    (hs : ∀ i,s i≠0)
    (hw : ∀ i,‖splitRemainder (a i) (s i) x (l i)‖≤C*‖x-(a i+s i)‖) :
    ‖ss1FNormalizedError f G a s l‖≤((p+1:ℕ):ℝ)*
      (B*(1+2*C)*r₁+η*(r₀+(5+2*C)*r₁)) := by
  have hr₀ : 0≤r₀ := (norm_nonneg (a 0)).trans (har 0)
  have hH := hessian_lipschitz_of_third_spectral_bound H T S hS hT hB (by
    intro z hz u hu
    simpa only [hu,mul_one] using hbudget z hz u u u)
  have hε : 0≤B*(1+2*C)*r₁+η*(r₀+(5+2*C)*r₁) := by positivity
  apply ss1FNormalizedError_newer_image_norm f G a s l hs hε
  · intro i hi
    have hn : ‖s i‖≠0 := norm_ne_zero_iff.mpr (hs i)
    have hh := secant_image_endpoint_bound G H S hS h₀ hH hG (a i) (a i+s i) (ha i) (hb i)
    rw [hH₀,ContinuousLinearMap.id_apply,add_sub_cancel_left,Real.coe_toNNReal _ hB] at hh
    have hraw : ‖G (a i+s i)-G (a i)-s i‖≤B*r₁*‖s i‖ := hh.trans
      (mul_le_mul_of_nonneg_right (by nlinarith only [hnew i hi,hbr i,hB]) (norm_nonneg _))
    have he : unitWindowImages s (fun j=>G (a j+s j)-G (a j)) i-unitWindow s i=
        ‖s i‖⁻¹ • (G (a i+s i)-G (a i)-s i) := by
      simp only [unitWindowImages,unitWindow,krylov.Methods.rescaleWindow,smul_sub]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    apply (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr (norm_nonneg _))).trans
    have hc : ‖s i‖⁻¹*(B*r₁*‖s i‖)=B*r₁ := by field_simp
    rw [hc]
    nlinarith only [mul_nonneg (mul_nonneg hB hC) hr₁,
      mul_nonneg hη (show 0≤r₀+(5+2*C)*r₁ by positivity)]
  · intro i
    have hh := ss1F_continuous_source_diagonal_bound f G H T S hS h₀ hH₀ hf hG hT hc
      hη hB hmod hbudget (a i) (s i) x (ha i) (hb i) hx (l i) C (hw i)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hstep : ‖s i‖≤r₀+r₁ := by
      have hh := norm_sub_le (a i+s i) (a i)
      simp only [add_sub_cancel_left] at hh
      linarith only [hh,har i,hbr i]
    have hdist : ‖x-(a i+s i)‖≤2*r₁ := (norm_sub_le _ _).trans (by linarith only [hxr,hbr i])
    have h₁ := mul_le_mul_of_nonneg_left hxr hB
    have h₂ := mul_le_mul_of_nonneg_left hdist (mul_nonneg hB hC)
    have h₃ := mul_le_mul_of_nonneg_left hdist (show 0≤2+C by positivity)
    have h₄ := mul_le_mul_of_nonneg_left (add_le_add hstep h₃) hη
    nlinarith only [h₁,h₂,h₄]

end
end krylov.Convergence
