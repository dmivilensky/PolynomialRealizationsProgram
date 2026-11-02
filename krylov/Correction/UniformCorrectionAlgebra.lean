import krylov.Stability.UniformGram

/-!
Article: main_krylov, thm:UCq, quantitative final correction algebra.
Use: Bound the cubic cost of true basis, model-inverse and first-order-factor
replacements before instantiating them on the original RFC terminal solve.
Source: exact operator telescoping, genuine operator norms and scalar budgets.
-/

namespace krylov.Correction
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine terminal correction product has an exact four-term perturbation split and the corresponding explicit cubic norm allowance.
Use: Assemble the uniform actual RFC second-order response with quantitative constants.
Article: main_krylov, thm:UCq.
Proof: Telescope the actual operator product, keeping both first-order factors. Bound each real operator action separately; first-order coordinate and inverse errors and second-order factor errors all contribute only a cubic budget.
-/
theorem correction_product_error_split (P T N N₀ H : E →L[ℝ] E) (ρ r : E) :
    P (N (H ρ))-T (N₀ r)=
      (P-T) (N (H ρ))+T ((N-N₀) (H ρ))+T (N₀ ((H-ContinuousLinearMap.id ℝ E) ρ))+T (N₀ (ρ-r)) := by
  simp only [_root_.sub_apply,map_sub,ContinuousLinearMap.id_apply]
  abel

/-- The genuine terminal correction product has an exact four-term perturbation split and the corresponding explicit cubic norm allowance.
Use: Assemble the uniform actual RFC second-order response with quantitative constants.
Article: main_krylov, thm:UCq.
Proof: Telescope the actual operator product, keeping both first-order factors. Bound each real operator action separately; first-order coordinate and inverse errors and second-order factor errors all contribute only a cubic budget.
-/
theorem correction_product_cubic_bound (P T N N₀ H : E →L[ℝ] E) (ρ r : E)
    {a b c d e ε : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
    (hε : 0≤ε) (hε1 : ε≤1)
    (hT : ‖T‖≤2) (hP : ‖P-T‖≤2*a*ε)
    (hN : ‖N-N₀‖≤b*ε^2) (hN₀ : ‖N₀‖≤d*ε)
    (hH : ‖H‖≤2) (hH₀ : ‖H-ContinuousLinearMap.id ℝ E‖≤2*a*ε)
    (hρ : ‖ρ-r‖≤c*ε^2) (hr : ‖r‖≤e*ε) :
    ‖P (N (H ρ))-T (N₀ r)‖≤
      (4*a*(d+b)*(e+c)+4*b*(e+c)+4*d*a*(e+c)+2*d*c)*ε^3 := by
  have hρn : ‖ρ‖≤(e+c)*ε := by
    have ht := (norm_le_norm_sub_add ρ r).trans (add_le_add hρ hr)
    have hsq := mul_le_mul_of_nonneg_left hε1 (mul_nonneg hc hε)
    nlinarith only [ht,hsq]
  have hNn : ‖N‖≤(d+b)*ε := by
    have ht := (norm_le_norm_sub_add N N₀).trans (add_le_add hN hN₀)
    have hsq := mul_le_mul_of_nonneg_left hε1 (mul_nonneg hb hε)
    nlinarith only [ht,hsq]
  have h₁ : ‖(P-T) (N (H ρ))‖≤(4*a*(d+b)*(e+c))*ε^3 := by
    calc
      _ ≤ ‖P-T‖*(‖N‖*(‖H‖*‖ρ‖)) := ((P-T).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((N.le_opNorm _).trans (mul_le_mul_of_nonneg_left (H.le_opNorm _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ (2*a*ε)*(((d+b)*ε)*(2*((e+c)*ε))) := by gcongr
      _ = _ := by ring
  have h₂ : ‖T ((N-N₀) (H ρ))‖≤(4*b*(e+c))*ε^3 := by
    calc
      _ ≤ ‖T‖*(‖N-N₀‖*(‖H‖*‖ρ‖)) := (T.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (((N-N₀).le_opNorm _).trans (mul_le_mul_of_nonneg_left (H.le_opNorm _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ 2*((b*ε^2)*(2*((e+c)*ε))) := by gcongr
      _ = _ := by ring
  have h₃ : ‖T (N₀ ((H-ContinuousLinearMap.id ℝ E) ρ))‖≤(4*d*a*(e+c))*ε^3 := by
    calc
      _ ≤ ‖T‖*(‖N₀‖*(‖H-ContinuousLinearMap.id ℝ E‖*‖ρ‖)) := (T.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((N₀.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          ((H-ContinuousLinearMap.id ℝ E).le_opNorm _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ 2*((d*ε)*((2*a*ε)*((e+c)*ε))) := by gcongr
      _ = _ := by ring
  have h₄ : ‖T (N₀ (ρ-r))‖≤(2*d*c)*ε^3 := by
    calc
      _ ≤ ‖T‖*(‖N₀‖*‖ρ-r‖) := (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (N₀.le_opNorm _) (norm_nonneg _))
      _ ≤ 2*((d*ε)*(c*ε^2)) := by gcongr
      _ = _ := by ring
  rw [correction_product_error_split]
  have ht := ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) (le_refl _))) (le_refl _))).trans
      (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄)
  exact ht.trans_eq (by ring)

end
end krylov.Correction
