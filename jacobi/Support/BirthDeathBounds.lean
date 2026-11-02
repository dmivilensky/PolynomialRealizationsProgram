import jacobi.Support.Chain
import jacobi.Support.SineQuotientBounds

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
The actual original support birth/death product has uniform positive
two-sided bounds throughout the whole growing half chain, including
every small positive index. The proof keeps the genuine original
four sine ratios and their proved positive denominator bounds.
Use: birthDeath_bounds applies the already proved uniform positive ratio estimates directly, including the entire actual small-index prefix.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual original birth/death product is the product of four genuine shifted sine ratios at the same positive original row.
Use: birthDeath_bounds applies the already proved uniform positive ratio estimates directly, including the entire actual small-index prefix.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: substitute the literal original A_(m-1),C_m formulas and their exact positive-index cast; only scalar factor reordering remains. -/
theorem birthDeath_product_ratios (a b : ℝ) (n m : ℕ) (hm:0<m) :
    coefficientA a b n (m-1)*coefficientC a b n m=
      (sin (((m:ℝ)+(gamma a-1/2))*step a b n)/sin (((m:ℝ)+(averageGamma a b-1))*step a b n)*
        (sin (((m:ℝ)+(2*averageGamma a b-1))*step a b n)/sin (((m:ℝ)+(averageGamma a b-1/2))*step a b n)))*
      (sin (((m:ℝ)+(0:ℝ))*step a b n)/sin (((m:ℝ)+(averageGamma a b-1/2))*step a b n)*
        (sin (((m:ℝ)+(gamma b-1/2))*step a b n)/sin (((m:ℝ)+averageGamma a b)*step a b n))) := by
  simp only [coefficientA,coefficientC,Nat.cast_sub hm,Nat.cast_one]
  ring_nf

/-- The genuine original squared-coupling birth/death product has uniform positive two-sided bounds throughout the full original growing half-chain range.
Use: coupling_lower supplies the printed actual lower bound a_m>=c, without assuming a numerical check of a finite initial segment.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: all four genuine numerator and denominator shifts exceed minus one in the source parameter range. Their proved positive sine-ratio bounds multiply to the same actual birth/death product. -/
theorem birthDeath_bounds {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,0<m→2*m≤n+6→
      c≤coefficientA a b n (m-1)*coefficientC a b n m ∧
      coefficientA a b n (m-1)*coefficientC a b n m≤C := by
  -- The same ratio estimates cover every actual positive row, with no asymptotic exclusion of small m.
  have hg := parameter_pos ha hb
  obtain ⟨c₁,C₁,hc₁,hC₁,h₁⟩ := sine_quotient_bounds a b
    (show -1<gamma a-1/2 by linarith [hg.1]) (show -1<averageGamma a b-1 by linarith [hg.2.2]) 6
  obtain ⟨c₂,C₂,hc₂,hC₂,h₂⟩ := sine_quotient_bounds a b
    (show -1<2*averageGamma a b-1 by linarith [hg.2.2]) (show -1<averageGamma a b-1/2 by linarith [hg.2.2]) 6
  obtain ⟨c₃,C₃,hc₃,hC₃,h₃⟩ := sine_quotient_bounds a b
    (show (-1:ℝ)<0 by norm_num) (show -1<averageGamma a b-1/2 by linarith [hg.2.2]) 6
  obtain ⟨c₄,C₄,hc₄,hC₄,h₄⟩ := sine_quotient_bounds a b
    (show -1<gamma b-1/2 by linarith [hg.2.1]) (show -1<averageGamma a b by linarith [hg.2.2]) 6
  refine ⟨(c₁*c₂)*(c₃*c₄),(C₁*C₂)*(C₃*C₄),by positivity,by positivity,?_⟩
  filter_upwards [h₁,h₂,h₃,h₄] with n hn₁ hn₂ hn₃ hn₄
  intro m hm hmn
  obtain ⟨hl₁,hu₁⟩ := hn₁ m hm hmn
  obtain ⟨hl₂,hu₂⟩ := hn₂ m hm hmn
  obtain ⟨hl₃,hu₃⟩ := hn₃ m hm hmn
  obtain ⟨hl₄,hu₄⟩ := hn₄ m hm hmn
  have hp₁ := hc₁.le.trans hl₁
  have hp₂ := hc₂.le.trans hl₂
  have hp₃ := hc₃.le.trans hl₃
  have hp₄ := hc₄.le.trans hl₄
  rw [birthDeath_product_ratios a b n m hm]
  constructor
  · exact mul_le_mul (mul_le_mul hl₁ hl₂ hc₂.le hp₁)
      (mul_le_mul hl₃ hl₄ hc₄.le hp₃) (mul_nonneg hc₃.le hc₄.le) (mul_nonneg hp₁ hp₂)
  · exact mul_le_mul (mul_le_mul hu₁ hu₂ hp₂ hC₁.le)
      (mul_le_mul hu₃ hu₄ hp₄ hC₃.le) (mul_nonneg hp₃ hp₄) (mul_nonneg hC₁.le hC₂.le)

end
end jacobi.Support
