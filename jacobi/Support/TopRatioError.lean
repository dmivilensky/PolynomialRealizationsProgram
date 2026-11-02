import jacobi.Support.TopRatio
import jacobi.Support.ProductError
import jacobi.Support.SineQuotientBounds

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The actual original adjacent top-node squared ratio differs from one
by O(1/(m+1)), uniformly on the entire original growing half chain.
All factor bounds come from the genuine shifted sine quotients.
Use: topValue_difference combines this actual original ratio bound with the genuine positive top-node power growth.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The original birth/death ratio governing the actual adjacent top-node squares has the complete printed first-order index error.
Use: topValue_difference combines this actual original ratio bound with the genuine positive top-node power growth.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the proved exact ratio is the product of three genuine shifted sine quotients at original index m+1. Each has the proved O(1/(m+1)) error, and the first two have uniform genuine bounds. Apply the exact three-factor perturbation estimate with these same actual original factors. -/
theorem topRatio_error {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+6→
      |coefficientA a b (n+1) m/coefficientC a b (n+1) (m+1)-1|≤C/((m:ℝ)+1) := by
  -- One original positive index m+1 is used for all three actual ratios, including m=0.
  have hg := parameter_pos ha hb
  obtain ⟨c₁,C₁,hc₁,hC₁,h₁⟩ := sine_quotient_bounds a b
    (show -1<gamma a-1/2 by linarith [hg.1]) (show -1<gamma b-1/2 by linarith [hg.2.1]) 8
  obtain ⟨c₂,C₂,hc₂,hC₂,h₂⟩ := sine_quotient_bounds a b
    (show -1<2*averageGamma a b-1 by linarith [hg.2.2]) (show (-1:ℝ)<0 by norm_num) 8
  obtain ⟨D₁,hD₁,he₁⟩ := sine_quotient_error a b (p:=gamma a-1/2)
    (show -1<gamma b-1/2 by linarith [hg.2.1]) 8
  obtain ⟨D₂,hD₂,he₂⟩ := sine_quotient_error a b (p:=2*averageGamma a b-1) (show (-1:ℝ)<0 by norm_num) 8
  obtain ⟨D₃,hD₃,he₃⟩ := sine_quotient_error a b (p:=averageGamma a b)
    (show -1<averageGamma a b-1 by linarith [hg.2.2]) 8
  refine ⟨C₁*C₂*D₃+C₁*D₂+D₁,by positivity,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually h₁,(tendsto_add_atTop_nat 1).eventually h₂,
    (tendsto_add_atTop_nat 1).eventually he₁,(tendsto_add_atTop_nat 1).eventually he₂,
    (tendsto_add_atTop_nat 1).eventually he₃,eventually_ge_atTop (8:ℕ)] with n hn₁ hn₂ hn₃ hn₄ hn₅ hlarge
  intro m hm
  have hm' : m<n := by omega
  have hmn : 2*(m+1)≤n+1+8 := by omega
  obtain ⟨hl₁,hu₁⟩ := hn₁ (m+1) (by omega) hmn
  obtain ⟨hl₂,hu₂⟩ := hn₂ (m+1) (by omega) hmn
  have hd₁ := hn₃ (m+1) (by omega) hmn
  have hd₂ := hn₄ (m+1) (by omega) hmn
  have hd₃ := hn₅ (m+1) (by omega) hmn
  simp only [Nat.cast_add,Nat.cast_one,add_zero] at hl₁ hu₁ hl₂ hu₂ hd₁ hd₂ hd₃
  have hr₁ : |sin (((m:ℝ)+1+(gamma a-1/2))*step a b (n+1))/
      sin (((m:ℝ)+1+(gamma b-1/2))*step a b (n+1))|≤C₁ := by
    rw [abs_of_nonneg (hc₁.le.trans hl₁)]
    exact hu₁
  have hr₂ : |sin (((m:ℝ)+1+(2*averageGamma a b-1))*step a b (n+1))/
      sin (((m:ℝ)+1)*step a b (n+1))|≤C₂ := by
    rw [abs_of_nonneg (hc₂.le.trans hl₂)]
    exact hu₂
  rw [topRatio_product ha hb hm']
  exact product3_error hC₁.le hC₂.le hr₁ hr₂ hd₁ hd₂ hd₃

end
end jacobi.Support
