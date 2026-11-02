import jacobi.Support.Chain
import jacobi.Support.SineQuotientBounds

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
The actual original initial diagonal is uniformly bounded, including
the exceptional average parameter. Its genuine C_0 boundary is handled
exactly and its two positive A_0 sine ratios have already proved bounds.
Use: diagonal_zero_bound controls the original row zero without dividing by a potentially vanishing lower terminal denominator.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The genuine initial support birth coefficient is the exact product of two positive-index shifted sine ratios.
Use: diagonal_zero_bound controls the original row zero without dividing by a potentially vanishing lower terminal denominator.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: substitute its literal four sine factors; the original positive-index expression is obtained by adding and subtracting one in their exact shifts. -/
theorem coefficientA_zero_ratios (a b : ℝ) (n : ℕ) :
    coefficientA a b n 0=
      (sin (((1:ℝ)+(gamma a-1/2))*step a b n)/sin (((1:ℝ)+(averageGamma a b-1))*step a b n))*
      (sin (((1:ℝ)+(2*averageGamma a b-1))*step a b n)/sin (((1:ℝ)+(averageGamma a b-1/2))*step a b n)) := by
  simp only [coefficientA,Nat.cast_zero,zero_add]
  ring_nf

/-- The actual original initial support diagonal has the full printed uniform bound throughout the source parameter range.
Use: the support recurrence's oscillatory perturbation estimate includes its original boundary normalization with this independently proved bound.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: the actual C_0 is zero. The genuine A_0 is a product of two uniformly positive bounded sine quotients at original row one. The original cosine has absolute value at most one, so the literal initial diagonal is uniformly bounded. -/
theorem diagonal_zero_bound {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,|diagonal a b n 0|≤C := by
  -- The actual boundary zero is used before any quotient cancellation, covering the exceptional original average parameter.
  have hg := parameter_pos ha hb
  obtain ⟨c₁,C₁,hc₁,hC₁,h₁⟩ := sine_quotient_bounds a b
    (show -1<gamma a-1/2 by linarith [hg.1]) (show -1<averageGamma a b-1 by linarith [hg.2.2]) 6
  obtain ⟨c₂,C₂,hc₂,hC₂,h₂⟩ := sine_quotient_bounds a b
    (show -1<2*averageGamma a b-1 by linarith [hg.2.2]) (show -1<averageGamma a b-1/2 by linarith [hg.2.2]) 6
  refine ⟨2+C₁*C₂,by positivity,?_⟩
  filter_upwards [h₁,h₂] with n hn₁ hn₂
  obtain ⟨hl₁,hu₁⟩ := hn₁ 1 (by omega) (by omega)
  obtain ⟨hl₂,hu₂⟩ := hn₂ 1 (by omega) (by omega)
  simp only [Nat.cast_one] at hl₁ hu₁ hl₂ hu₂
  have hp₁ := hc₁.le.trans hl₁
  have hp₂ := hc₂.le.trans hl₂
  have hA0 : 0≤coefficientA a b n 0 := by
    rw [coefficientA_zero_ratios]
    exact mul_nonneg hp₁ hp₂
  have hA : coefficientA a b n 0≤C₁*C₂ := by
    rw [coefficientA_zero_ratios]
    exact mul_le_mul hu₁ hu₂ hp₂ hC₁.le
  rw [diagonal,coefficientC_zero,add_zero]
  calc
    _ ≤ |cos (gamma a*step a b n)|+|coefficientA a b n 0/2| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (cos (gamma a*step a b n)) (coefficientA a b n 0/2)
    _ ≤ 1+(C₁*C₂)/2 := by
      rw [abs_div,abs_of_nonneg hA0]
      exact add_le_add (abs_cos_le_one _) (by norm_num; linarith)
    _ ≤ _ := by nlinarith [mul_pos hC₁ hC₂]

end
end jacobi.Support
