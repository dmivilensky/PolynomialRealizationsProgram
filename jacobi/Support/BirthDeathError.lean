import jacobi.Support.CenteredError
import jacobi.Support.SineShiftBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
The actual original squared support coupling differs from its free
value by O(m^-2) uniformly throughout the genuine growing half chain.
All centered-quotient hypotheses are discharged from the original
positive sine factors and elementary sine-square bounds.
Use: coupling_error converts this into the printed actual adjacent-coefficient bound |a_m-1/2|<=C/m^2 for the support polynomial oscillatory energy estimate.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The genuine original birth/death product satisfies the complete uniform inverse-square perturbation estimate.
Use: coupling_error converts this into the printed actual adjacent-coefficient bound |a_m-1/2|<=C/m^2 for the support polynomial oscillatory energy estimate.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: use the exact centered original four-sine quotient. Its actual middle sine is at least c*m*h and its two outer denominator sines have the same positive scale. The three genuine small sine squares are bounded by their angle squares, so the proved scalar centered-quotient estimate applies with every premise discharged. -/
theorem birthDeath_error {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,0<m→2*m≤n+6→
      |coefficientA a b n (m-1)*coefficientC a b n m-1|≤C/(m:ℝ)^2 := by
  -- The exact original square quotient is estimated before taking its actual positive square root.
  have hg := parameter_pos ha hb
  obtain ⟨c₀,C₀,hc₀,hC₀,h₀⟩ := shifted_sine_bounds a b (show -1<averageGamma a b-1/2 by linarith [hg.2.2]) 6
  obtain ⟨c₁,C₁,hc₁,hC₁,h₁⟩ := shifted_sine_bounds a b (show -1<averageGamma a b-1 by linarith [hg.2.2]) 6
  obtain ⟨c₂,C₂,hc₂,hC₂,h₂⟩ := shifted_sine_bounds a b (show -1<averageGamma a b by linarith [hg.2.2]) 6
  let P : ℝ := (gamma a-gamma b)/2
  let Q : ℝ := averageGamma a b-1/2
  let K : ℝ := (P^2+Q^2+1/4)/(c₁*c₂)+P^2*Q^2/(c₀^2*(c₁*c₂))
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [h₀,h₁,h₂] with n hn₀ hn₁ hn₂
  intro m hm hmn
  have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hh := hn₀.1
  let u : ℝ := ((m:ℝ)+averageGamma a b-1/2)*step a b n
  have hS : c₀*(m:ℝ)*step a b n≤sin u := by
    simpa only [u,sub_eq_add_neg,add_assoc] using (hn₀.2 m hm hmn).1
  have hL : c₁*(m:ℝ)*step a b n≤sin (u-step a b n/2) := by
    convert (hn₁.2 m hm hmn).1 using 1
    congr 1
    dsimp [u]
    ring
  have hH : c₂*(m:ℝ)*step a b n≤sin (u+step a b n/2) := by
    convert (hn₂.2 m hm hmn).1 using 1
    congr 1
    dsimp [u]
    ring
  have hD : (c₁*c₂)*(m:ℝ)^2*(step a b n)^2≤sin u^2-sin (step a b n/2)^2 := by
    rw [← sine_opposite_product]
    have hHp : 0≤sin (u+step a b n/2) := (by positivity : 0≤c₂*(m:ℝ)*step a b n).trans hH
    convert mul_le_mul hH hL (by positivity) hHp using 1; ring
  have hP : sin (P*step a b n)^2≤P^2*(step a b n)^2 := by
    simpa only [mul_pow] using (Real.sin_sq_le_sq (x:=P*step a b n))
  have hQ : sin (Q*step a b n)^2≤Q^2*(step a b n)^2 := by
    simpa only [mul_pow] using (Real.sin_sq_le_sq (x:=Q*step a b n))
  have hT : sin (step a b n/2)^2≤(1/4:ℝ)*(step a b n)^2 := by
    convert (Real.sin_sq_le_sq (x:=step a b n/2)) using 1; ring
  have herr := centered_quotient_error hm1 hh hc₀ (mul_pos hc₁ hc₂) hS hD
    (sq_nonneg P) (sq_nonneg Q) (by norm_num : (0:ℝ)≤1/4) hP hQ hT
  rw [coupling_centered a b n m hm]
  exact herr.trans (div_le_div_of_nonneg_right (by dsimp [K]; linarith) (sq_nonneg (m:ℝ)))

end
end jacobi.Support
