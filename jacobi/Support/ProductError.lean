import jacobi.Support.CouplingBounds

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
Elementary product and positive-square perturbation estimates used to
bound the genuine adjacent top-node solution difference. All original
support inputs are supplied by the proved actual sine-ratio bounds.
Use: topRatio_error inserts the original three shifted support sine quotients and their proved index-dependent errors.
-/
namespace jacobi.Support
noncomputable section
open Real

/-- The product of three original scalar ratios has a quantified first-order error obtained from the same actual factor bounds.
Use: topRatio_error inserts the original three shifted support sine quotients and their proved index-dependent errors.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: expand r1*r2*r3-1 as r1*r2*(r3-1)+r1*(r2-1)+(r1-1), apply the triangle inequality and the genuine factor bounds, then collect the common positive index denominator. -/
theorem product3_error {r₁ r₂ r₃ C₁ C₂ D₁ D₂ D₃ k : ℝ}
    (hC₁:0≤C₁) (hC₂:0≤C₂) (hr₁:|r₁|≤C₁) (hr₂:|r₂|≤C₂)
    (he₁:|r₁-1|≤D₁/k) (he₂:|r₂-1|≤D₂/k) (he₃:|r₃-1|≤D₃/k) :
    |r₁*r₂*r₃-1|≤(C₁*C₂*D₃+C₁*D₂+D₁)/k := by
  -- The exact telescoping product difference avoids assuming that the three original errors have the same sign.
  have ht := (norm_add_le (r₁*r₂*(r₃-1)+r₁*(r₂-1)) (r₁-1)).trans
    (add_le_add (norm_add_le (r₁*r₂*(r₃-1)) (r₁*(r₂-1))) (le_refl ‖r₁-1‖))
  simp only [Real.norm_eq_abs,abs_mul] at ht
  have he : r₁*r₂*(r₃-1)+r₁*(r₂-1)+(r₁-1)=r₁*r₂*r₃-1 := by ring
  rw [he] at ht
  have h₁ := mul_le_mul (mul_le_mul hr₁ hr₂ (abs_nonneg _) hC₁) he₃ (abs_nonneg _) (mul_nonneg hC₁ hC₂)
  have h₂ := mul_le_mul hr₁ he₂ (abs_nonneg _) hC₁
  calc
    _ ≤ _ := ht.trans (add_le_add (add_le_add h₁ h₂) he₁)
    _ = _ := by ring

/-- The difference of genuine nonnegative original wave values is controlled by the exact relative difference of their squares.
Use: topValue_difference converts the original adjacent squared birth/death ratio estimate into the genuine top-node polynomial difference bound.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: divide by the positive original reference value, apply the proved square-root error inequality to the genuine nonnegative quotient, and use its exact original squared-ratio identity. -/
theorem positive_square_difference {u v R : ℝ} (hu:0<u) (hv:0≤v) (hrec:v^2=u^2*R) :
    |v-u|≤u*|R-1| := by
  -- The positive orientation of the original solution is retained; an unsigned square identity alone would not suffice.
  have hq : 0≤v/u := div_nonneg hv hu.le
  have he : (v/u)^2=R := by
    rw [div_pow]
    exact (div_eq_iff (pow_ne_zero 2 hu.ne')).mpr (by nlinarith [hrec])
  have hs := sqrt_error_one (sq_nonneg (v/u))
  rw [Real.sqrt_sq hq,he] at hs
  have hnorm : v-u=u*(v/u-1) := by field_simp [hu.ne']
  rw [hnorm,abs_mul,abs_of_pos hu]
  exact mul_le_mul_of_nonneg_left hs hu.le

end
end jacobi.Support
