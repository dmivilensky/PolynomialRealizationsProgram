import jacobi.Support.FrequencyGeometry

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The original frequency/index transition has exact floor and power
bounds. These elementary estimates combine the proved low-frequency
and oscillatory estimates without splitting the endpoint exponent.
Use: the global support envelope turns the genuine imaginary strip b/N into one common finite-propagation bound.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference

/-- The actual n+1 support-chain frequency is at least n throughout the full original parameter range.
Use: the global support envelope turns the genuine imaginary strip b/N into one common finite-propagation bound.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the exact original frequency is n+gamma_alpha+gamma_beta and both exponents are positive. -/
theorem natural_frequency_ge (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    (n:ℝ)≤ jacobi.Jacobi.frequency a b (n+1) := by
  rw [frequency_gamma]
  push_cast
  linarith [(parameter_pos ha hb).1,(parameter_pos ha hb).2.1]

/-- The genuine reciprocal-frequency floor has the source's exact transition comparability.
Use: the support oscillatory envelope takes its actual transition index floor(1/|theta|), whose product with |theta| is bounded below by one and above by 1+|theta|.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: multiply the two defining real floor inequalities by the same strictly positive original frequency modulus. -/
theorem frequency_floor_bounds {t:ℝ} (ht:0<t) :
    1≤t*((Nat.floor (1/t):ℝ)+1) ∧ t*((Nat.floor (1/t):ℝ)+1)≤1+t := by
  have hlo := mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity : 0≤1/t)) ht.le
  have hhi := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one (1/t)) ht
  have hid : t*(1/t)=1 := by field_simp
  constructor <;> nlinarith only [hlo,hhi,hid]

/-- A bounded genuine scaled frequency gives the original endpoint power comparison.
Use: the global support envelope compares its actual transition power with the printed frequency decay for every positive source exponent.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: take the nonnegative exponent of the actual scaled-frequency inequality and divide by the same positive frequency power. -/
theorem frequency_power_bound {t x R g:ℝ} (ht:0<t) (hx:0≤x) (hg:0≤g) (h:t*x≤R) :
    x^g≤R^g*t^(-g) := by
  have hp := rpow_le_rpow (mul_nonneg ht.le hx) h hg
  rw [mul_rpow ht.le hx] at hp
  have hdiv : x^g≤R^g/t^g := (le_div_iff₀ (rpow_pos_of_pos ht g)).mpr (by simpa only [mul_comm] using hp)
  exact hdiv.trans_eq (by rw [div_eq_mul_inv,rpow_neg ht.le])

/-- Beyond the genuine transition frequency, the printed frequency decay is no larger than the original index growth power.
Use: the actual high-frequency support wave bound also implies its source power bound, yielding the exact minimum in Appendix C.3.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: divide the actual positive scaled-frequency inequality and take its nonnegative original exponent. -/
theorem inverse_frequency_power_le {t x g:ℝ} (ht:0<t) (hg:0≤g) (h:1≤t*x) :
    t^(-g)≤x^g := by
  have hinv : 1/t≤x := (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using h)
  calc
    _ = (1/t)^g := by rw [one_div,inv_rpow ht.le,rpow_neg ht.le]
    _ ≤ _ := rpow_le_rpow (by positivity) hinv hg

end
end jacobi.Support
