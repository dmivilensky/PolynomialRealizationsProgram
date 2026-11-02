import jacobi.Hankel.SmallSine

/-!
Article: jacobi, Lemma E.1.
No asymptotic or root-existence conclusion is assumed: the inputs
are the literal equation and explicit genuine norm bounds.
Use: sine_zero_cubic keeps the three inverse-frequency powers in the true original zero correction.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Every genuine inverse-frequency coefficient retains its full integer inverse-power bound.
Use: sine_zero_cubic keeps the three inverse-frequency powers in the true original zero correction.
Article: jacobi, Lemma E.1.
Proof: apply the complex quotient norm identity and monotonicity of the genuine nonnegative frequency norm power. -/
theorem frequency_quotient_power_bound {c z : ℂ} {A x p : ℝ} (hc : ‖c‖≤A)
    (hx : 0<x) (hz : x≤‖z‖) (hp : 0<p) (n : ℕ) :
    ‖c/((p:ℂ)*z^n)‖≤A/(p*x^n) := by
  rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  have hpow := pow_le_pow_left₀ hx.le hz n
  exact (div_le_div_of_nonneg_left (norm_nonneg c) (mul_pos hp (pow_pos hx n))
    (mul_le_mul_of_nonneg_left hpow hp.le)).trans (div_le_div_of_nonneg_right hc (by positivity))

/-- An actual zero of the sine equation with a cubic genuine residual lies within an explicit inverse-frequency distance of its original grid center.
Use: sine_zero_cubic first obtains the actual small displacement needed for its sharper cubic correction.
Article: jacobi, Lemma E.1.
Proof: rearrange the true equation to isolate sin(zeta). Bound its two original rational corrections using the genuine sine and cosine disk bounds, weaken the actual cubic residual only at this initial step, and use the proved small-sine lower bound. -/
theorem sine_zero_displacement {c q ζ e : ℂ} {B E x : ℝ} (hB : 0≤B) (hE : 0≤E)
    (hc : ‖c‖≤B) (hx : 1≤x) (hz : x≤‖q+ζ‖) (hζ : ‖ζ‖≤1/4)
    (he : ‖e‖≤E/x^3) (hroot : frequencySine c q ζ+e=0) :
    ‖ζ‖≤(B*(B+2)/2+2*B+2*E)/x := by
  -- Only the literal original sine equation is rearranged; no zero estimate is an input.
  have hp : ‖c*(c+2)‖≤B*(B+2) := by
    rw [norm_mul]
    exact mul_le_mul hc ((norm_add_le _ _).trans (by norm_num; exact hc)) (norm_nonneg _) hB
  have h8 := frequency_quotient_bound hp hx hz (by norm_num : (0:ℝ)<8) (n := 2) (by norm_num)
  have h2 := frequency_quotient_bound hc hx hz (by norm_num : (0:ℝ)<2) (n := 1) (by norm_num)
  simp only [pow_one] at h2
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have he' : ‖e‖≤E/x := he.trans (div_le_div_of_nonneg_left hE hxp (le_self_pow₀ hx (by norm_num : (3:ℕ)≠0)))
  have hs : Complex.sin ζ=c*(c+2)/(8*(q+ζ)^2)*Complex.sin ζ+c/(2*(q+ζ))*Complex.cos ζ-e := by
    unfold frequencySine at hroot
    linear_combination hroot
  obtain ⟨hsin,hcos⟩ := trigonometric_quarter_disk hζ
  have hA : ‖c*(c+2)/(8*(q+ζ)^2)*Complex.sin ζ‖≤B*(B+2)/(8*x)*2 := by
    rw [norm_mul]
    exact mul_le_mul h8 hsin (norm_nonneg _) (by positivity)
  have hD : ‖c/(2*(q+ζ))*Complex.cos ζ‖≤B/(2*x)*2 := by
    rw [norm_mul]
    exact mul_le_mul h2 hcos (norm_nonneg _) (by positivity)
  have hsinbound : ‖Complex.sin ζ‖≤B*(B+2)/(8*x)*2+B/(2*x)*2+E/x := by
    rw [hs]
    exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hA hD)) he')
  exact (sine_quarter_linear hζ).1.trans
    ((mul_le_mul_of_nonneg_left hsinbound (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))

/-- The actual small sine zero equation with its genuine cubic residual has the exact original reciprocal-grid correction with a uniform cubic error.
Use: the genuine complex Bessel branches inherit the uniform cubic frequency correction, hence the inverse-square squared-zero error of Lemma E.1.
Article: jacobi, Lemma E.1.
Proof: first derive the actual inverse-frequency displacement from the literal equation. Expand zeta-c/(2*q) as its genuine cubic sine increment, quadratic cosine increment, original second coefficient, reciprocal-frequency replacement and the actual residual. Every original frequency has norm at least x, so all five terms have the same cubic bound. -/
theorem sine_zero_cubic {c q ζ e : ℂ} {B E x : ℝ} (hB : 0≤B) (hE : 0≤E)
    (hc : ‖c‖≤B) (hx : 1≤x) (hq : x≤‖q‖) (hz : x≤‖q+ζ‖) (hζ : ‖ζ‖≤1/4)
    (he : ‖e‖≤E/x^3) (hroot : frequencySine c q ζ+e=0) :
    let K := B*(B+2)/2+2*B+2*E
    ‖ζ-c/(2*q)‖≤(K^3+B*(B+2)*K/4+B*K^2/2+B*K/2+E)/x^3 := by
  -- The actual five error terms are kept separate until their original cubic powers have been bounded.
  let K : ℝ := B*(B+2)/2+2*B+2*E
  have hK : 0≤K := by dsimp [K]; positivity
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hsmall := sine_zero_displacement hB hE hc hx hz hζ he hroot
  change ‖ζ‖≤K/x at hsmall
  have hp : ‖c*(c+2)‖≤B*(B+2) := by
    rw [norm_mul]
    exact mul_le_mul hc ((norm_add_le _ _).trans (by norm_num; exact hc)) (norm_nonneg _) hB
  have h8 := frequency_quotient_power_bound hp hxp hz (by norm_num : (0:ℝ)<8) 2
  have h2 := frequency_quotient_power_bound hc hxp hz (by norm_num : (0:ℝ)<2) 1
  simp only [pow_one] at h2
  have hb1 : ‖ζ-Complex.sin ζ‖≤K^3/x^3 := by
    rw [norm_sub_rev]
    exact (sine_quarter_cubic hζ).trans ((pow_le_pow_left₀ (norm_nonneg _) hsmall 3).trans_eq (by ring))
  have hb2 : ‖c*(c+2)/(8*(q+ζ)^2)*Complex.sin ζ‖≤B*(B+2)*K/(4*x^3) := by
    rw [norm_mul]
    have hs : ‖Complex.sin ζ‖≤2*(K/x) := (sine_quarter_linear hζ).2.trans (by linarith)
    exact (mul_le_mul h8 hs (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hb3 : ‖c/(2*(q+ζ))*(Complex.cos ζ-1)‖≤B*K^2/(2*x^3) := by
    rw [norm_mul]
    have hs : ‖Complex.cos ζ-1‖≤(K/x)^2 := (cosine_quarter_quadratic hζ).trans (pow_le_pow_left₀ (norm_nonneg _) hsmall 2)
    exact (mul_le_mul h2 hs (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hq0 : q≠0 := norm_pos_iff.mp (hxp.trans_le hq)
  have hz0 : q+ζ≠0 := norm_pos_iff.mp (hxp.trans_le hz)
  have hdif : c/(2*(q+ζ))-c/(2*q)= -c*ζ/(2*(q+ζ)*q) := by field_simp; ring
  have hb4 : ‖c/(2*(q+ζ))-c/(2*q)‖≤B*K/(2*x^3) := by
    rw [hdif,norm_div,norm_mul,norm_mul,norm_mul,norm_neg]
    norm_num only [Complex.norm_ofNat]
    have hnum : ‖c‖*‖ζ‖≤B*(K/x) := mul_le_mul hc hsmall (norm_nonneg _) hB
    have hden : 2*x*x≤2*‖q+ζ‖*‖q‖ := mul_le_mul
      (mul_le_mul_of_nonneg_left hz (by norm_num : (0:ℝ)≤2)) hq hxp.le (by positivity)
    exact (div_le_div₀ (mul_nonneg hB (by positivity)) hnum (by positivity) hden).trans_eq (by ring)
  have hident : ζ-c/(2*q)=(ζ-Complex.sin ζ)+
      c*(c+2)/(8*(q+ζ)^2)*Complex.sin ζ+c/(2*(q+ζ))*(Complex.cos ζ-1)+
      (c/(2*(q+ζ))-c/(2*q))-e := by
    unfold frequencySine at hroot
    linear_combination hroot
  change ‖ζ-c/(2*q)‖≤(K^3+B*(B+2)*K/4+B*K^2/2+B*K/2+E)/x^3
  rw [hident]
  exact ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add hb1 hb2)) hb3)) hb4)) he)).trans_eq (by ring)

end
end jacobi.Hankel
