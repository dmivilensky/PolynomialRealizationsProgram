import jacobi.Support.SineProductCorrection

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The original finite rising-factor product is exactly its Gamma quotient
and has the printed normalized power-law constant. The proof reuses
the genuine community Euler Gamma limit already used in jacobi.Reference,
so no Stirling asymptotic is postulated.
Use: sineProduct_gamma and the normalized sine-product asymptotics retain the source's precise Gamma normalization constant.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual positive finite rising-factor quotient is exactly its original Gamma ratio.
Use: sineProduct_gamma and the normalized sine-product asymptotics retain the source's precise Gamma normalization constant.
Article: jacobi, Appendix C.3 (sine-product estimates).
Source: Euler's Gamma recurrence, proved for finite products in jacobi.Reference.gamma_product.
Proof: apply the actual positive finite Gamma product twice, once at s and once at one, then divide the same genuine finite products. -/
theorem risingRatio_gamma {s : ℝ} (hs:0<s) (m : ℕ) :
    (∏j∈Finset.range m,((j:ℝ)+s)/((j:ℝ)+1))=
      Gamma ((m:ℝ)+s)/(Gamma s*Gamma ((m:ℝ)+1)) := by
  -- Positivity of the genuine initial Gamma factor justifies its exact cancellation.
  have hnum := gamma_product hs m
  have hden := gamma_product (by norm_num : (0:ℝ)<1) m
  simp only [Gamma_one,one_mul] at hden
  rw [Finset.prod_div_distrib]
  have hn : (∏j∈Finset.range m,((j:ℝ)+s))=Gamma ((m:ℝ)+s)/Gamma s := by
    apply (eq_div_iff (Gamma_pos_of_pos hs).ne').mpr
    simpa only [add_comm,mul_comm] using hnum.symm
  have hd : (∏j∈Finset.range m,((j:ℝ)+1))=Gamma ((m:ℝ)+1) := by
    simpa only [add_comm] using hden.symm
  rw [hn,hd]
  ring

/-- The actual original sine product has the complete exact printed Gamma-times-smooth-correction factorization.
Use: quantitative smooth-correction control and risingRatio_limit yield the precise original sine-product uniform limit and top-node normalization.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: combine the already proved literal sine-product correction identity with the exact genuine finite Gamma quotient. -/
theorem sineProduct_gamma {N s : ℝ} (hN:0<N) (hs:0<s) (m : ℕ)
    (hjs:∀j<m,(j:ℝ)+s<N) (hj1:∀j<m,(j:ℝ)+1<N) :
    sineProduct (π/N) s m=Gamma ((m:ℝ)+s)/(Gamma s*Gamma ((m:ℝ)+1))*exp (sineCorrection N s m) := by
  rw [sineProduct_correction hN hs m hjs hj1,risingRatio_gamma hs]

/-- The original rising-factor quotient has its exact normalized power-law limit for every positive real shift.
Use: the finite sine-product edge asymptotic combines this exact source Gamma constant with sineCorrection_error.
Article: jacobi, Appendix C.3 (sine-product estimates).
Source: Euler's Gamma limit, already proved in jacobi.Reference.gamma_ratio_limit.
Proof: invert the previously proved genuine Gamma-ratio limit and multiply by the elementary n/(n+s) limit. The exact positive-degree rpow subtraction identity gives the desired original normalization. -/
theorem risingRatio_limit {s : ℝ} (hs:0<s) :
    Tendsto (fun m : ℕ => (m:ℝ)^(1-s)*
      (∏j∈Finset.range m,((j:ℝ)+s)/((j:ℝ)+1))) atTop (𝓝 ((Gamma s)⁻¹)) := by
  -- Only the irrelevant degree-zero term is excluded when simplifying the genuine positive real powers.
  have h := ((gamma_ratio_limit hs).inv₀ (by norm_num)).mul (tendsto_natCast_div_add_atTop s)
  have ht := h.mul_const (Gamma s)⁻¹
  simp only [inv_one,one_mul] at ht
  apply (tendsto_congr' ?_).mpr ht
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hm0 : (0:ℝ)<m := by exact_mod_cast hm
  have hms : (m:ℝ)+s≠0 := ne_of_gt (by linarith)
  have hG : Gamma ((m:ℝ)+1)≠0 := (Gamma_pos_of_pos (by linarith)).ne'
  rw [risingRatio_gamma hs,Real.rpow_sub hm0,Real.rpow_one]
  field_simp [hms,hG,(Real.rpow_pos_of_pos hm0 s).ne']

end
end jacobi.Support
