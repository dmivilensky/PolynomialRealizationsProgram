import jacobi.Reference.RelativeNormalization

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The full relative characteristic formula is proved at every complex
energy away from its actual Bessel poles, with the original scalar
proved equal to one. Every infinite product used in the identity has
genuine absolute convergence; the pole exclusion is its natural domain.
Use: proves relative_characteristic_product with convergent products for arbitrary complex energy, beyond the negative-axis comparison.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Away from the actual Bessel poles, the original relative characteristic factors have genuinely summable deviations from one.
Use: proves relative_characteristic_product with convergent products for arbitrary complex energy, beyond the negative-axis comparison.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: for all sufficiently large original indices, sigma_k>=2*|z|,
so |sigma_k-z|>=sigma_k/2. The original bounded spectral displacement
is therefore dominated by a constant times the proved summable first
Bessel trace. The finite original prefix causes no convergence loss. -/
theorem relative_perturbation_summable {a : ℝ} (ha : -1<a) (z : ℂ) :
    Summable (fun k : ℕ => ‖((eigenvalue a k:ℂ)-(jacobi.Bessel.sigma a ha k:ℂ))/
      ((jacobi.Bessel.sigma a ha k:ℂ)-z)‖) := by
  -- The actual first Bessel trace controls the full infinite tail, including at arbitrary nonreal energy.
  obtain ⟨C,hC,herror⟩ := spectrum_error_bounded ha
  have hs : Summable (fun k : ℕ => 2*C/ jacobi.Bessel.sigma a ha k) := by
    convert! (jacobi.Bessel.edgeValue_summable ha).mul_left C using 1
    funext k
    unfold jacobi.Bessel.edgeValue
    ring
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [(jacobi.Bessel.sigma_tendsto ha).eventually (eventually_ge_atTop (2*‖z‖))] with k hk
  have hσ := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)
  have hn : jacobi.Bessel.sigma a ha k-‖z‖≤‖(jacobi.Bessel.sigma a ha k:ℂ)-z‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσ] using
      norm_sub_norm_le (jacobi.Bessel.sigma a ha k:ℂ) z
  have hden : jacobi.Bessel.sigma a ha k/2≤‖(jacobi.Bessel.sigma a ha k:ℂ)-z‖ := by linarith
  have hnum : ‖(eigenvalue a k:ℂ)-(jacobi.Bessel.sigma a ha k:ℂ)‖≤C := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
    exact herror k
  rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),norm_div]
  calc
    _ ≤ C/‖(jacobi.Bessel.sigma a ha k:ℂ)-z‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ C/(jacobi.Bessel.sigma a ha k/2) := div_le_div_of_nonneg_left hC.le (by positivity) hden
    _ = _ := by ring

/-- The two original printed characteristics satisfy their exact relative spectral product with constant one on its full complex domain.
Use: supplies the fully normalized meromorphic comparison for the original rho derivative formula, parity splitting and Proposition C.2.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the true Bessel pole exclusion makes every individual
denominator nonzero. The relative factor perturbations are absolutely
summable. Factor the original reference product into the original
Bessel product, the genuine phase normalization product and the
relative product; their proved true constant is exactly one. -/
theorem relative_characteristic_product {a : ℝ} (ha : -1<a) (z : ℂ)
    (hz : characteristicSigma a z≠0) :
    characteristicTau a z/characteristicSigma a z=
      ∏' k : ℕ,((eigenvalue a k:ℂ)-z)/((jacobi.Bessel.sigma a ha k:ℂ)-z) := by
  -- Every factorization is applied to actual convergent products with the original printed prefactors still present.
  let S : ℕ → ℂ := fun k => (jacobi.Bessel.sigma a ha k:ℂ)/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2)
  let Q : ℕ → ℂ := fun k => 1-z/(jacobi.Bessel.sigma a ha k:ℂ)
  let R : ℕ → ℂ := fun k => ((eigenvalue a k:ℂ)-z)/((jacobi.Bessel.sigma a ha k:ℂ)-z)
  have hnon (k : ℕ) : (jacobi.Bessel.sigma a ha k:ℂ)-z≠0 := by
    intro h
    exact hz ((characteristicSigma_zero_iff ha z).mpr ⟨k,(sub_eq_zero.mp h).symm⟩)
  have hR : Multipliable R := by
    have hh := multipliable_one_add_of_summable (relative_perturbation_summable ha z)
    convert! hh using 1
    funext k
    dsimp [R]
    field_simp [hnon k]
    ring
  have hS : Multipliable S := bessel_phase_ratio_multipliable ha
  have hQ : Multipliable Q := bessel_characteristic_multipliable ha z
  have he (k : ℕ) : ((eigenvalue a k:ℂ)-z)/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2)=
      (S k*Q k)*R k := by
    have hσ : (jacobi.Bessel.sigma a ha k:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
      (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)).ne'
    dsimp [S,Q,R]
    field_simp [hnon k,hσ]
  have hp : (∏' k : ℕ,((eigenvalue a k:ℂ)-z)/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2))=
      ∏' k : ℕ,(S k*Q k)*R k := tprod_congr he
  rw [(hS.mul hQ).tprod_mul hR,hS.tprod_mul hQ] at hp
  have hC : (characteristicSigmaConstant a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (characteristicSigmaConstant_pos ha).ne'
  have hQ0 : (∏' k,Q k)≠0 := by
    intro h
    apply hz
    rw [characteristicSigma,jacobi.Bessel.canonical_product ha]
    change (characteristicSigmaConstant a:ℂ)*(∏' k,Q k)=0
    rw [h,mul_zero]
  rw [characteristicTau_product ha,hp,characteristicSigma,jacobi.Bessel.canonical_product ha]
  change (Complex.Gamma (gamma a:ℂ)^2)⁻¹*((∏' k,S k)*(∏' k,Q k)*(∏' k,R k))/
      ((characteristicSigmaConstant a:ℂ)*(∏' k,Q k))=(∏' k,R k)
  have hc := relativeCharacteristicConstant_eq_one ha
  change (Complex.Gamma (gamma a:ℂ)^2)⁻¹/(characteristicSigmaConstant a:ℂ)*(∏' k,S k)=1 at hc
  calc
    _ = ((Complex.Gamma (gamma a:ℂ)^2)⁻¹/(characteristicSigmaConstant a:ℂ)*(∏' k,S k))*(∏' k,R k) := by
      field_simp [hC,hQ0]
    _ = _ := by rw [hc,one_mul]

end
end jacobi.Reference
