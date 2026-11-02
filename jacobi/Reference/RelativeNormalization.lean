import jacobi.Reference.RelativeNormalizationFactors

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The constant in the relative product of the two original printed
characteristics is proved to equal one. The original genus-zero products
are genuinely factored, and the two separately proved negative-axis
limits fix the remaining scalar without a normalization assumption.
Use: relativeCharacteristicConstant_eq_one proves this original scalar is one, rather than selecting characteristic normalizations to make it one.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- The exact scalar left by factoring the two original canonical products.
Use: relativeCharacteristicConstant_eq_one proves this original scalar is one, rather than selecting characteristic normalizations to make it one.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
-/
def relativeCharacteristicConstant (a : ℝ) (ha : -1<a) : ℂ :=
  (Complex.Gamma (gamma a:ℂ)^2)⁻¹/(characteristicSigmaConstant a:ℂ)*
    ∏' k : ℕ,(jacobi.Bessel.sigma a ha k:ℂ)/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2)

/-- At original negative energy the quotient of the two actual printed characteristics is the genuine relative spectral product times its original unfixed scalar.
Use: relativeCharacteristicConstant_eq_one fixes that exact scalar from the two independently proved negative-axis limits.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: factor each original reference factor as the Bessel phase
ratio, the original Bessel genus-zero factor and the true spectral
displacement factor. All three products are proved multipliable.
The actual B5 shift gap excludes every zero denominator on this path. -/
theorem relative_characteristic_negative_product {a : ℝ} (ha : -1<a) {y : ℝ} (hy : 1≤y) :
    characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)/
      characteristicSigma a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)=
        relativeCharacteristicConstant a ha*
          ∏' k : ℕ,(1+(((eigenvalue a k- jacobi.Bessel.sigma a ha k)/
            (jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2):ℝ):ℂ)) := by
  -- Factor only genuine convergent products of the original spectra, with the original prefactors still visible.
  let z : ℂ := ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)
  let S : ℕ → ℂ := fun k => (jacobi.Bessel.sigma a ha k:ℂ)/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2)
  let Q : ℕ → ℂ := fun k => 1-z/(jacobi.Bessel.sigma a ha k:ℂ)
  let D : ℕ → ℂ := fun k =>
    (((eigenvalue a k- jacobi.Bessel.sigma a ha k)/
      (jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2):ℝ):ℂ)
  have hS : Multipliable S := bessel_phase_ratio_multipliable ha
  have hQ : Multipliable Q := bessel_characteristic_multipliable ha z
  obtain ⟨C,_,hb⟩ := negative_relative_factor_bound ha
  have hs : Summable (fun k : ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  have hD : Summable (fun k => ‖D k‖) := hs.of_nonneg_of_le (fun _ => norm_nonneg _) (hb y hy)
  have hR := multipliable_one_add_of_summable hD
  have he (k : ℕ) : ((eigenvalue a k:ℂ)-z)/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2)=
      (S k*Q k)*(1+D k) := by
    have hσp := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)
    have hg : 0<gamma a := by linarith [(parameters ha).1]
    have hk : 0<(k:ℝ)+gamma a := by positivity
    have hgap : jacobi.Jacobi.endpointCorrection a< jacobi.Bessel.sigma a ha k :=
      jacobi.Bessel.sigma_above_correction ha k
    have hden : 0< jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2 := by
      nlinarith [sq_nonneg y]
    dsimp [S,Q,D,z]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hσp.ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
      show (k:ℂ)+(gamma a:ℂ)≠0 by exact_mod_cast hk.ne',
      show (jacobi.Bessel.sigma a ha k:ℂ)-(jacobi.Jacobi.endpointCorrection a:ℂ)+(y:ℂ)^2≠0 by exact_mod_cast hden.ne']
    ring
  have hp : (∏' k : ℕ,((eigenvalue a k:ℂ)-z)/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2))=
      ∏' k : ℕ,(S k*Q k)*(1+D k) := tprod_congr he
  rw [(hS.mul hQ).tprod_mul hR,hS.tprod_mul hQ] at hp
  have hQ0 : (∏' k,Q k)≠0 := by
    intro hz
    have hc : characteristicSigma a z=0 := by
      rw [characteristicSigma,jacobi.Bessel.canonical_product ha]
      change (characteristicSigmaConstant a:ℂ)*(∏' k,Q k)=0
      rw [hz,mul_zero]
    obtain ⟨k,hk⟩ := (characteristicSigma_zero_iff ha z).mp hc
    have hh := congrArg Complex.re hk
    change jacobi.Jacobi.endpointCorrection a-y^2= jacobi.Bessel.sigma a ha k at hh
    have hgap : jacobi.Jacobi.endpointCorrection a< jacobi.Bessel.sigma a ha k :=
      jacobi.Bessel.sigma_above_correction ha k
    nlinarith [sq_nonneg y]
  change characteristicTau a z/characteristicSigma a z=_
  rw [characteristicTau_product ha,hp,characteristicSigma,jacobi.Bessel.canonical_product ha]
  change (Complex.Gamma (gamma a:ℂ)^2)⁻¹*((∏' k,S k)*(∏' k,Q k)*(∏' k : ℕ,(1+D k)))/
    ((characteristicSigmaConstant a:ℂ)*(∏' k,Q k))=
      ((Complex.Gamma (gamma a:ℂ)^2)⁻¹/(characteristicSigmaConstant a:ℂ)*(∏' k,S k))*(∏' k : ℕ,(1+D k))
  field_simp [hQ0]

/-- The relative normalization constant of the two actual printed characteristics is exactly one.
Use: removes the unproved scalar in the original norming-ratio and parity residue formulas of Appendix C.2 and Proposition C.2.
Article: jacobi, Proposition C.3.
Proof: the genuine factored relative product tends to one by dominated
product convergence, while the quotient of the original characteristics
tends to one by their independently derived exact integral asymptotics.
The same original factored identity therefore has limits k and one;
uniqueness of limits forces the actual constant k to equal one. -/
theorem relativeCharacteristicConstant_eq_one {a : ℝ} (ha : -1<a) :
    relativeCharacteristicConstant a ha=1 := by
  -- Both limiting computations refer to the same proved identity, so an arbitrary entire normalization factor cannot survive.
  have hp := (negative_relative_product_limit ha).const_mul (relativeCharacteristicConstant a ha)
  simp only [mul_one] at hp
  have hq : Tendsto (fun y : ℝ => characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)/
      characteristicSigma a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)) atTop
        (𝓝 (relativeCharacteristicConstant a ha)) := by
    apply hp.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    exact (relative_characteristic_negative_product ha hy).symm
  exact tendsto_nhds_unique hq (characteristic_negative_ratio ha)

/-- The original Bessel-to-reference-phase product equals precisely the Gamma and printed Bessel central normalizations, with no unexplained factor.
Use: cancels the normalization in the original norming-ratio derivative identity.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the proved true relative constant is one; its positive original Gamma and central characteristic factors can be canceled exactly. -/
theorem spectral_normalization_product {a : ℝ} (ha : -1<a) :
    (∏' k : ℕ,(jacobi.Bessel.sigma a ha k:ℂ)/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2))=
      Complex.Gamma (gamma a:ℂ)^2*(characteristicSigmaConstant a:ℂ) := by
  have hh := relativeCharacteristicConstant_eq_one ha
  dsimp [relativeCharacteristicConstant] at hh
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hG : Complex.Gamma (gamma a:ℂ)≠0 := Complex.Gamma_ne_zero_of_re_pos hg
  field_simp [hG,
    Complex.ofReal_ne_zero.mpr (characteristicSigmaConstant_pos ha).ne'] at hh
  linear_combination hh

end
end jacobi.Reference
