import jacobi.Reference.CharacteristicDerivativeProducts

/-!
Article: jacobi, Proposition C.3.
The original defining product rho_k is identified with the genuine
derivative ratio Delta_tau'(tau_k)/Delta_sigma'(sigma_k). The exact
relative characteristic normalization and every omitted-factor product
are proved for the original spectra; neither weight nor derivative is
defined by this identity.
Use: normingRatio_eq_characteristic_derivatives gives the article's exact derivative formula with no unproved normalization or spectral premise.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- The actual original norming product multiplies the true Bessel characteristic derivative to the true reference characteristic derivative.
Use: normingRatio_eq_characteristic_derivatives gives the article's exact derivative formula with no unproved normalization or spectral premise.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: multiply the original rho factors, the genuine omitted Bessel
derivative factors and the proved Bessel-to-phase normalization factors.
Away from k, the original Bessel gap cancels and leaves the omitted
reference derivative factor; at k the remaining scalar is
sigma_k/varpi_k^2. The proved exact normalization product then cancels
every original characteristic prefactor in the two genuine derivatives. -/
theorem characteristic_derivative_norming {a : ℝ} (ha : -1<a) (k : ℕ) :
    deriv (characteristicTau a) (eigenvalue a k:ℂ)=
      (normingRatio a ha k:ℂ)*deriv (characteristicSigma a) (jacobi.Bessel.sigma a ha k:ℂ) := by
  classical
  -- Every sequence below is the original spectral sequence or the actual omitted-factor derivative product.
  let phase : ℕ → ℂ := fun l => (Real.pi:ℂ)^2*((l:ℂ)+(gamma a:ℂ))^2
  let S : ℕ → ℂ := fun l => (jacobi.Bessel.sigma a ha l:ℂ)/phase l
  let N : ℕ → ℂ := fun l => (normingFactor a ha k l:ℂ)
  let Pσ : ℕ → ℂ := fun l => if l=k then 1 else
    ((jacobi.Bessel.sigma a ha l:ℂ)-(jacobi.Bessel.sigma a ha k:ℂ))/(jacobi.Bessel.sigma a ha l:ℂ)
  let Pτ : ℕ → ℂ := fun l => if l=k then 1 else ((eigenvalue a l:ℂ)-(eigenvalue a k:ℂ))/phase l
  let T : ℕ → ℂ := fun l => (N l*Pσ l)*S l
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hphase (l : ℕ) : phase l≠0 := by
    apply mul_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    apply pow_ne_zero
    exact_mod_cast (ne_of_gt (show 0<(l:ℝ)+gamma a by positivity))
  have hσ (l : ℕ) : (jacobi.Bessel.sigma a ha l:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha l)).ne'
  have hn : HasProd N (normingRatio a ha k:ℂ) := by
    convert! (normingRatio_properties ha k).1.map Complex.ofRealHom Complex.continuous_ofReal using 1
  have hmσ : Multipliable Pσ := by
    have hh := jacobi.Complex.affine_omit_product_multipliable (inverse_sigma_summable ha) 0
      (jacobi.Bessel.sigma a ha k:ℂ) k
    convert! hh using 1
    funext l
    dsimp [Pσ]
    split_ifs
    · rfl
    · field_simp [hσ l]; ring
  have hmτ : Multipliable Pτ := by
    have hh := jacobi.Complex.affine_omit_product_multipliable (inverse_phase_summable ha)
      (jacobi.Jacobi.endpointCorrection a:ℂ) (eigenvalue a k:ℂ) k
    convert! hh using 1
    funext l
    dsimp [Pτ,phase]
    split_ifs
    · rfl
    · unfold eigenvalue
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
        show (l:ℂ)+(gamma a:ℂ)≠0 by exact_mod_cast (ne_of_gt (show 0<(l:ℝ)+gamma a by positivity))]
      ring
  have hmS : Multipliable S := bessel_phase_ratio_multipliable ha
  -- Away from the omitted index, the actual nonzero Bessel gap cancels inside each of the original factors.
  have hoff (l : ℕ) (hl : l≠k) : T l=Pτ l := by
    have hgap : (jacobi.Bessel.sigma a ha l:ℂ)-(jacobi.Bessel.sigma a ha k:ℂ)≠0 := by
      rw [← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ((jacobi.Bessel.sigma_strictMono ha).injective.ne hl))
    dsimp [T,N,Pσ,S,Pτ]
    rw [ite_eq_right hl,ite_eq_right hl,normingFactor,ite_eq_right hl]
    push_cast
    field_simp [hσ l,hgap]
  have hup : Multipliable (Function.update T k 1) := by
    convert! hmτ using 1
    funext l
    by_cases hl : l=k
    · simp [hl,Pτ]
    · rw [Function.update_of_ne hl]
      exact hoff l hl
  -- Multiply the three genuinely convergent original products, then extract their one remaining diagonal factor.
  have hleft : (∏' l,T l)=((normingRatio a ha k:ℂ)*(∏' l,Pσ l))*(∏' l,S l) := by
    rw [(hn.multipliable.mul hmσ).tprod_mul hmS,hn.multipliable.tprod_mul hmσ,hn.tprod_eq]
  have hrest : (∏' l : ℕ,if l=k then 1 else T l)=∏' l,Pτ l := by
    apply tprod_congr
    intro l
    by_cases hl : l=k
    · simp [hl,Pτ]
    · simp only [hl,ite_false]
      exact hoff l hl
  have hTk : T k=S k := by simp [T,N,Pσ,normingFactor]
  have hprod := Multipliable.tprod_eq_mul_tprod_ite' k hup
  rw [hleft,hrest,hTk] at hprod
  -- The independently proved true phase-normalization product cancels the printed characteristic prefactors exactly.
  have hSprod : (∏' l,S l)=Complex.Gamma (gamma a:ℂ)^2*(characteristicSigmaConstant a:ℂ) :=
    spectral_normalization_product ha
  rw [hSprod] at hprod
  dsimp only [S] at hprod
  field_simp [hphase k] at hprod
  rw [characteristicTau_derivative_product ha,characteristicSigma_derivative_product ha]
  change -(Complex.Gamma (gamma a:ℂ)^2)⁻¹/phase k*(∏' l,Pτ l)=
    (normingRatio a ha k:ℂ)*(-(characteristicSigmaConstant a:ℂ)/(jacobi.Bessel.sigma a ha k:ℂ)*(∏' l,Pσ l))
  have hΓ : Complex.Gamma (gamma a:ℂ)≠0 := Complex.Gamma_ne_zero_of_re_pos hg
  field_simp [hΓ,hσ k,hphase k]
  linear_combination hprod

/-- The original defining spectral-gap norming product is exactly the genuine derivative ratio of the two original printed characteristics.
Use: supplies the original reciprocal-derivative spectral weights in parity splitting, the transformed midpoint normalization and Proposition C.2.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: characteristic_derivative_norming proves the actual product
identity. The Bessel spectral zero is genuinely simple, so its actual
characteristic derivative is nonzero and division is legitimate. -/
theorem normingRatio_eq_characteristic_derivatives {a : ℝ} (ha : -1<a) (k : ℕ) :
    (normingRatio a ha k:ℂ)=deriv (characteristicTau a) (eigenvalue a k:ℂ)/
      deriv (characteristicSigma a) (jacobi.Bessel.sigma a ha k:ℂ) := by
  have hnon := characteristicSigma_simple ha
    ((characteristicSigma_zero_iff ha _).mpr ⟨k,rfl⟩)
  apply (eq_div_iff hnon).mpr
  exact (characteristic_derivative_norming ha k).symm

end
end jacobi.Reference
