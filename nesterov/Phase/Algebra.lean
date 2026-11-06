import nesterov.IQC.PolynomialSymbols
import nesterov.Momentum.Rates
import nesterov.Momentum.Parameters

/-!
Article: (factor), (factorgen), (imab) and the phase geometry in §4.
Use: the exact division-free amplitudes of the actual stationary method.
-/
namespace nesterov.Phase
noncomputable section

/-- The basic two-amplitude identity remains valid at every query zero. -/
theorem amplitude_factor (u p : ℂ) :
    ((Complex.normSq u-Complex.normSq p:ℝ):ℂ)-2*Complex.I*(p*star u).im=
      (u-p)*star (u+p) := by
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

/-- Endpoint characteristic polynomials determine the complete spectral pair. -/
theorem stationary_factor (M : StationaryMethod) {μ L : ℝ} (hμL : μ<L) (t : ℝ)
    (c : Spectral.Frequency) :
    ((Spectral.g (M.symbolPair μ L t) c:ℝ):ℂ)-
      2*Complex.I*Spectral.skew (M.symbolPair μ L t) c=
      -(4/((L-μ)^2):ℝ)*M.characteristic μ (polyak.Waves.z t (Real.arccos c))*
        star (M.characteristic L (polyak.Waves.z t (Real.arccos c))) := by
  let z := polyak.Waves.z t (Real.arccos c)
  let U := (M.queryPolynomial.map Complex.ofRealHom).eval z
  let V := (M.recurrencePolynomial.map Complex.ofRealHom).eval z
  let P := ((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z
  have hd : (L:ℂ)-(μ:ℂ)≠0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hμL))
  have hp : P=((L+μ)/(L-μ):ℝ)*U-(2/(L-μ):ℝ)*V := M.normalizedPolynomial_complex_eval μ L z
  have hlow : U-P=(2/(L-μ):ℝ)*M.characteristic μ z := by
    rw [hp,M.characteristic_eq_polynomial_eval]
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
    dsimp [U,V]
    push_cast
    field_simp [hd]
    ring
  have hupp : U+P= -(2/(L-μ):ℝ)*M.characteristic L z := by
    rw [hp,M.characteristic_eq_polynomial_eval]
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
    dsimp [U,V]
    push_cast
    field_simp [hd]
    ring
  change ((Complex.normSq U-Complex.normSq P:ℝ):ℂ)-2*Complex.I*(P*star U).im=_
  rw [amplitude_factor,hlow,hupp,star_mul]
  simp only [star_neg,Complex.star_def,Complex.conj_ofReal]
  push_cast
  dsimp only [z]
  field_simp [hd]
  ring

/-- The original heavy-ball/extrapolation characteristic normalization. -/
theorem momentum_factor {μ L β τ h : ℝ} (hμL : μ<L) (hh : h≠0) (t : ℝ)
    (c : Spectral.Frequency) :
    ((Spectral.g ((Momentum.method β τ h hh).symbolPair μ L t) c:ℝ):ℂ)-
      2*Complex.I*Spectral.skew ((Momentum.method β τ h hh).symbolPair μ L t) c=
      -(4/(h^2*(L-μ)^2):ℝ)*Quadratic.characteristic β τ h μ (polyak.Waves.z t (Real.arccos c))*
        star (Quadratic.characteristic β τ h L (polyak.Waves.z t (Real.arccos c))) := by
  rw [stationary_factor _ hμL,Momentum.method_characteristic,Momentum.method_characteristic,star_mul]
  simp only [star_neg,star_div₀,star_one,Complex.star_def,Complex.conj_ofReal]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hh,
    show (L:ℂ)-(μ:ℂ)≠0 by exact_mod_cast (ne_of_gt (sub_pos.mpr hμL))]

/-- The imaginary cross-characteristic identity before imposing the unit circle. -/
theorem characteristic_cross_im (β τ h μ L : ℝ) (z : ℂ) :
    (Quadratic.characteristic β τ h μ z*star (Quadratic.characteristic β τ h L z)).im=
      h*(L-μ)*z.im*((1-β)+2*τ*(1-z.re)+(1+τ)*(Complex.normSq z-1)) := by
  simp only [Quadratic.characteristic,Quadratic.queryPolynomial,Complex.star_def,
    Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,
    Complex.one_re,Complex.one_im,Complex.normSq_apply]
  ring

theorem characteristic_cross_im_unit (β τ h μ L : ℝ) {z : ℂ} (hz : Complex.normSq z=1) :
    (Quadratic.characteristic β τ h μ z*star (Quadratic.characteristic β τ h L z)).im=
      h*(L-μ)*z.im*((1-β)+2*τ*(1-z.re)) := by
  rw [characteristic_cross_im,hz]
  ring

/-- Equation (imab), including its strict positivity on the upper semicircle. -/
theorem characteristic_cross_im_pos (q : Momentum.Tuning) {μ L : ℝ} (hμL : μ<L)
    {z : ℂ} (hz : Complex.normSq z=1) (hzi : 0<z.im) :
    0<(Quadratic.characteristic q.beta q.tau q.stepSize μ z*
      star (Quadratic.characteristic q.beta q.tau q.stepSize L z)).im := by
  rw [characteristic_cross_im_unit _ _ _ _ _ hz]
  have hzre : z.re≤1 := by
    have hh := Complex.normSq_apply z
    rw [hz] at hh
    nlinarith [sq_nonneg z.im]
  apply mul_pos (mul_pos (mul_pos q.step_pos (sub_pos.mpr hμL)) hzi)
  nlinarith [q.beta_lt_one,mul_nonneg q.tau_nonneg (sub_nonneg.mpr hzre)]

end
end nesterov.Phase
