import polyak.Realization.ExplicitSpiral.Powers

/-!
Article: finite rational initial slacks are the genuine complex interpolation slacks.
Use: numerical certificates apply to the actual Y=2 trajectory.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: the initialized multiplier's gradient at every positive time. -/
theorem gradient_coordinates {r q : ℝ} (hr : 0<r) (hq : 0<q) {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r) (k : ℕ) :
    (multiplier z q*z^k).re=Source.gradientReal r q k ∧
    (multiplier z q*z^k).im=z.im*Source.gradientImag r q k := by
  obtain ⟨hsr,hsi,_,_⟩ := multiplier_defect_coordinates hr hq hn hz
  obtain ⟨hpr,hpi⟩ := power_coordinates hr hn hz k
  have him := imaginarySquare_eq hn hz
  constructor
  · simp only [Complex.mul_re,hsr,hsi,hpr,hpi,Source.gradientReal]
    linear_combination -Source.multiplierImag r q*Source.powerImag r k*him
  · simp only [Complex.mul_im,hsr,hsi,hpr,hpi,Source.gradientImag]
    ring

/-- Article: the power norm is exactly the radial power. -/
theorem normSq_power {r : ℝ} {z : ℂ} (hn : Complex.normSq z=r^2) (k : ℕ) :
    Complex.normSq (z^k)=r^(2*k) := by
  rw [map_pow,hn,← pow_mul]

/-- Article: exact equality of the corrected initial-pair radius. -/
theorem pairRadius_eq_source {r q : ℝ} (hr : 0<r) (hq : 0<q) {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r) (k : ℕ) :
    pairRadius (multiplier z q) (defect z q) (z^k)=Source.radius r q k := by
  obtain ⟨hsr,hsi,hdr,hdi⟩ := multiplier_defect_coordinates hr hq hn hz
  obtain ⟨hpr,hpi⟩ := power_coordinates hr hn hz k
  obtain ⟨hgr,hgi⟩ := gradient_coordinates hr hq hn hz k
  have him := imaginarySquare_eq hn hz
  simp only [pairRadius,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,sub_zero,
    hpr,hpi,hgr,hgi,hsr,hsi,hdr,hdi,Source.radius]
  linear_combination
    ((Source.powerImag r k)^2-(Source.gradientImag r q k-
      (Source.multiplierImag r q+Source.defectImag r q))^2)/4*him

/-- Article: exact equality of the corrected initial-pair discrepancy. -/
theorem pairDiscrepancy_eq_source {r q : ℝ} (hr : 0<r) (hq : 0<q) {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r) (k : ℕ) :
    pairDiscrepancy (multiplier z q) (defect z q) (z^k) (Source.valueConstant r q)=
      Source.discrepancy r q k := by
  obtain ⟨hsr,hsi,hdr,hdi⟩ := multiplier_defect_coordinates hr hq hn hz
  obtain ⟨hpr,hpi⟩ := power_coordinates hr hn hz k
  obtain ⟨hgr,hgi⟩ := gradient_coordinates hr hq hn hz k
  have him := imaginarySquare_eq hn hz
  simp only [pairDiscrepancy,normSq_power hn,Complex.inner,Complex.mul_re,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.conj_re,
    Complex.conj_im,Complex.one_re,Complex.one_im,sub_zero,hpr,hpi,hgr,hgi,
    hsr,hsi,hdr,hdi,Source.discrepancy]
  linear_combination
    -(Source.multiplierImag r q+Source.defectImag r q+Source.gradientImag r q k)*
      Source.powerImag r k/2*him

end
end polyak.Realization.ExplicitSpiral
