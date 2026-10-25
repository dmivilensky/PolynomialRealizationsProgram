import polyak.Realization.ExplicitSpiral.Source

/-!
Article: exact algebra underlying the initialized-spiral finite sign table.
Use: connect the independently specified rational source formulas to genuine
complex gradients and interpolation quantities, before using literal witnesses.
Proof: real and imaginary coordinates, the exact radial norm, and field identities.
-/

namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: factoring out Im λ retains its exact square. -/
theorem imaginarySquare_eq {r : ℝ} {z : ℂ} (hn : Complex.normSq z=r^2)
    (hr : z.re=Source.lambdaReal r) : z.im^2=Source.imaginarySquare r := by
  rw [Complex.normSq_apply,hr] at hn
  unfold Source.imaginarySquare
  linarith

/-- Article: the actual multiplier and first-gradient defect have the source coordinates. -/
theorem multiplier_defect_coordinates {r q : ℝ} (hr : 0<r) (hq : 0<q) {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r) :
    (multiplier z q).re=Source.multiplierReal r q ∧
    (multiplier z q).im=z.im*Source.multiplierImag r q ∧
    (defect z q).re=Source.defectReal r q ∧
    (defect z q).im=z.im*Source.defectImag r q := by
  have hrd : r^2+1≠0 := by positivity
  have hr0 := hr.ne'
  have hq0 := hq.ne'
  have hm : multiplier z q=(z+((q^2 : ℝ) : ℂ)/z)/((2*q : ℝ) : ℂ) := by
    simp [multiplier]
  have hd : defect z q=((q/2 : ℝ) : ℂ)*(1-z⁻¹) := by
    simp [defect]
  constructor
  · rw [hm]
    simp only [Complex.add_re,Complex.div_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,Complex.normSq_ofReal,hn,hz]
    unfold Source.lambdaReal Source.multiplierReal
    field_simp
    ring
  · constructor
    · rw [hm]
      simp only [Complex.add_im,Complex.div_im,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,Complex.normSq_ofReal,hn]
      unfold Source.multiplierImag
      field_simp
      ring
    · constructor
      · rw [hd]
        simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
          Complex.sub_re,Complex.one_re,Complex.inv_re,hn,hz]
        unfold Source.lambdaReal Source.defectReal
        field_simp
        ring
      · rw [hd]
        simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
          Complex.sub_im,Complex.one_im,Complex.inv_im,hn]
        unfold Source.defectImag
        field_simp
        ring

end
end polyak.Realization.ExplicitSpiral
