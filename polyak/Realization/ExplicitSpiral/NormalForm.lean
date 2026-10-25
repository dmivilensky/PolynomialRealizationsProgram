import polyak.Realization.ExplicitSpiral.Physical
import polyak.Realization.ExplicitSpiral.QuadraticBounds

/-!
Article: the initialized interpolation slacks have one quadratic plus one
complex oscillation, with the exact independently specified source coefficients.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: the exact complex correction coefficient. -/
def correctionCoefficient (s d : ℂ) (δ : ℝ) : ℂ :=
  ((1/2 : ℝ) : ℂ)*(starRingEnd ℂ d*(s-(δ : ℂ)))

/-- Article: the initialized slack in a phase-free quadratic normal form. -/
theorem pair_normal_form (s d Z : ℂ) (g C δ : ℝ)
    (hg : 1-Complex.normSq s=g) :
    pairRadius s d Z+δ*pairDiscrepancy s d Z ((C+2*s.re)/4)=
      (g+δ*C)/4*Complex.normSq Z+
      (Complex.mk (-g/2+(correctionCoefficient s d δ).re)
        (δ*s.im+(correctionCoefficient s d δ).im)*Z).re+
      ((g-δ*C)/4-(correctionCoefficient s d δ).re-Complex.normSq d/4) := by
  rw [pair_correction]
  simp only [pairRadius,pairDiscrepancy,correctionCoefficient,Complex.inner,
    Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.one_re,Complex.one_im,Complex.zero_re,Complex.zero_im] at *
  linear_combination ((Z.re-1)^2+Z.im^2)/4*hg

/-- Article: the actual complex correction coefficient has the exact rational coordinates. -/
theorem correction_coordinates {r q : ℝ} (hr : 0<r) (hq : 0<q) {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r) (δ : ℝ) :
    (correctionCoefficient (multiplier z q) (defect z q) δ).re=Source.alphaReal r q δ ∧
    (correctionCoefficient (multiplier z q) (defect z q) δ).im=z.im*Source.alphaImag r q δ := by
  obtain ⟨hsr,hsi,hdr,hdi⟩ := multiplier_defect_coordinates hr hq hn hz
  have him := imaginarySquare_eq hn hz
  simp only [correctionCoefficient,Complex.mul_re,Complex.mul_im,Complex.sub_re,
    Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,
    hsr,hsi,hdr,hdi] at *
  constructor
  · unfold Source.alphaReal
    linear_combination Source.defectImag r q*Source.multiplierImag r q/2*him
  · unfold Source.alphaImag
    ring

/-- Article: the actual oscillation coefficient, specified by its rational coordinates. -/
def oscillationCoefficient (r q : ℝ) (z : ℂ) (δ : ℝ) : ℂ :=
  ⟨Source.betaReal r q δ,z.im*Source.betaImag r q δ⟩

/-- Article: the source squared norm is the actual oscillation coefficient norm. -/
theorem normSq_oscillationCoefficient {r q : ℝ} {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r) (δ : ℝ) :
    Complex.normSq (oscillationCoefficient r q z δ)=Source.betaNorm r q δ := by
  simp only [oscillationCoefficient,Complex.normSq_apply,
    ← pow_two,mul_pow,imaginarySquare_eq hn hz]
  rfl

/-- Article: all source coefficients coincide with the actual quadratic normal form. -/
theorem source_normal_coefficients {r q : ℝ} (hr : 0<r) (hq : 0<q) {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r)
    (hF : Spiral.spiralPolynomial r q=0) (δ : ℝ) :
    Source.quadratic r δ=(Source.gap r+δ*physicalValueConstant r)/4 ∧
    oscillationCoefficient r q z δ=
      Complex.mk (-Source.gap r/2+(correctionCoefficient (multiplier z q) (defect z q) δ).re)
        (δ*(multiplier z q).im+(correctionCoefficient (multiplier z q) (defect z q) δ).im) ∧
    Source.constant r q δ=(Source.gap r-δ*physicalValueConstant r)/4-
      (correctionCoefficient (multiplier z q) (defect z q) δ).re-Complex.normSq (defect z q)/4 := by
  obtain ⟨hsr,hsi,hdr,hdi⟩ := multiplier_defect_coordinates hr hq hn hz
  obtain ⟨har,hai⟩ := correction_coordinates hr hq hn hz δ
  have him := imaginarySquare_eq hn hz
  have hd : Complex.normSq (defect z q)=Source.defectNorm r q := by
    simp only [Complex.normSq_apply,← pow_two,hdr,hdi,mul_pow,him]
    rfl
  refine ⟨?_,?_,?_⟩
  · unfold Source.quadratic Source.hyperbolic physicalValueConstant
    field_simp
    ring
  · apply Complex.ext
    · simp only [oscillationCoefficient,har,Source.betaReal]
      unfold Source.hyperbolic Source.lambdaReal
      field_simp
    · simp only [oscillationCoefficient,hsi,hai,Source.betaImag]
      rw [source_multiplierImag_eq hr hq hF]
      ring
  · rw [har,hd]
    unfold Source.constant Source.hyperbolic physicalValueConstant
    field_simp
    ring

/-- Article: actual initialized slacks equal the certified quadratic and oscillation. -/
theorem actual_pair_normal_form {r q : ℝ} (hr : 0<r) (hq : 0<q) {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r)
    (hF : Spiral.spiralPolynomial r q=0) (δ : ℝ) (Z : ℂ) :
    pairRadius (multiplier z q) (defect z q) Z+
      δ*pairDiscrepancy (multiplier z q) (defect z q) Z (Source.valueConstant r q)=
      Source.quadratic r δ*Complex.normSq Z+
        (oscillationCoefficient r q z δ*Z).re+Source.constant r q δ := by
  obtain ⟨ha,hβ,hc⟩ := source_normal_coefficients hr hq hn hz hF δ
  obtain ⟨hsr,_,_,_⟩ := multiplier_defect_coordinates hr hq hn hz
  have hv : Source.valueConstant r q=
      (physicalValueConstant r+2*(multiplier z q).re)/4 := by rw [hsr]; rfl
  rw [hv,pair_normal_form _ _ _ _ _ _ (multiplier_gap hr hq hn hz hF),← ha,← hβ,← hc]

end
end polyak.Realization.ExplicitSpiral
