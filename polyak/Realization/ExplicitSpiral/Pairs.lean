import polyak.Realization.ExplicitSpiral.Data

/-!
Article: initialized-spiral interpolation pairs containing time zero.
Use: independently relate the exact source slacks to the genuine interpolation
radius and discrepancy, before importing any numerical sign certificate.
Proof: expansion of complex coordinates and orthogonality of the scalar repair.
-/

namespace polyak.Realization.ExplicitSpiral
noncomputable section
open Interpolation

/-- Article: a planar initial-pair radius with corrected gradient s+Δ. -/
def pairRadius (s d Z : ℂ) : ℝ :=
  (1/4 : ℝ)*(Complex.normSq (Z-1)-Complex.normSq (s*Z-(s+d)))

/-- Article: a planar initial-pair discrepancy with the unchanged wave values. -/
def pairDiscrepancy (s d Z : ℂ) (b : ℝ) : ℝ :=
  b*Complex.normSq Z-b-(1/2 : ℝ)*inner ℝ (s+d+s*Z) (Z-1)

/-- Article: the correction contributes precisely the source α term and |Δ|²/4. -/
theorem pair_correction (s d Z : ℂ) (b δ : ℝ) :
    pairRadius s d Z+δ*pairDiscrepancy s d Z b=
      pairRadius s 0 Z+δ*pairDiscrepancy s 0 Z b+
        (1/2 : ℝ)*(starRingEnd ℂ d*(s-(δ : ℂ))*(Z-1)).re-
          Complex.normSq d/4 := by
  simp only [pairRadius,pairDiscrepancy,Complex.inner,Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.sub_re,
    Complex.sub_im,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.one_re,Complex.one_im,Complex.zero_re,Complex.zero_im]
  ring

/-- Article: a uniform norm bound for the only changed planar pair. -/
theorem pair_correction_lower (s d Z : ℂ) (b δ : ℝ)
    (hbase : 0≤pairRadius s 0 Z+δ*pairDiscrepancy s 0 Z b) :
    -((‖d‖*(‖s‖+|δ|)*(‖Z‖+1))/2+Complex.normSq d/4) ≤
      pairRadius s d Z+δ*pairDiscrepancy s d Z b := by
  rw [pair_correction]
  have hnorm : ‖starRingEnd ℂ d*(s-(δ : ℂ))*(Z-1)‖ ≤
      ‖d‖*(‖s‖+|δ|)*(‖Z‖+1) := by
    rw [norm_mul,norm_mul,Complex.norm_conj]
    have hs : ‖s-(δ : ℂ)‖≤‖s‖+|δ| := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using norm_sub_le s (δ : ℂ)
    have hZ : ‖Z-1‖≤‖Z‖+1 := by simpa only [norm_one] using norm_sub_le Z (1 : ℂ)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs (norm_nonneg d)) hZ
      (norm_nonneg _) (by positivity)
  have hre := (abs_le.mp (Complex.abs_re_le_norm
    (starRingEnd ℂ d*(s-(δ : ℂ))*(Z-1)))).1
  linarith

/-- Article: positive-time pairs reduce to the unchanged stationary table. -/
theorem untouched_pair {z s : ℂ} {C q : ℝ}
    (hbase : TableFeasible (modePosition z) (modeGradient z s) (modeValue z s C))
    {i j : Option ℕ} (hi : i≠some 0) (hj : j≠some 0) :
    |datumT (position z q) (gradient z s q) (value z s C) i j|≤
      datumR (position z q) (gradient z s q) i j := by
  change |datumT (productPosition _ _) (productGradient _ _ _) (value _ _ _) i j|≤_
  have hv : value z s C=productValue (modeValue z s C)
      (scalarPosition (response 0 (q^2)) 2) 0 := by
    funext a
    simp [value,productValue]
  rw [hv]
  simp only [mul_zero,zero_add]
  change |datumT (productPosition _ _) (productGradient _ _ _) (productValue _ _ _) i j|≤
    datumR (productPosition _ _) (productGradient _ _ _) i j
  rw [datumT_product,datumR_product]
  simp only [correctGradient,hi,hj,↓reduceIte,datumT,datumR] at *
  exact (hbase i j).trans (le_add_of_nonneg_right (by positivity))

end
end polyak.Realization.ExplicitSpiral
