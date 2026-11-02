import jacobi.Reference.ContourDisplacement
import jacobi.Reference.RelativeCharacteristic
import jacobi.Bessel.ProductContinuity
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The actual complete relative spectral product differs from one by
O(R_m^-2). On sufficiently large original energy circles it is
nonzero, so neither characteristic vanishes there and the product is
exactly Delta_sigma/Delta_tau, with its already proved scalar one.
Use: contour_relative_product_bound absorbs the exponential product Lipschitz factor into one fixed constant.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every genuine parity contour radius is larger than one.
Use: contour_relative_product_bound absorbs the exponential product Lipschitz factor into one fixed constant.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: gamma>1/4 gives m+gamma+1/2>3/4, and pi>3. -/
theorem contourRadius_one_lt {a : ℝ} (ha : -1<a) (m : ℕ) : 1<contourRadius a m := by
  have hg := (parameters ha).1
  have hm := Nat.cast_nonneg (α := ℝ) m
  unfold contourRadius
  nlinarith [Real.pi_gt_three]

/-- The actual relative product with the reference spectral denominators, before excluding target zeros.
Use: contour_relative_product_bound proves nonvanishing and then contour_characteristic_product identifies the original characteristic quotient.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def contourProduct (a : ℝ) (ha : -1<a) (z : ℂ) : ℂ :=
  ∏' l:ℕ,(1+((jacobi.Bessel.sigma a ha l:ℂ)-(eigenvalue a l:ℂ))/((eigenvalue a l:ℂ)-z))

/-- The complete genuine relative spectral product is uniformly within C/R_m^2 of one on every original parity contour.
Use: excludes all original target poles on sufficiently large contours and proves the normalized characteristic comparison in contour_characteristic_product.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the actual complete displacement sum is bounded by D/R_m^2
and hence by D. The proved infinite-product Lipschitz estimate against
the constant-one product then bounds the actual difference by exp(D)*D/R_m^2. -/
theorem contour_relative_product_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ m:ℕ,∀ z:ℂ,
      ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖=(contourRadius a m)^2 →
        ‖contourProduct a ha z-1‖≤C/(contourRadius a m)^2 := by
  -- Absolute convergence is proved for the original factors before the product estimate is applied.
  obtain ⟨D,hD,hbound⟩ := contour_displacement_sum_bound ha
  refine ⟨Real.exp D*D,by positivity,fun m z hz => ?_⟩
  obtain ⟨hs,hb⟩ := hbound m z hz
  let d : ℕ → ℂ := fun l =>
    ((jacobi.Bessel.sigma a ha l:ℂ)-(eigenvalue a l:ℂ))/((eigenvalue a l:ℂ)-z)
  have h := jacobi.Bessel.infinite_product_lipschitz d (fun _ => 0) hs (by simp)
  simp only [add_zero,tprod_one,norm_zero,tsum_zero,sub_zero] at h
  have hR : 1≤(contourRadius a m)^2 := by nlinarith [contourRadius_one_lt ha m]
  have hsum : (∑' l:ℕ,‖d l‖)≤D := hb.trans (div_le_self hD.le hR)
  change ‖contourProduct a ha z-1‖≤_
  exact h.trans ((mul_le_mul (Real.exp_le_exp.mpr hsum) hb
    (tsum_nonneg (fun _ => norm_nonneg _)) (Real.exp_pos _).le).trans_eq (by ring))

/-- Where the original contour product is nonzero, no genuine target characteristic zero can occur.
Use: contour_characteristic_product uses the proved original meromorphic product formula only after its genuine pole exclusion has been established.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: every actual target zero is an original sigma_l. At that energy
the corresponding true relative factor vanishes, so the complete product is zero. -/
theorem characteristicSigma_ne_zero_of_contourProduct {a : ℝ} (ha : -1<a) (z : ℂ)
    (hτ : characteristicTau a z≠0) (hP : contourProduct a ha z≠0) : characteristicSigma a z≠0 := by
  -- A target zero supplies a zero product factor only after the reference pole exclusion.
  intro hz
  obtain ⟨l,hl⟩ := (characteristicSigma_zero_iff ha z).mp hz
  have ht : (eigenvalue a l:ℂ)-z≠0 := by
    intro h
    exact hτ ((characteristicTau_zero_iff a z).mpr ⟨l,(sub_eq_zero.mp h).symm⟩)
  apply hP
  unfold contourProduct
  apply tprod_of_exists_eq_zero ⟨l,?_⟩
  rw [← hl]
  field_simp [ht]
  ring

/-- A nonzero actual contour product is exactly the original characteristic quotient, with scalar one.
Use: contour_characteristic_bound transfers the proved product estimate to the same Delta_sigma/Delta_tau used in the article's residue integral.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: reference poles are excluded geometrically, and a nonzero true
product excludes target poles. Both original reciprocal products
converge absolutely and multiply termwise to one. The already proved
relative characteristic formula has its exact original normalization one. -/
theorem contour_characteristic_product {a : ℝ} (ha : -1<a) (m : ℕ) {z : ℂ}
    (hz : ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖=(contourRadius a m)^2)
    (hP : contourProduct a ha z≠0) :
    characteristicSigma a z/characteristicTau a z=contourProduct a ha z := by
  -- Pole exclusions precede every cancellation of the actual printed characteristic functions.
  have hτ := characteristicTau_contour_ne_zero ha m hz
  have hσ := characteristicSigma_ne_zero_of_contourProduct ha z hτ hP
  obtain ⟨C,_,hb⟩ := contour_displacement_sum_bound ha
  have hsmall := (hb m z hz).1
  let P : ℕ → ℂ := fun l =>
    1+((jacobi.Bessel.sigma a ha l:ℂ)-(eigenvalue a l:ℂ))/((eigenvalue a l:ℂ)-z)
  let Q : ℕ → ℂ := fun l => ((eigenvalue a l:ℂ)-z)/((jacobi.Bessel.sigma a ha l:ℂ)-z)
  have hPm : Multipliable P := multipliable_one_add_of_summable hsmall
  have hQm : Multipliable Q := by
    convert! multipliable_one_add_of_summable (relative_perturbation_summable ha z) using 1
    funext l
    have hne : (jacobi.Bessel.sigma a ha l:ℂ)-z≠0 := by
      intro h
      exact hσ ((characteristicSigma_zero_iff ha z).mpr ⟨l,(sub_eq_zero.mp h).symm⟩)
    dsimp [Q]
    field_simp [hne]
    ring
  have hpoint (l : ℕ) : P l*Q l=1 := by
    have ht := contour_denominator_ne_zero ha m l hz
    have hs : (jacobi.Bessel.sigma a ha l:ℂ)-z≠0 := by
      intro h
      exact hσ ((characteristicSigma_zero_iff ha z).mpr ⟨l,(sub_eq_zero.mp h).symm⟩)
    dsimp [P,Q]
    field_simp [ht,hs]
    ring
  have hprod : (∏' l,P l)*(∏' l,Q l)=1 := by
    rw [← hPm.tprod_mul hQm]
    simp only [hpoint,tprod_one]
  rw [← relative_characteristic_product ha z hσ] at hprod
  change contourProduct a ha z*(characteristicTau a z/characteristicSigma a z)=1 at hprod
  apply (div_eq_iff hτ).mpr
  field_simp [hσ] at hprod
  exact hprod.symm

/-- The original contour radii dominate their actual positive index.
Use: contour_characteristic_bound chooses one genuine finite threshold for nonvanishing of the original target characteristic.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: pi>3 and gamma>1/4 imply pi*(m+gamma+1/2)>=m+1 for every nonnegative m. -/
theorem contourRadius_index_le {a : ℝ} (ha : -1<a) (m : ℕ) :
    (m+1:ℝ)≤contourRadius a m := by
  have hg := (parameters ha).1
  have hm := Nat.cast_nonneg (α := ℝ) m
  unfold contourRadius
  nlinarith [Real.pi_gt_three]

/-- The two original characteristics have their uniform O(R_m^-2) relative comparison and matching lower bound on all sufficiently large original parity contours.
Use: with the independent reference Gamma lower bound and the proved true wave bound, this is estimate (iii) in the vanishing contour proof of parity splitting.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the genuine product is uniformly close to one, so it is nonzero
past one fixed index threshold. Its exact quotient identity transfers
the estimate to the original characteristics; the reverse triangle
inequality gives the original lower bound. -/
theorem contour_characteristic_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∃ M:ℕ,∀ m:ℕ,M≤m → ∀ z:ℂ,
      ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖=(contourRadius a m)^2 →
      characteristicSigma a z≠0 ∧
      ‖characteristicSigma a z/characteristicTau a z-1‖≤C/(contourRadius a m)^2 ∧
      ‖characteristicTau a z‖/2≤‖characteristicSigma a z‖ := by
  -- The threshold follows from the actual proved product constant; no finite numerical certificate is assumed.
  obtain ⟨C,hC,hbound⟩ := contour_relative_product_bound ha
  obtain ⟨M,hM⟩ := exists_nat_gt (2*C)
  refine ⟨C,hC,M,fun m hm z hz => ?_⟩
  have hMm : (M:ℝ)≤m := by exact_mod_cast hm
  have hR := contourRadius_one_lt ha m
  have hidx := contourRadius_index_le ha m
  have hs : 2*C≤(contourRadius a m)^2 := by nlinarith
  have hsmall : ‖contourProduct a ha z-1‖≤1/2 :=
    (hbound m z hz).trans ((div_le_iff₀ (sq_pos_of_pos (contourRadius_pos ha m))).mpr (by linarith))
  have hP : contourProduct a ha z≠0 := by
    intro h
    rw [h,zero_sub,norm_neg,norm_one] at hsmall
    norm_num at hsmall
  have hτ := characteristicTau_contour_ne_zero ha m hz
  have hσ := characteristicSigma_ne_zero_of_contourProduct ha z hτ hP
  have he := contour_characteristic_product ha m hz hP
  refine ⟨hσ,?_,?_⟩
  · rw [he]
    exact hbound m z hz
  have hn := norm_sub_norm_le (1:ℂ) (contourProduct a ha z)
  rw [norm_one,norm_sub_rev] at hn
  have hl : (1/2:ℝ)≤‖contourProduct a ha z‖ := by linarith
  rw [← he,norm_div] at hl
  have ht : 0<‖characteristicTau a z‖ := norm_pos_iff.mpr hτ
  have hh := (le_div_iff₀ ht).mp hl
  linarith

end
end jacobi.Reference
