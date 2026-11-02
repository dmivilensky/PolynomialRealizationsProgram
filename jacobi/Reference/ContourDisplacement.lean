import jacobi.Reference.ContourGeometry

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The literal displacement factors (sigma_l-tau_l)/(tau_l-z) have
an absolutely summable majorant whose complete sum is O(R_m^-2),
uniformly on the original energy circles. Only the already proved
McMahon displacement and elementary quadratic-gap inequalities enter.
Use: contour_factor_bound pairs the original McMahon numerator with the exact radial reference denominator.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original spectral displacement is bounded on the genuine reference-frequency scale.
Use: contour_factor_bound pairs the original McMahon numerator with the exact radial reference denominator.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: k+gamma<=max(1,gamma)*(k+1), so the proved original index-square bound is also a shifted-frequency-square bound. -/
theorem displacement_phase_bound {a : ℝ} (ha : -1<a) :
    ∃ D : ℝ,0<D ∧ ∀ l:ℕ,
      |jacobi.Bessel.sigma a ha l-eigenvalue a l|≤D/((l:ℝ)+gamma a)^2 := by
  -- The fixed positive comparison factor includes every genuine small spectral index.
  obtain ⟨C,hC,herror⟩ := spectrum_error ha
  let L := max 1 (gamma a)
  have hL : 1≤L := le_max_left _ _
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  refine ⟨C*L^2,by positivity,fun l => (herror l).trans ?_⟩
  have hy : 0<(l:ℝ)+gamma a := by positivity
  have hl : (l:ℝ)+gamma a≤L*(l+1) := by
    have hn := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg (α := ℝ) l)
    have hh : gamma a≤L := le_max_right _ _
    nlinarith
  have hs := (sq_le_sq₀ hy.le (by positivity : 0≤L*(l+1:ℝ))).mpr hl
  apply (div_le_div_iff₀ (by positivity : 0<(l+1:ℝ)^2) (sq_pos_of_pos hy)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hs hC.le]

/-- Every original relative spectral displacement factor has a uniform summable contour majorant.
Use: contour_displacement_sum_bound proves the full O(R_m^-2) comparison of the genuine characteristic products.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the exact radial quadratic gap bounds the actual complex
denominator. The positive-index displacement bound and the elementary
quadratic-gap majorant give a shifted p-series plus a half-integer distance series. -/
theorem contour_factor_bound {a : ℝ} (ha : -1<a) {D : ℝ} (hD : 0<D)
    (he : ∀ l:ℕ,|jacobi.Bessel.sigma a ha l-eigenvalue a l|≤D/((l:ℝ)+gamma a)^2)
    (m l : ℕ) {z : ℂ}
    (hz : ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖=(contourRadius a m)^2) :
    ‖((jacobi.Bessel.sigma a ha l:ℂ)-(eigenvalue a l:ℂ))/((eigenvalue a l:ℂ)-z)‖≤
      D/(contourRadius a m)^2*(2/((l:ℝ)+gamma a)^2+3*halfDistanceMajorant m l) := by
  -- The nonzero denominator is established geometrically for the actual original contour.
  let x : ℝ := (m:ℝ)+gamma a+1/2
  let y : ℝ := (l:ℝ)+gamma a
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hx : 0<x := by dsimp [x]; positivity
  have hy : 0<y := by dsimp [y]; positivity
  have hne : y≠x := by
    intro h
    exact halfDistance_ne_zero m l (by dsimp [x,y] at h; linarith)
  have hq : 0 < |y^2-x^2| := abs_pos.mpr (by
    intro h
    have hh : y=x := by nlinarith [sub_eq_zero.mp h]
    exact hne hh)
  have hden : 0<‖(eigenvalue a l:ℂ)-z‖ := norm_pos_iff.mpr (contour_denominator_ne_zero ha m l hz)
  have hnum : ‖(jacobi.Bessel.sigma a ha l:ℂ)-(eigenvalue a l:ℂ)‖≤D/y^2 := by
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,y] using he l
  have hfirst := div_le_div₀ (show 0≤D/y^2 by positivity) hnum
    (mul_pos (sq_pos_of_pos Real.pi_pos) hq) (contour_denominator_lower ha m l hz)
  have haux := quadratic_gap_inverse_majorant hx hy hne
  have hadd : 1/y^2≤1/x^2+1/y^2 := by linarith [one_div_nonneg.mpr (sq_nonneg x)]
  have hrel := (div_le_div_of_nonneg_right hadd hq.le).trans haux
  have hbound := mul_le_mul_of_nonneg_left hrel (show 0≤D/Real.pi^2 by positivity)
  have hd : halfDistanceMajorant m l=1/(y-x)^2 := by
    unfold halfDistanceMajorant x y
    congr 2
    ring
  rw [norm_div]
  apply hfirst.trans
  convert hbound using 1
  · simp only [div_eq_mul_inv,mul_inv]; ring
  · rw [hd]
    have hR : (contourRadius a m)^2=Real.pi^2*x^2 := by dsimp [contourRadius,x]; ring
    rw [hR]
    change D/(Real.pi^2*x^2)*(2/y^2+3*(1/(y-x)^2))=
      D/Real.pi^2*((2/y^2+3/(y-x)^2)/x^2)
    simp only [div_eq_mul_inv,mul_inv]
    ring

/-- The genuine complete relative displacement sum on every original parity contour is bounded by C/R_m^2.
Use: contour_relative_product_bound obtains the correctly normalized characteristic comparison needed for the vanishing parity contour integral.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: both parts of the pointwise majorant are genuinely summable.
The shifted reference p-series has fixed mass and the translated
half-integer p-series has a center-independent bound; sum the actual original factors. -/
theorem contour_displacement_sum_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ m:ℕ,∀ z:ℂ,
      ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖=(contourRadius a m)^2 →
      Summable (fun l:ℕ => ‖((jacobi.Bessel.sigma a ha l:ℂ)-(eigenvalue a l:ℂ))/
        ((eigenvalue a l:ℂ)-z)‖) ∧
      (∑' l:ℕ,‖((jacobi.Bessel.sigma a ha l:ℂ)-(eigenvalue a l:ℂ))/
        ((eigenvalue a l:ℂ)-z)‖)≤C/(contourRadius a m)^2 := by
  -- No large-contour exception is needed for this factor sum: all reference poles are already separated.
  obtain ⟨D,hD,he⟩ := displacement_phase_bound ha
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hs := shifted_inverse_square_summable hg
  let S : ℝ := ∑' l:ℕ,1/((l:ℝ)+gamma a)^2
  let T : ℝ := ∑' l:ℕ,1/(l+1:ℝ)^2
  have hS : 0≤S := tsum_nonneg (fun _ => by positivity)
  have hT : 0≤T := tsum_nonneg (fun _ => by positivity)
  refine ⟨D*(2*S+3*(8*T+4)),by positivity,fun m z hz => ?_⟩
  have hm := (hs.mul_left 2).add ((halfDistance_summable m).mul_left 3)
  have hM : Summable (fun l:ℕ => D/(contourRadius a m)^2*
      (2/((l:ℝ)+gamma a)^2+3*halfDistanceMajorant m l)) := by
    simpa only [mul_one_div] using hm.mul_left (D/(contourRadius a m)^2)
  have hb := fun l => contour_factor_bound ha hD he m l hz
  have hf := hM.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hf,(hf.tsum_le_tsum hb hM).trans ?_⟩
  have hsum : (∑' l:ℕ,(2/((l:ℝ)+gamma a)^2+3*halfDistanceMajorant m l))=
      2*S+3*(∑' l,halfDistanceMajorant m l) := by
    have hh := (hs.mul_left 2).tsum_add ((halfDistance_summable m).mul_left 3)
    rw [tsum_mul_left,tsum_mul_left] at hh
    simpa only [mul_one_div,S] using hh
  rw [tsum_mul_left,hsum]
  calc
    _ ≤ D/(contourRadius a m)^2*(2*S+3*(8*T+4)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp [T]
      linarith [halfDistance_tsum_bound m]
    _ = _ := by ring

end
end jacobi.Reference
