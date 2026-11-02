import jacobi.Reference.IndexMajorant

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
A shifted inverse-square majorant controls the complete relative
spectral product on circles between consecutive reference frequencies.
The estimates include all indices; the half-integer shift excludes every
reference pole without introducing an exceptional spectral prefix.
Use: contour_displacement_sum_bound controls all relative product factors without a separate near-diagonal harmonic estimate.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter
open scoped Topology

/-- A reciprocal quadratic gap admits a sum of two inverse-square majorants.
Use: contour_displacement_sum_bound controls all relative product factors without a separate near-diagonal harmonic estimate.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: for positive x,y, |y^2-x^2| dominates (y-x)^2.
After clearing positive squares, the remaining inequality is (x-2*y)^2>=0. -/
theorem quadratic_gap_inverse_majorant {x y : ℝ} (hx : 0<x) (hy : 0<y) (hne : y≠x) :
    (1/x^2+1/y^2)/|y^2-x^2|≤(2/y^2+3/(y-x)^2)/x^2 := by
  -- The two squares separate the low-frequency tail from the translated diagonal.
  have hd : 0<(y-x)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hg : (y-x)^2≤|y^2-x^2| := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_of_neg (by nlinarith : y^2-x^2<0)]
      nlinarith
    · rw [abs_of_pos (by nlinarith : 0<y^2-x^2)]
      nlinarith
  apply (div_le_div_of_nonneg_left (show 0≤1/x^2+1/y^2 by positivity) hd hg).trans
  apply (div_le_div_iff₀ hd (sq_pos_of_pos hx)).mpr
  field_simp
  nlinarith [sq_nonneg (x-2*y)]

/-- The inverse-square distance from an integer frequency index to a midpoint contour index.
Use: its uniformly bounded sum controls the reference denominators on every original parity contour.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def halfDistanceMajorant (m l : ℕ) : ℝ := 1/((l:ℝ)-m-1/2)^2

/-- Integer frequencies never meet a midpoint contour index.
Use: proves the genuine positive denominators in the original contour estimates.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: distinct integer indices differ by at least one; equality is also separated by one half. -/
theorem halfDistance_ne_zero (m l : ℕ) : (l:ℝ)-m-1/2≠0 := by
  rcases lt_trichotomy l m with h | rfl | h
  · have hh : (l:ℝ)+1≤m := by exact_mod_cast h
    linarith
  · norm_num
  · have hh : (m:ℝ)+1≤l := by exact_mod_cast h
    linarith

/-- The half-integer distance majorant is bounded by the original integer distance majorant plus its single diagonal value.
Use: proves halfDistance_summable and halfDistance_tsum_bound uniformly in the contour index.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: off the diagonal, shifting an integer distance by one half reduces
its absolute value by at most a factor two. On the diagonal its inverse square is four. -/
theorem halfDistance_bound (m l : ℕ) :
    halfDistanceMajorant m l≤4*distanceMajorant m l+(if l=m then 4 else 0) := by
  -- The diagonal is retained explicitly, so the original contour has no omitted factor.
  by_cases h : l=m
  · subst l
    norm_num [halfDistanceMajorant,distanceMajorant]
  · rw [ite_eq_right h,add_zero]
    have hd : 0<((l:ℝ)-m)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (by exact_mod_cast h))
    have hh : 0<((l:ℝ)-m-1/2)^2 := sq_pos_of_ne_zero (halfDistance_ne_zero m l)
    unfold halfDistanceMajorant distanceMajorant
    rw [mul_one_div]
    apply (div_le_div_iff₀ hh hd).mpr
    have hsq : ((l:ℝ)-m)^2≤4*((l:ℝ)-m-1/2)^2 := by
      rcases lt_or_gt_of_ne h with hl | hl
      · have hc : (l:ℝ)+1≤m := by exact_mod_cast hl
        nlinarith
      · have hc : (m:ℝ)+1≤l := by exact_mod_cast hl
        nlinarith
    simpa only [one_mul] using hsq

/-- The inverse-square midpoint-contour distance series is genuinely summable.
Use: gives absolute convergence of the original relative characteristic factors on every parity contour.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the translated integer p-series is summable, and the retained midpoint diagonal has singleton support. -/
theorem halfDistance_summable (m : ℕ) : Summable (halfDistanceMajorant m) := by
  have hd : Summable (fun l:ℕ => if l=m then (4:ℝ) else 0) := (hasSum_ite_eq m 4).summable
  exact ((distanceMajorant_summable m).mul_left 4 |>.add hd).of_nonneg_of_le
    (fun l => by unfold halfDistanceMajorant; positivity) (halfDistance_bound m)

/-- Every midpoint-contour inverse-square distance series has one bound independent of its center.
Use: gives the uniform constant in the original O(R^-2) relative characteristic contour estimate.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: sum halfDistance_bound. The translated integer distance series
has at most twice the fixed positive p-series mass, and the diagonal contributes four. -/
theorem halfDistance_tsum_bound (m : ℕ) :
    (∑' l,halfDistanceMajorant m l)≤8*(∑' l:ℕ,1/(l+1:ℝ)^2)+4 := by
  -- Both series are genuinely summable before comparing their actual sums.
  have hd : Summable (fun l:ℕ => if l=m then (4:ℝ) else 0) := (hasSum_ite_eq m 4).summable
  have hs := (distanceMajorant_summable m).mul_left 4
  have h := (halfDistance_summable m).tsum_le_tsum (halfDistance_bound m) (hs.add hd)
  rw [hs.tsum_add hd,tsum_mul_left,tsum_ite_eq] at h
  exact h.trans (by linarith [distanceMajorant_tsum_le m])

end
end jacobi.Reference
