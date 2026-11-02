import jacobi.Bessel.SpectralBounds

/-!
Article: jacobi, Appendix C.2 (norming ratios).
A translated inverse-square series has a bound independent of its center.
A single rational inequality then controls the complete spectral perturbation
sum; no near-diagonal logarithmic estimate or large-index exception is needed.
Source: the classical p-series and elementary inequalities, proved here using mathlib.
Use: gives a summable majorant uniform in the center of the actual norming-product estimate.
-/
namespace jacobi.Reference
noncomputable section
open Real Finset

/-- The inverse square of the distance between distinct integer indices, with zero at the omitted diagonal.
Use: gives a summable majorant uniform in the center of the actual norming-product estimate.
Article: jacobi, Appendix C.2 (norming ratios).
-/
def distanceMajorant (k l : ℕ) : ℝ := 1/((l:ℝ)-k)^2

/-- The translated inverse-square series is genuinely summable for every center.
Use: justifies all sums in the uniform norming-ratio logarithm estimate.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: after the finite prefix through the diagonal, the actual tail is precisely the positive-index p-series. -/
theorem distanceMajorant_summable (k : ℕ) : Summable (distanceMajorant k) := by
  apply (summable_nat_add_iff (k+1)).mp
  convert jacobi.Bessel.inverse_square_majorant_summable 1 using 1
  ext l
  simp only [distanceMajorant,Nat.cast_add,Nat.cast_one,one_pow]
  congr 2
  ring

/-- The whole translated inverse-square sum is at most twice the positive-index p-series, independently of its center.
Use: produces the uniform inverse-square norming-ratio estimate without a three-region index split.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the left finite prefix reverses to an initial p-series sum, the
central term is zero and the right infinite tail is the full p-series.
The finite prefix is bounded by that same positive series. -/
theorem distanceMajorant_tsum_le (k : ℕ) :
    (∑' l,distanceMajorant k l)≤2*(∑' l:ℕ,1/(l+1:ℝ)^2) := by
  -- Reflect the actual finite prefix; no estimate depends on the center k.
  have hs : Summable (fun l:ℕ => 1/(l+1:ℝ)^2) := by
    simpa only [one_pow] using jacobi.Bessel.inverse_square_majorant_summable 1
  have htail : (fun l => distanceMajorant k (l+(k+1)))=(fun l:ℕ => 1/(l+1:ℝ)^2) := by
    funext l
    dsimp [distanceMajorant]
    push_cast
    congr 2
    ring
  have hprefix : (∑ l∈range k,distanceMajorant k l)=∑ l∈range k,1/(l+1:ℝ)^2 := by
    rw [← sum_range_reflect (distanceMajorant k) k]
    apply sum_congr rfl
    intro l hl
    have hlk : l<k := mem_range.mp hl
    have he : ((k-1-l:ℕ):ℝ)=(k:ℝ)-1-l := by
      rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one]
    rw [distanceMajorant,he]
    congr 1
    ring
  rw [← (distanceMajorant_summable k).sum_add_tsum_nat_add (k+1),htail,
    sum_range_succ,hprefix]
  simp only [distanceMajorant,sub_self,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,div_zero,add_zero]
  linarith [hs.sum_le_tsum (range k) (fun l _ => by positivity)]

/-- A single two-series bound controls the full rational spectral-error majorant away from the diagonal.
Use: combines actual inverse-square spectral errors and quadratic gaps into an index-uniform summable bound.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the squared-index gap dominates the squared integer distance.
After clearing positive denominators, the remaining inequality is the
nonnegativity of (x-2*y)^2; this avoids separate low, middle and high ranges. -/
theorem inverse_square_gap_majorant {k l : ℕ} (hkl : k≠l) :
    (1/(k+1:ℝ)^2+1/(l+1:ℝ)^2)/|(l+1:ℝ)^2-(k+1:ℝ)^2|≤
      (2/(l+1:ℝ)^2+3*distanceMajorant k l)/(k+1:ℝ)^2 := by
  -- The distance is nonzero precisely because the actual omitted diagonal is excluded.
  let x : ℝ := k+1
  let y : ℝ := l+1
  have hx : 0<x := by dsimp [x]; positivity
  have hy : 0<y := by dsimp [y]; positivity
  have hne : y≠x := by
    dsimp [x,y]
    exact fun h => hkl (by exact_mod_cast (by linarith : (k:ℝ)=l))
  have hd : 0<(y-x)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hg : (y-x)^2≤|y^2-x^2| := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_of_neg (by nlinarith : y^2-x^2<0)]
      nlinarith
    · rw [abs_of_pos (by nlinarith : 0<y^2-x^2)]
      nlinarith
  have hfirst := div_le_div_of_nonneg_left
    (show 0≤1/x^2+1/y^2 by positivity) hd hg
  have hsecond : (1/x^2+1/y^2)/(y-x)^2≤(2/y^2+3/(y-x)^2)/x^2 := by
    apply (div_le_div_iff₀ hd (sq_pos_of_pos hx)).mpr
    field_simp
    nlinarith [sq_nonneg (x-2*y)]
  have he : distanceMajorant k l=1/(y-x)^2 := by
    dsimp [distanceMajorant,x,y]
    congr 2
    ring
  change (1/x^2+1/y^2)/|y^2-x^2|≤(2/y^2+3*distanceMajorant k l)/x^2
  rw [he,mul_one_div]
  exact hfirst.trans hsecond

end
end jacobi.Reference
