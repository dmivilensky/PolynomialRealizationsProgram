import krylov.Correction.InformedScalar
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), complete missing-entry radial envelope.
Use: reduce the true two-dimensional hidden-entry coefficient on the closed
spectral disc to the two original radial branches, including both corners.
Source: exact scalar Schur half-width and elementary nonnegative products.
-/

namespace krylov.OneGradient
noncomputable section

/-- The original two-dimensional hidden-entry/output-defect coefficient.
Use: its full closed-disc maximum is the known-base minimax coefficient.
Article: main_krylov, thm:local(c), missing-entry objective. -/
def twoDimensionalHiddenValue (W w a g : ℝ) : ℝ :=
  W^2*a*(1-a^2/(1-g^2))+w*W*Real.sqrt (a^2+g^2)

/-- The exact radial upper envelope of the genuine hidden-entry coefficient.
Use: compute both original minimax branches from the complete closed disc.
Article: main_krylov, thm:local(c), fixed-radius optimization. -/
def twoDimensionalRadialValue (W w r : ℝ) : ℝ :=
  if r^2≤(1/2 : ℝ) then W^2*r*(1-r^2)+w*W*r
  else W^2/2*Real.sqrt (1-r^2)+w*W*r

/-- The exact missing-entry coefficient lies below the original radial
envelope on the entire closed spectral disc, including the singular
corners where the scalar Schur denominator is zero.
Use: the minimax scalar reduction covers every boundary point explicitly.
Article: main_krylov, thm:local(c), fixed-radius maximum.
Proof: the small-radius gap factors as (r-a)(1-r²-ra). At larger radii
the squared difference (a-sqrt(1-r²))² gives the sharp half-root bound.
At a singular denominator the actual cross coordinate vanishes, so both
true coefficients reduce exactly to the output-defect contribution. -/
theorem twoDimensional_hidden_radial_bound (W w a g : ℝ) (ha : 0≤ a) (hg : 0≤ g)
    (hdisc : a^2+g^2≤1) :
    twoDimensionalHiddenValue W w a g≤ twoDimensionalRadialValue W w (Real.sqrt (a^2+g^2)) := by
  let r := Real.sqrt (a^2+g^2)
  have hr : 0≤ r := Real.sqrt_nonneg _
  have hrsq : r^2=a^2+g^2 := Real.sq_sqrt (by positivity)
  have hr1 : r^2≤1 := hrsq ▸ hdisc
  have har : a≤ r := by nlinarith [sq_nonneg g]
  have hd : 0≤1-g^2 := by nlinarith [sq_nonneg a]
  by_cases hdz : 1-g^2=0
  · have haz : a=0 := by nlinarith [sq_nonneg a]
    have hrz : r^2=1 := by nlinarith
    change twoDimensionalHiddenValue W w a g≤ twoDimensionalRadialValue W w r
    rw [twoDimensionalHiddenValue,haz,twoDimensionalRadialValue,ite_eq_right (by rw [hrz];norm_num),hrz]
    simp only [zero_pow (by decide : 2≠0),mul_zero,zero_mul,zero_div,sub_zero,zero_add,
      sub_self,Real.sqrt_zero]
    have hre : r=g := by
      dsimp only [r]
      rw [haz]
      simp only [zero_pow (by decide : 2≠0),zero_add,Real.sqrt_sq hg]
    rw [hre,Real.sqrt_sq hg]
  have hdp : 0<1-g^2 := lt_of_le_of_ne hd (Ne.symm hdz)
  have hsmall (hhalf : r^2≤(1/2 : ℝ)) : a*(1-a^2/(1-g^2))≤ r*(1-r^2) := by
    have hca : 0≤1-r^2-r*a := by nlinarith [mul_nonneg hr (sub_nonneg.mpr har)]
    have hp := mul_nonneg (sub_nonneg.mpr har) hca
    have he2 : (r-a)*(1-r^2-r*a)=r*(1-g^2)-a := by
      nlinarith [congrArg (fun x : ℝ => r*x) hrsq]
    have hrp : 0≤ r*(1-g^2)-a := he2 ▸ hp
    have hp2 := mul_nonneg (sub_nonneg.mpr hr1) hrp
    apply (mul_le_mul_iff_of_pos_right hdp).mp
    have he : a*(1-a^2/(1-g^2))*(1-g^2)=a*(1-r^2) := by field_simp;rw [hrsq];ring
    rw [he]
    nlinarith
  unfold twoDimensionalRadialValue
  split_ifs with hhalf
  · unfold twoDimensionalHiddenValue
    have h := mul_le_mul_of_nonneg_left (hsmall hhalf) (sq_nonneg W)
    change W^2*a*(1-a^2/(1-g^2))+w*W*r≤_
    nlinarith
  · let c := Real.sqrt (1-r^2)
    have hc : 0≤ c := Real.sqrt_nonneg _
    have hcsq : c^2=1-r^2 := Real.sq_sqrt (sub_nonneg.mpr hr1)
    have hbound : a*(1-a^2/(1-g^2))≤ c/2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
      apply (mul_le_mul_iff_of_pos_right hdp).mp
      have he : a*(1-a^2/(1-g^2))*(1-g^2)=a*c^2 := by
        field_simp
        nlinarith [congrArg (fun x : ℝ => a*x) hrsq,congrArg (fun x : ℝ => a*x) hcsq]
      have hp := mul_nonneg hc (sq_nonneg (a-c))
      nlinarith [he]
    unfold twoDimensionalHiddenValue
    have h := mul_le_mul_of_nonneg_left hbound (sq_nonneg W)
    change W^2*a*(1-a^2/(1-g^2))+w*W*r≤_
    nlinarith

end
end krylov.OneGradient
