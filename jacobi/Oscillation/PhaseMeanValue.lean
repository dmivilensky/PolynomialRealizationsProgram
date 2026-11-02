import jacobi.Oscillation.PhasePerturbation

/-!
Article: jacobi, Proposition B.1.
A true perturbed inverse-square phase has explicit Lipschitz and
identity-remainder bounds on every original joining interval bounded
away from zero. The original finite and Bessel phases instantiate the
same elementary mean-value argument at their genuine numbered zeros.
Use: controls the original finite initial phase and the true Bessel phase-to-zero remainder.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse-square phase correction has a uniform scalar bound on any positive interval away from its singular endpoint.
Use: controls the original finite initial phase and the true Bessel phase-to-zero remainder.
Article: jacobi, Proposition B.1.
Proof: sine squared lies in [0,1], and x>=l>0 bounds the positive denominator below by l^2. -/
theorem phase_correction_bound {c x l e epsilon theta : ℝ} (hl : 0<l) (hxl : l≤x)
    (he : |e|≤epsilon) :
    |(c/x^2+e)*sin theta^2|≤ |c|/l^2+epsilon := by
  -- Separate the bounded trigonometric factor from the actual inverse-square coefficient before applying the triangle inequality.
  have hx : 0<x := hl.trans_le hxl
  have hs : |sin theta^2|≤1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_add_cos_sq theta,sq_nonneg (cos theta)]
  have hd : |c|/x^2≤ |c|/l^2 := div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hl)
    (pow_le_pow_left₀ hl.le hxl 2)
  rw [abs_mul]
  calc
    _ ≤ |c/x^2+e| *1 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ ≤ |c|/l^2+epsilon := by
      rw [mul_one]
      have hh := abs_add_le (c/x^2) e
      rw [abs_div,abs_of_pos (sq_pos_of_pos hx)] at hh
      linarith

/-- A genuine inverse-square perturbed phase differs from the identity by at most its actual correction bound times the original argument displacement.
Use: compares true Bessel phase differences with the same actual zero displacement in Proposition B.1 (a).
Article: jacobi, Proposition B.1.
Proof: subtract the identity from the genuine phase derivative. Apply the
community mean-value theorem on the actual unordered joining interval
and the exact scalar correction estimate at every point there. -/
theorem phase_identity_remainder {f e : ℝ → ℝ} {u v c l epsilon : ℝ}
    (hl : 0<l)
    (hx : ∀ x∈uIcc u v,l≤x)
    (hf : ∀ x∈uIcc u v,HasDerivAt f (1+(c/x^2+e x)*sin (f x)^2) x)
    (he : ∀ x∈uIcc u v,|e x|≤epsilon) :
    |(f v-f u)-(v-u)|≤(|c|/l^2+epsilon)*|v-u| := by
  -- The unordered interval handles both signs of the original finite zero displacement, preserving the same exact phase base.
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => f x-x) (f' := fun x => (c/x^2+e x)*sin (f x)^2)
    (fun x hxx => by
      have hh : HasDerivAt (fun t => f t-t) ((c/x^2+e x)*sin (f x)^2) x := by
        convert (hf x hxx).sub (hasDerivAt_id x) using 1
        · rfl
        · ring
      exact hh.hasDerivWithinAt)
    (fun x hxx => by simpa only [Real.norm_eq_abs] using phase_correction_bound hl (hx x hxx) (he x hxx))
    (convex_uIcc u v) left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at h
  convert h using 1
  congr 1
  ring

/-- The original genuine phase is Lipschitz with its explicit actual coefficient bound on an unordered joining interval.
Use: aligns the original finite phase with the actual Bessel base zero, using the proved genuine finite-root frequency error.
Article: jacobi, Proposition B.1.
Proof: add the actual argument displacement back to the proved identity remainder and apply the triangle inequality. -/
theorem phase_lipschitz_bound {f e : ℝ → ℝ} {u v c l epsilon : ℝ}
    (hl : 0<l) (hx : ∀ x∈uIcc u v,l≤x)
    (hf : ∀ x∈uIcc u v,HasDerivAt f (1+(c/x^2+e x)*sin (f x)^2) x)
    (he : ∀ x∈uIcc u v,|e x|≤epsilon) :
    |f v-f u|≤(1+|c|/l^2+epsilon)*|v-u| := by
  have h := phase_identity_remainder hl hx hf he
  have hh := abs_add_le ((f v-f u)-(v-u)) (v-u)
  rw [sub_add_cancel] at hh
  have heq : (1+|c|/l^2+epsilon)*|v-u|=(|c|/l^2+epsilon)*|v-u|+|v-u| := by ring
  rw [heq]
  linarith

end
end jacobi.Oscillation
