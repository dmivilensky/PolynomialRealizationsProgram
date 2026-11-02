import jacobi.Bessel.OrderShift

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The actual normalized Bessel functions satisfy their three-order
contiguous identity on the whole complex energy plane. It extends
the Poisson integral's negative asymptotic to every original order
alpha>-1, including alpha<=-1/2.
Source: the classical Bessel three-term order recurrence, DLMF 10.6.1.
Use: extends the original Poisson negative-axis asymptotic to the article's whole order range alpha>-1.
-/
namespace jacobi.Bessel
noncomputable section
open Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized entire Bessel functions satisfy the exact three-order recurrence at every complex energy.
Use: extends the original Poisson negative-axis asymptotic to the article's whole order range alpha>-1.
Article: jacobi, Appendix C.2 (norming ratios).
Source: the Bessel order recurrence, DLMF 10.6.1, derived here from the proved actual differential and adjacent-derivative identities.
Proof: differentiate the genuine adjacent-order derivative identity
once more. Substitute both actual derivatives into the original
Bessel equation. Only alpha+1 and alpha+2 are canceled, and their
positive real parts exclude zero throughout the original range. -/
theorem normalized_contiguous {a : ℂ} (ha : -1<a.re) (z : ℂ) :
    normalized a z=normalized (a+1) z-z/(4*(a+1)*(a+2))*normalized (a+2) z := by
  -- The same original entire functions occur in the differential equation and both genuine order shifts.
  have ha1 : -1<(a+1).re := by simp only [add_re,one_re]; linarith
  have h1 : deriv (normalized a)=(fun w => (-1/(4*(a+1)))*normalized (a+1) w) :=
    funext (normalized_derivative_order_shift ha)
  have h2 : deriv (deriv (normalized a)) z=
      (1/(16*(a+1)*(a+2)))*normalized (a+2) z := by
    rw [h1,deriv_const_mul_field,normalized_derivative_order_shift ha1,
      show a+1+1=a+2 by ring]
    simp only [div_eq_mul_inv,mul_inv]
    ring
  have h := normalized_equation ha z
  rw [h2,normalized_derivative_order_shift ha] at h
  have hp : a+1≠0 := by
    intro hz
    have hh := congrArg Complex.re hz
    simp only [add_re,one_re,zero_re] at hh
    linarith
  have hq : a+2≠0 := by
    intro hz
    have hh := congrArg Complex.re hz
    norm_num at hh
    linarith
  field_simp [hp,hq] at h ⊢
  linear_combination h/4

end
end jacobi.Bessel
