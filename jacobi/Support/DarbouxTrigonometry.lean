import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Elementary sine quotient identities give the actual endpoint Darboux
deletion. They replace an appeal to the general Askey--Wilson difference
equation, including its exceptional parameter extensions, by exact real
algebra valid whenever the three genuine interior sine factors are nonzero.
Use: sine_quotient_difference cancels the common actual interior sine factor in the original shifted coefficient difference.
-/
namespace jacobi.Support
noncomputable section
open Real

/-- The sine-product difference underlying the original support Christoffel transformation.
Use: sine_quotient_difference cancels the common actual interior sine factor in the original shifted coefficient difference.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: the elementary sine addition formulas.
Proof: expand the four original sine factors and the resulting sine of a sum; all mixed terms cancel algebraically. -/
theorem sine_product_difference (u v w : ℝ) :
    sin (u+v)*sin (u+w)-sin (u-w)*sin (u-v)=2*sin u*cos u*sin (v+w) := by
  simp only [Real.sin_add,Real.sin_sub]
  ring

/-- The genuine difference of the two original common-denominator support sine quotients has a single simple remaining sine denominator.
Use: sine_quotient_darboux gives the actual shifted diagonal identity.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: sine addition and ordinary real quotient cancellation.
Proof: combine the original numerator difference, use the proved actual sine-product identity and cancel the genuine nonzero interior sine. -/
theorem sine_quotient_difference (u v w D : ℝ) (hu : sin u≠0) (hD : D≠0) :
    sin (u+v)*sin (u+w)/(sin u*D)-sin (u-w)*sin (u-v)/(sin u*D)=
      2*cos u*sin (v+w)/D := by
  rw [← sub_div,sine_product_difference]
  field_simp

/-- The four actual shifted sine quotients satisfy the exact original support diagonal Darboux identity.
Use: coefficient_darboux_diagonal specializes this elementary identity to the original A,C and their actual alpha+2 parameter shift.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: the endpoint Darboux transformation, here proved directly by sine addition.
Proof: pair the original common-denominator differences at u and u+2*t. Their proved numerator identities leave the cosine difference cos(u)-cos(u+2*t)=2*sin(u+t)*sin(t), whose genuine middle sine cancels. -/
theorem sine_quotient_darboux (u v w t : ℝ)
    (hu : sin u≠0) (hm : sin (u+t)≠0) (hp : sin (u+2*t)≠0) :
    sin (u+v)*sin (u+w)/(sin u*sin (u+t))+
      sin (u+2*t-w)*sin (u+2*t-v)/(sin (u+t)*sin (u+2*t))-
      (sin (u+2*t+v)*sin (u+2*t+w)/(sin (u+t)*sin (u+2*t))+
        sin (u-w)*sin (u-v)/(sin u*sin (u+t)))=
      4*sin (v+w)*sin t := by
  -- Both cancellations concern genuine actual denominators; the final identity contains no reciprocal sine.
  have h1 := sine_quotient_difference u v w (sin (u+t)) hu hm
  have h2 := sine_quotient_difference (u+2*t) v w (sin (u+t)) hp hm
  have hcos : cos u-cos (u+2*t)=2*sin (u+t)*sin t := by
    have hA := Real.cos_sub (u+t) t
    have hB := Real.cos_add (u+t) t
    rw [show u+t-t=u by ring] at hA
    rw [show u+t+t=u+2*t by ring] at hB
    linear_combination hA-hB
  rw [mul_comm (sin (u+2*t))] at h2
  calc
    _ = (2*cos u*sin (v+w)/sin (u+t))-(2*cos (u+2*t)*sin (v+w)/sin (u+t)) := by
      linear_combination h1-h2
    _ = 2*sin (v+w)*(cos u-cos (u+2*t))/sin (u+t) := by ring
    _ = _ := by rw [hcos]; field_simp; ring

end
end jacobi.Support
