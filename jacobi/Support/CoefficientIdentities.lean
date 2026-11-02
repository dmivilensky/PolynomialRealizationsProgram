import jacobi.Support.Chain
import jacobi.Support.DarbouxTrigonometry

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
Exact centered sine identities expose the second-order cancellation in
the genuine support diagonal and squared coupling. The resulting error
estimates use positive original sine denominators and elementary bounds,
without separately approximating two cancelling first-order terms.
Use: coupling_centered exposes the genuine squared-coupling cancellation required by the coefficient estimate in Appendix D.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference

/-- Opposite shifts in an original sine pair give an exact difference of squares.
Use: coupling_centered exposes the genuine squared-coupling cancellation required by the coefficient estimate in Appendix D.
Article: jacobi, Appendix C.3 (coefficient bounds).
Source: elementary sine addition formulas.
Proof: expand both sine factors and substitute the genuine sine-cosine square identity. -/
theorem sine_opposite_product (u v : ℝ) :
    sin (u+v)*sin (u-v)=sin u^2-sin v^2 := by
  rw [sin_add,sin_sub]
  nlinarith [sin_sq_add_cos_sq u,sin_sq_add_cos_sq v]

/-- The original support diagonal has an exact centered sine quotient with a numerator quadratic in the lattice step.
Use: diagonal_centered and the genuine shifted-sine bounds prove the printed uniform O(m^-2) diagonal estimate.
Article: jacobi, Appendix C.3 (coefficient bounds).
Source: elementary trigonometric addition and product identities.
Proof: combine the two genuine original quotients over their nonzero common denominator and expand the addition formulas; the original sine-cosine square identities cancel every first-order term. -/
theorem diagonal_sine_identity (u v w t : ℝ)
    (hu:sin u≠0) (hm:sin (u-t)≠0) (hp:sin (u+t)≠0) :
    cos (v+w-t)-
      (sin (u+v)*sin (u+w)/(sin u*sin (u+t))+
        sin (u-w)*sin (u-v)/(sin (u-t)*sin u))/2=
      -cos t*sin (v-t)*sin (w-t)/(sin (u-t)*sin (u+t)) := by
  -- Centering makes the first-order cancellation exact before any uniform estimate is applied.
  have hcu : cos u^2=1-sin u^2 := by nlinarith [sin_sq_add_cos_sq u]
  have hct : cos t^2=1-sin t^2 := by nlinarith [sin_sq_add_cos_sq t]
  have hct3 : cos t^3=cos t*(1-sin t^2) := by linear_combination cos t*hct
  field_simp
  simp only [sin_add,sin_sub,cos_add,cos_sub]
  ring_nf
  simp only [hcu,hct,hct3]
  ring

/-- The actual original support diagonal is the exact centered quadratic-step sine quotient.
Use: the actual coefficient estimate applies to the same original matrix diagonal used by the support polynomial recurrence and envelope.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: specialize the proved elementary identity at the original center (m+bar_gamma)*h, with the exact printed endpoint shifts. -/
theorem diagonal_centered (a b : ℝ) (n m : ℕ)
    (h0:sin (((m:ℝ)+averageGamma a b)*step a b n)≠0)
    (hm:sin (((m:ℝ)+averageGamma a b-1/2)*step a b n)≠0)
    (hp:sin (((m:ℝ)+averageGamma a b+1/2)*step a b n)≠0) :
    diagonal a b n m=
      -cos (step a b n/2)*sin ((gamma a-gamma b)/2*step a b n)*
        sin ((averageGamma a b-1/2)*step a b n)/
          (sin (((m:ℝ)+averageGamma a b-1/2)*step a b n)*
            sin (((m:ℝ)+averageGamma a b+1/2)*step a b n)) := by
  -- The generic sine identity is instantiated at the actual original parameters and step, without a generic-position restriction.
  let u := ((m:ℝ)+averageGamma a b)*step a b n
  let v := (gamma a-gamma b+1)/2*step a b n
  let w := averageGamma a b*step a b n
  let t := step a b n/2
  have hM : sin (u-t)≠0 := by convert hm using 1; congr 1; dsimp [u,t]; ring
  have hP : sin (u+t)≠0 := by convert hp using 1; congr 1; dsimp [u,t]; ring
  convert diagonal_sine_identity u v w t h0 hM hP using 1 <;>
    simp only [diagonal,coefficientA,coefficientC,u,v,w,t,averageGamma] <;> ring_nf

end
end jacobi.Support
