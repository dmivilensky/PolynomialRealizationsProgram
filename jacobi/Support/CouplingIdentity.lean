import jacobi.Support.CoefficientIdentities

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
The genuine squared support coupling has an exact centered difference-
of-squares expression. This exposes its original quadratic cancellation
before the uniform coefficient estimate is applied.
Use: coupling_centered turns the actual original squared coupling into a rational expression whose difference from one has a quadratic-step numerator.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference

/-- The four original centered support sine factors give an exact squared-coupling quotient.
Use: coupling_centered turns the actual original squared coupling into a rational expression whose difference from one has a quadratic-step numerator.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: pair opposite sine shifts using the proved elementary difference-of-squares identity; only reordering of genuine scalar factors remains, so no denominator exclusions are required. -/
theorem coupling_sine_identity (u p q t : ℝ) :
    (sin (u+p)*sin (u+q)/(sin (u-t)*sin u))*
      (sin (u-q)*sin (u-p)/(sin u*sin (u+t)))=
      ((sin u^2-sin p^2)*(sin u^2-sin q^2))/(sin u^2*(sin u^2-sin t^2)) := by
  rw [← sine_opposite_product u p,← sine_opposite_product u q,← sine_opposite_product u t]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The actual original squared support coupling is exactly the source-centered sine-square quotient.
Use: coupling_error bounds the genuine coefficient a_m-1/2 on the original growing half-chain range.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: at a positive original index m, substitute the actual four printed support factors into the proved centered identity. Every original shifted angle agrees by the literal parameter definitions and m-1 cast identity. -/
theorem coupling_centered (a b : ℝ) (n m : ℕ) (hm:0<m) :
    coefficientA a b n (m-1)*coefficientC a b n m=
      ((sin (((m:ℝ)+averageGamma a b-1/2)*step a b n)^2-
          sin ((gamma a-gamma b)/2*step a b n)^2)*
        (sin (((m:ℝ)+averageGamma a b-1/2)*step a b n)^2-
          sin ((averageGamma a b-1/2)*step a b n)^2))/
      (sin (((m:ℝ)+averageGamma a b-1/2)*step a b n)^2*
        (sin (((m:ℝ)+averageGamma a b-1/2)*step a b n)^2-sin (step a b n/2)^2)) := by
  -- The equality concerns the literal original birth/death product, before any square-root or asymptotic replacement.
  convert coupling_sine_identity (((m:ℝ)+averageGamma a b-1/2)*step a b n)
    ((gamma a-gamma b)/2*step a b n) ((averageGamma a b-1/2)*step a b n)
    (step a b n/2) using 1
  simp only [coefficientA,coefficientC,Nat.cast_sub hm,Nat.cast_one,averageGamma]
  ring_nf

end
end jacobi.Support
