import jacobi.Finite.NormalizedPolynomials

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Use: the discrete Green identity fixes the original support wave uniquely, rather than only up to a scalar.
-/
namespace jacobi.Finite
noncomputable section
open Real Polynomial chebyshev1 chebyshev2

/-- The genuine original normalized polynomial has the original constant initial value at every complex energy.
Use: the discrete Green identity fixes the original support wave uniquely, rather than only up to a scalar.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: both the original empty coupling product and original degree-zero continuant equal one. -/
theorem normalizedLeading_zero {n : ℕ} (J : Jacobi n) (z : ℂ) :
    Polynomial.aeval z (normalizedLeading J 0)=1 := by
  simp [normalizedLeading]

/-- The actual normalized original spectral polynomial satisfies its genuine three-term equation at arbitrary complex energy.
Use: the support Wronskian and exact Volterra identity apply directly to the original spectral orthogonal polynomials.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: normalize the genuine original monic three-term recurrence by its actual positive coupling product. The degree-zero boundary is handled separately; the interior identity cancels only positive coupling products and uses the exact square-root square of the original squared coupling. -/
theorem normalizedLeading_recurrence {n : ℕ} (J : Jacobi n) (hJ:J.Irreducible)
    (z : ℂ) (m : ℕ) (hm:m+1<n) :
    (Real.sqrt (J.data.aSq (m+1)):ℂ)*Polynomial.aeval z (normalizedLeading J (m+1))+
      (if m=0 then 0 else (Real.sqrt (J.data.aSq m):ℂ)*Polynomial.aeval z (normalizedLeading J (m-1)))+
      (J.data.b m:ℂ)*Polynomial.aeval z (normalizedLeading J m)=
        z*Polynomial.aeval z (normalizedLeading J m) := by
  -- Positive original recurrence factors justify every normalization, also for nonreal spectral parameters.
  have hn := sqrt_pos.mpr (hJ (m+1) (by omega) hm)
  cases m with
  | zero =>
    simp only [normalizedLeading,JacobiData.linkProduct_succ,JacobiData.linkProduct_zero,
      JacobiData.leading,JacobiData.block,Nat.zero_add,one_mul,inv_one,mul_one,
      map_mul,map_sub,map_one,aeval_C,aeval_X,Complex.coe_algebraMap]
    have hnc : (Real.sqrt (J.data.aSq 1):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn.ne'
    push_cast
    field_simp [hnc]
    ring
  | succ m =>
    have hp := sqrt_pos.mpr (hJ (m+1) (by omega) (by omega))
    have hL := linkProduct_pos hJ (show m<n by omega)
    have hrec : J.data.leading (m+2)=(X-C (J.data.b (m+1)))*J.data.leading (m+1)-
        C (J.data.aSq (m+1))*J.data.leading m := by
      simp only [JacobiData.leading,JacobiData.block,Nat.zero_add]
    simp only [normalizedLeading,hrec,JacobiData.linkProduct_succ,Nat.add_sub_cancel,
      ite_eq_right (Nat.succ_ne_zero m),map_mul,map_sub,aeval_C,aeval_X,Complex.coe_algebraMap]
    have hs : (J.data.aSq (m+1):ℂ)=(Real.sqrt (J.data.aSq (m+1)):ℂ)^2 := by
      exact_mod_cast (Real.sq_sqrt (J.coupling_nonneg (m+1))).symm
    rw [hs]
    push_cast
    have hnc := Complex.ofReal_ne_zero.mpr hn.ne'
    have hpc := Complex.ofReal_ne_zero.mpr hp.ne'
    have hLc := Complex.ofReal_ne_zero.mpr hL.ne'
    field_simp [hnc,hpc,hLc]
    ring

end
end jacobi.Finite
