import jacobi.GelfandLevitan.QuadraticSeries

/-!
Article: jacobi, Appendix C.2 (uniform GL coercivity).
For every actual half-supported L2 input, the original identity-plus-F
quadratic form equals the convergent positive source coefficient sum.
Its only zero is the zero input: the actual original coefficient
uniqueness theorem supplies injectivity, with no frame or completeness
assumption on the perturbed functions. Uniform coercivity requires
the additional compact-operator argument, beyond this pointwise result.
Use: its exact positive spectral expansion and genuine injectivity lead to the source uniform coercivity and GL existence argument.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology

/-- The actual identity-plus-original-kernel quadratic form after the source zero extension.
Use: its exact positive spectral expansion and genuine injectivity lead to the source uniform coercivity and GL existence argument.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
-/
def quadratic (a : ℝ) (ha : -1<a) (v : Space) : ℝ := ‖v‖^2+kernelQuadratic a ha v

/-- The actual identity-plus-F quadratic form has exactly the convergent original positive norming-weighted coefficient expansion.
Use: proves genuine nonnegativity and reduces every actual null vector to vanishing original Bessel coefficients.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: add the genuinely convergent actual kernel correction series
to the original complete-reference Parseval series. The source
half-support identity identifies each true reference coefficient;
the two reference squares cancel at every original spectral index. -/
theorem quadratic_hasSum (a : ℝ) (ha : -1<a) (v : Space) (hv : HalfSupported v) :
    HasSum (fun k => normingRatio a ha k*(realCoefficient a v (jacobi.Bessel.sigma a ha k))^2/
      norming a k) (quadratic a ha v) := by
  -- Both genuine spectral series are proved convergent before the original reference terms cancel.
  have hs := (reference_parseval_hasSum a ha v).add (kernel_quadratic_hasSum a ha v)
  have he (k : ℕ) : (referenceCoefficient a k v)^2/norming a k+
      (normingRatio a ha k*(realCoefficient a v (jacobi.Bessel.sigma a ha k))^2-
        (realCoefficient a v (eigenvalue a k))^2)/norming a k=
      normingRatio a ha k*(realCoefficient a v (jacobi.Bessel.sigma a ha k))^2/norming a k := by
    rw [realCoefficient_reference a v hv k]
    ring
  simpa only [he,quadratic] using hs

/-- The genuine original identity-plus-F quadratic form is nonnegative on every actual source half-supported L2 input.
Use: provides the nonnegative form needed before applying actual compactness and injectivity to obtain GL uniform coercivity.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: every original norming ratio and norming integral is strictly
positive; each real source coefficient square is nonnegative. The
actual quadratic identity is the sum of exactly these genuine terms. -/
theorem quadratic_nonneg (a : ℝ) (ha : -1<a) (v : Space) (hv : HalfSupported v) :
    0≤quadratic a ha v := by
  rw [← (quadratic_hasSum a ha v hv).tsum_eq]
  exact tsum_nonneg (fun k => div_nonneg
    (mul_nonneg (normingRatio_properties ha k).2.le (sq_nonneg _)) (norming_pos ha k).le)

/-- The actual original identity-plus-F form has no nonzero half-supported L2 null vector.
Use: supplies genuine GL injectivity for the original kernel; the further uniform lower bound follows after the compact-operator argument.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: a zero sum of the actual nonnegative spectral terms makes
each original coefficient square zero. Strict positivity of the
actual norming data removes its weight. The fully proved original
Bessel coefficient uniqueness theorem then forces the input to vanish. -/
theorem quadratic_eq_zero_imp (a : ℝ) (ha : -1<a) (v : Space) (hv : HalfSupported v)
    (hq : quadratic a ha v=0) : v=0 := by
  -- The source Jensen and Parseval uniqueness theorem applies to every original L2 input, without a finite-dimensional restriction.
  have hs := quadratic_hasSum a ha v hv
  have hn (k : ℕ) : 0≤normingRatio a ha k*(realCoefficient a v (jacobi.Bessel.sigma a ha k))^2/
      norming a k := div_nonneg (mul_nonneg (normingRatio_properties ha k).2.le (sq_nonneg _))
        (norming_pos ha k).le
  have ht : ∑' k,normingRatio a ha k*(realCoefficient a v (jacobi.Bessel.sigma a ha k))^2/norming a k=0 :=
    hs.tsum_eq.trans hq
  have he := (hasSum_zero_iff_of_nonneg hn).mp (ht ▸ hs.summable.hasSum)
  apply bessel_coefficients_injective ha v hv
  intro k
  have hh := congrFun he k
  have hratio := (normingRatio_properties ha k).2
  have hnorm := norming_pos ha k
  have hz := (div_eq_zero_iff.mp hh).resolve_right hnorm.ne'
  have hsq := (mul_eq_zero.mp hz).resolve_left hratio.ne'
  exact sq_eq_zero_iff.mp hsq

/-- The actual source identity-plus-F quadratic form is strictly positive at every nonzero half-supported original L2 input.
Use: together with genuine compactness this gives the uniform source coercivity required for solving the GL equation.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the genuine form is nonnegative, and its proved actual injectivity excludes zero at a nonzero original input. -/
theorem quadratic_pos (a : ℝ) (ha : -1<a) (v : Space) (hv : HalfSupported v) (hne : v≠0) :
    0<quadratic a ha v :=
  lt_of_le_of_ne (quadratic_nonneg a ha v hv) (fun he => hne (quadratic_eq_zero_imp a ha v hv he.symm))

end
end jacobi.GelfandLevitan
