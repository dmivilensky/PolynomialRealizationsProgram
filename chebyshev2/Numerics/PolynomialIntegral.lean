import chebyshev2.Numerics.IntegerResidualCell
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: chebyshev2, Section 4.1.
Value certificates for quadrature.
Use: `chebyshev2.Numerics.IntegerCertificate.Poly.integral_error` feeds
`chebyshev2.Numerics.IntegerCertificate.Poly.ValuePanel.integral_error` (integral error).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate.Poly
open Polynomial Set MeasureTheory
set_option autoImplicit false

/--
The precise assertion is `result.Mem s (source.value v)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.sourceRange_sound` uses this
assertion to establish `result.Mem s (source.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Poly.Taylor.evalProgram_sound`,
`chebyshev2.Numerics.IntegerCertificate.Poly.range_sound`,
`chebyshev2.Numerics.IntegerCertificate.codeExpression_value` with the arguments shown in
the proof.
-/
theorem Taylor.source_enclosed_at {s n : Nat} (hs : 0<s) {x : ℝ}
    (hx : x∈Icc (0:ℝ) 1) (ops : List Op)
    {stack out : List (List Bounds)} {v : Nat → ℝ}
    {cps : List (Option (List Bounds))}
    (hv : Taylor.Encloses s stack x v)
    (he : Taylor.evalProgram s n stack cps ops=some out)
    {i : Nat} {source : Expr} (hsource : codeExpressionCheck ops i source=true)
    {pB : List Bounds} (hi : out[i]?=some pB) {result : Bounds}
    (hrange : range s ⟨0,s⟩ pB=some result) :
    result.Mem s (source.value v) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.Poly.Taylor.evalProgram_sound`,
  -- `chebyshev2.Numerics.IntegerCertificate.Poly.range_sound`,
  -- `chebyshev2.Numerics.IntegerCertificate.codeExpression_value` with the arguments shown
  -- in the proof.
  obtain ⟨p,hp,hpval⟩ := Taylor.evalProgram_sound hs hx ops hv he i pB hi
  have hx' : (⟨0,s⟩:Bounds).Mem s x := by
    constructor <;> dsimp [Bounds.Mem]
    · simpa using mul_nonneg (Nat.cast_nonneg s) hx.1
    · simpa using mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg s)
  have h := range_sound hs hp hx' hrange
  rw [hpval] at h
  have hshape : codeExpression Expr.input ops i=source := of_decide_eq_true hsource
  have hvalue := codeExpression_value ops Expr.input v i
  simp only [Expr.value,hshape] at hvalue
  rwa [← hvalue] at h

/--
Add the actual solution error to the constant coefficient.

The precise assertion is `At s (add [E] bs) x y`.

Use: `chebyshev2.Numerics.IntegerCertificate.valueModel_sound` uses this assertion to
establish the precise assertion is `Poly.At s (valueModel s cs u radius) x y`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Numerics.IntegerCertificate.Poly.add_sound`
with the arguments shown in the proof.
-/
theorem widen_sound {s : Nat} {bs : List Bounds} {p : ℝ[X]} {E : Bounds}
    {x y : ℝ} (hp : Rep s bs p) (he : E.Mem s (y-p.eval x)) :
    At s (add [E] bs) x y := by
  have hc : Rep s [E] (C (y-p.eval x)) := by
    simpa using Rep.cons he (Rep.nil (s := s))
  exact ⟨C (y-p.eval x)+p,add_sound hc hp,by simp⟩

/--
Defines `integralCoefficients` by pattern matching with result type `List Int → ℚ`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.Poly.integral_coefficients` rewrites with this
definition to establish `(∫ x in (0:ℝ)..1, x^n*(exactPolynomial s
cs).eval x)= (integralCoefficients s n cs:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def integralCoefficients (s n : Nat) : List Int → ℚ
  | [] => 0
  | a::as => (a:ℚ)/(s*(n+1))+integralCoefficients s (n+1) as

/--
The precise assertion is `(∫ x in (0:ℝ)..1, x^n*(exactPolynomial s cs).eval x)=
(integralCoefficients s n cs:ℝ)`.

Use: `chebyshev2.Numerics.IntegerCertificate.Poly.integral_exact` uses this identity to
establish the precise assertion is `(∫ x in (0:ℝ)..1, (exactPolynomial s cs).eval x)=
(integralCoefficients s 0 cs:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `cs` while keeping `n` arbitrary; the recursive step uses the
previous-stage assertion. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem integral_coefficients (s n : Nat) (cs : List Int) :
    (∫ x in (0:ℝ)..1, x^n*(exactPolynomial s cs).eval x)=
      (integralCoefficients s n cs:ℝ) := by
  -- Induct on `cs` while keeping `n` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cs generalizing n with
  | nil => simp [exactPolynomial,integralCoefficients]
  | cons a cs ih =>
    have he : (fun x : ℝ => x^n*(exactPolynomial s (a::cs)).eval x)=
        (fun x => (a:ℝ)/s*x^n+x^(n+1)*(exactPolynomial s cs).eval x) := by
      funext x
      simp only [exactPolynomial,eval_add,eval_C,eval_mul,eval_X]
      ring
    rw [he,intervalIntegral.integral_add (by
      exact (by fun_prop : Continuous (fun x : ℝ => (a:ℝ)/s*x^n)).intervalIntegrable _ _) (by
      exact (by fun_prop : Continuous (fun x : ℝ => x^(n+1)*(exactPolynomial s cs).eval x)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,integral_pow,ih]
    simp only [integralCoefficients,Rat.cast_add,Rat.cast_div,Rat.cast_intCast,
      one_pow,zero_pow (Nat.succ_ne_zero n),sub_zero]
    push_cast
    simp only [mul_one_div,div_div]

/--
The precise assertion is `(∫ x in (0:ℝ)..1, (exactPolynomial s cs).eval x)=
(integralCoefficients s 0 cs:ℝ)`.

Use: `chebyshev2.Numerics.IntegerCertificate.Poly.integral_error` rewrites with this
identity to prove the bound `|(∫ x in (0:ℝ)..1,f
x)-(integralCoefficients s 0 cs:ℝ)|≤ε`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Poly.integral_coefficients` with the arguments
shown in the proof.
-/
theorem integral_exact (s : Nat) (cs : List Int) :
    (∫ x in (0:ℝ)..1, (exactPolynomial s cs).eval x)=
      (integralCoefficients s 0 cs:ℝ) := by simpa using integral_coefficients s 0 cs

/--
A uniform, value-only residual certifies the entire integral.

The stated quantitative bound `|(∫ x in (0:ℝ)..1,f x)-(integralCoefficients s 0 cs:ℝ)|≤ε`.

Use: `chebyshev2.Numerics.IntegerCertificate.Poly.ValuePanel.integral_error` uses this
bound to prove the bound `|(∫ t in (p.domain.lo:ℝ)..p.domain.hi,f
t)-(p.center s:ℝ)|≤(p.radius:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Poly.integral_exact` with the arguments shown in
the proof.
-/
theorem integral_error {f : ℝ → ℝ} {s : Nat} {cs : List Int} {ε : ℝ}
    (hf : IntervalIntegrable f volume 0 1)
    (he : ∀ x∈Icc (0:ℝ) 1, |f x-(exactPolynomial s cs).eval x|≤ε) :
    |(∫ x in (0:ℝ)..1,f x)-(integralCoefficients s 0 cs:ℝ)|≤ε := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.Poly.integral_exact` with the arguments shown
  -- in the proof.
  have hp : IntervalIntegrable (fun x => (exactPolynomial s cs).eval x) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => (exactPolynomial s cs).eval x)).intervalIntegrable _ _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := ε) (f := fun x => f x-(exactPolynomial s cs).eval x)
    (fun x hx => by
      have hx' : x∈Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hx
      simpa only [Real.norm_eq_abs] using he x ⟨hx'.1.le,hx'.2⟩)
  rw [intervalIntegral.integral_sub hf hp,integral_exact] at h
  simpa only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] using h

end chebyshev2.Numerics.IntegerCertificate.Poly
