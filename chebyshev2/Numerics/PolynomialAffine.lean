import chebyshev2.Numerics.PolynomialIntegral

/-!
Article: chebyshev2, Section 4.1.
Horner composition, with outward rounding of every coefficient.
Use: `chebyshev2.Numerics.IntegerCertificate.Poly.compose_sound` feeds
`chebyshev2.Numerics.IntegerCertificate.valueModel_sound` (value Model sound).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate.Poly
open Polynomial
set_option autoImplicit false

/--
Horner composition, with outward rounding of every coefficient.

Use: `chebyshev2.Numerics.IntegerCertificate.Poly.compose_sound` uses this definition to
establish the precise assertion is `Rep s (compose s us as) (p.comp u)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def compose (s : Nat) (u : List Bounds) : List Bounds → List Bounds
  | [] => []
  | a::as => trim (add [a] (convolution s u (compose s u as)))

/--
The precise assertion is `Rep s (compose s us as) (p.comp u)`.

Use: `chebyshev2.Numerics.IntegerCertificate.Poly.compose_at` uses this assertion to
establish the precise assertion is `At s (compose s (exactBounds us) (exactBounds as)) x
((exactPolynomial s as).eval ((exactPolynomial s us).eval x))`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `hp`; the recursive step uses the previous-stage assertion.
-/
theorem compose_sound {s : Nat} (hs : 0<s) {as us : List Bounds} {p u : ℝ[X]}
    (hp : Rep s as p) (hu : Rep s us u) : Rep s (compose s us as) (p.comp u) := by
  induction hp with
  | nil => simpa [compose] using (Rep.nil (s := s))
  | @cons a as c p hc hp ih =>
    have hconstant : Rep s [a] (C c) := by
      simpa using Rep.cons hc (Rep.nil (s := s))
    simpa [compose] using trim_sound hs (add_sound hconstant (convolution_sound hs hu ih))

/--
The precise assertion is `At s (compose s (exactBounds us) (exactBounds as)) x
((exactPolynomial s as).eval ((exactPolynomial s us).eval x))`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates `chebyshev2.Numerics.IntegerCertificate.Poly.Rep.at`,
`chebyshev2.Numerics.IntegerCertificate.Poly.compose_sound`,
`chebyshev2.Numerics.IntegerCertificate.Poly.exactBounds_sound` with the arguments shown in
the proof.
-/
theorem compose_at {s : Nat} (hs : 0<s) (as us : List Int) (x : ℝ) :
    At s (compose s (exactBounds us) (exactBounds as)) x
      ((exactPolynomial s as).eval ((exactPolynomial s us).eval x)) := by
  simpa only [eval_comp] using
    (compose_sound hs (exactBounds_sound hs as) (exactBounds_sound hs us)).at x

end chebyshev2.Numerics.IntegerCertificate.Poly
