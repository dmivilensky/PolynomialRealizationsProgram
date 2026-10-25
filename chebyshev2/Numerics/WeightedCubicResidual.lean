import chebyshev2.Numerics.ReferenceResidualIdentity
import chebyshev2.Numerics.DirectReferenceCore

/-!
Article: chebyshev2, Section 4.1.
The cubic-coordinate quadrature weight cancels the vanishing secant slope at the origin.
Use: `chebyshev2.Numerics.ReferenceData.calibration_Gamma_direct` feeds
`chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.cleared_error` (cleared error).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
noncomputable section
open Set chebyshev2.Calibration
set_option autoImplicit false

/--
The stated quantitative bound `|t^2*(r-z)|≤η/(k*l^2)`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.weighted_error` uses this
bound to prove the bound `|6*t^2*(R.calibration hσ hb hω).amplitude κ
(t^3)-6*t^3*h|≤24*er/κ`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Numerics.positive_cubic_residual_error`
with the arguments shown in the proof.
-/
theorem weighted_positive_cubic_residual_error {k a b r z l t η : ℝ}
    (hk : 0<k) (hl : 0<l) (ht : 0≤t) (hη : 0≤η)
    (hpositive : 0<t → 0<b ∧ 0<r)
    (heq : k*r^3-a*r-b=0) (hz : l*t≤z)
    (he : |k*z^3-a*z-b|≤η) : |t^2*(r-z)|≤η/(k*l^2) := by
  -- Use the identities/estimates `chebyshev2.Numerics.positive_cubic_residual_error` with
  -- the arguments shown in the proof.
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    simp only [zero_pow (by decide : (2:Nat)≠0),zero_mul,abs_zero]
    exact div_nonneg hη (mul_pos hk (sq_pos_of_pos hl)).le
  · obtain ⟨hb,hr⟩ := hpositive ht
    have hm : 0<l*t := mul_pos hl ht
    have herror := positive_cubic_residual_error hk hb hr heq hm hz he
    have hs : (k*(l*t)^2)*|r-z|≤η := by
      have hh := (le_div_iff₀ (mul_pos hk (sq_pos_of_pos hm))).mp herror
      nlinarith [hh]
    rw [abs_mul,abs_of_nonneg (sq_nonneg t),le_div_iff₀ (mul_pos hk (sq_pos_of_pos hl))]
    nlinarith [hs]

/--
Exact identity `(R.calibration hσ hb hω).Gamma (t^3)=R.directGamma hσ t`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.cleared_error` rewrites
with this identity to prove the bound `|6*t^2*(R.calibration hσ hb
hω).amplitude κ (t^3)-g|≤24*er/(dl*kl)+eq`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedGamma_factor`,
`chebyshev2.Calibration.ReferenceData.directGamma_eq` with the arguments shown in the
proof.
-/
theorem ReferenceData.calibration_Gamma_direct (R : ReferenceData) {σ b ω : ℝ}
    (hσ : 0<σ) (hb : 0<b) (hω : 0≤ω) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (R.calibration hσ hb hω).Gamma (t^3)=R.directGamma hσ t := by
  rw [R.normalizedGamma_factor hσ hb hω ht,R.directGamma_eq hσ ht]
  rfl

end
end chebyshev2.Numerics
