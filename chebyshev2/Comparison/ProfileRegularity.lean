import chebyshev2.Comparison.ProfileRepresentation

/-!
Article: chebyshev2, Theorem 3.2.
Classical ground-coordinate regularity for all comparison profiles.
Use: `chebyshev2.Comparison.Profile.coordinate_derivative` feeds
`chebyshev2.Calibration.ReferenceData.coordinate_derivative` (coordinate derivative).
Proof chain: `chebyshev2.Calibration.ReferenceData.contact_strictMono` — chebyshev2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.PrescribedSpeed chebyshev2.GroundState chebyshev2.Filters
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : chebyshev2.Comparison.Profile κ) (hκ : 0 < κ)

/--
The actual derivative at the stated point: `HasDerivAt (P.speedData hκ).q (κ*P.density hκ
x-chebyshev2.Calibration.Q ((P.speedData hκ).q x)) x`.

Use: `chebyshev2.Comparison.Profile.coordinate_c1` uses this derivative formula to
establish smoothness to the stated order: `ContDiff ℝ 1 (P.speedData hκ).q`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem coordinate_derivative (x : ℝ) :
    HasDerivAt (P.speedData hκ).q
      (κ*P.density hκ x-chebyshev2.Calibration.Q ((P.speedData hκ).q x)) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let S := P.speedData hκ
  apply locallyAC_hasDerivAt_of_continuous (d := fun x =>
    κ*P.density hκ x-chebyshev2.Calibration.Q (S.q x)) S.q_locallyAC _ _ x
  · filter_upwards [S.q_derivative_ae] with x hx
    convert hx using 1
    have hi := S.density_identity hκ x
    change κ*S.density κ x=S.speed x+S.q x*(2-S.q x) at hi
    change κ*S.density κ x-S.q x*(2-S.q x)=S.speed x
    linarith
  · exact (continuous_const.mul (P.density_continuous hκ)).sub
      (S.q_continuous.mul (continuous_const.sub S.q_continuous))

/--
Smoothness to the stated order: `ContDiff ℝ 1 (P.speedData hκ).q`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.2.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem coordinate_c1 : ContDiff ℝ 1 (P.speedData hκ).q := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (P.coordinate_derivative hκ x).differentiableAt,?_⟩
  have he : deriv (P.speedData hκ).q=fun x =>
      κ*P.density hκ x-chebyshev2.Calibration.Q ((P.speedData hκ).q x) :=
    funext (fun x => (P.coordinate_derivative hκ x).deriv)
  rw [he]
  exact (continuous_const.mul (P.density_continuous hκ)).sub
    ((P.speedData hκ).q_continuous.mul
      (continuous_const.sub (P.speedData hκ).q_continuous))

end
end chebyshev2.Comparison.Profile
