import «2610.05164v2».DualCertificate.UniformCertificate
import «2610.05164v2».SineContinuum.EnergyArticle

/-!
Article: 2610.05164v2, Section 4.1.
Uniform transfer and the exact budget for the one-determinant 1.000013 guarantee, instantiated by
Compact.ReferenceBase.
Use: `«2610.05164v2».DualCertificate.one_det_uniform_of_value` feeds
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` (uniform gain
improvement).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».DualCertificate
noncomputable section
open Set Filter Real «2610.05164v2».Optimal
open scoped Topology
set_option autoImplicit false

/--
Defines `coarseSineUpper` of type `ℚ` by `114269221 / 100000000`.

Use: `«2610.05164v2».DualCertificate.coarse_sine_upper` uses this definition to establish the
stated quantitative bound `«2610.05164v2».SineJacobi.energy < (coarseSineUpper : ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def coarseSineUpper : ℚ := 114269221 / 100000000
/--
Defines `oneDetLower` of type `ℚ` by `1142663 / 1000000`.

Use: `«2610.05164v2».DualCertificate.one_det_factor_budget` uses this definition to establish
the stated quantitative bound `(coarseSineUpper : ℝ) < (oneDetGainFactor : ℝ)^2 * (oneDetLower
: ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def oneDetLower : ℚ := 1142663 / 1000000
/--
Defines `oneDetGainFactor` of type `ℚ` by `1000013 / 1000000`.

Use: `«2610.05164v2».DualCertificate.one_det_factor_budget` uses this definition to establish
the stated quantitative bound `(coarseSineUpper : ℝ) < (oneDetGainFactor : ℝ)^2 * (oneDetLower
: ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def oneDetGainFactor : ℚ := 1000013 / 1000000

/--
The stated quantitative bound `«2610.05164v2».SineJacobi.energy < (coarseSineUpper : ℝ)`.

Use: `«2610.05164v2».DualCertificate.one_det_uniform_of_value` uses this bound to establish the
bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».SineJacobi.energy_decimal` with the
arguments shown in the proof.
-/
theorem coarse_sine_upper : «2610.05164v2».SineJacobi.energy < (coarseSineUpper : ℝ) := by
  convert «2610.05164v2».SineJacobi.energy_decimal.2 using 1
  norm_num [coarseSineUpper]

/--
The stated quantitative bound `(coarseSineUpper : ℝ) < (oneDetGainFactor : ℝ)^2 * (oneDetLower
: ℝ)`.

Use: `«2610.05164v2».DualCertificate.one_det_uniform_of_value` uses this bound to establish the
bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem one_det_factor_budget :
    (coarseSineUpper : ℝ) < (oneDetGainFactor : ℝ)^2 * (oneDetLower : ℝ) := by norm_num [coarseSineUpper, oneDetGainFactor, oneDetLower]

/--
This transfer works for any proved uniform finite-energy lower bound, including the
one-determinant route, without introducing a dual certificate.

Use: `«2610.05164v2».DualCertificate.one_det_uniform_of_value` uses this bound to establish the
bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem uniform_sine_of_finite_lower {L q : ℝ} (hq : 0 < q)
    (hE : «2610.05164v2».SineJacobi.energy < q^2 * L)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ J : «2610.05164v2».Fiber (n+1), L-ε ≤ J.val.normalizedEnergy) :
    ∀ᶠ n in atTop, ∀ I : «2606.16671v2».SpectralInterval, ∀ J : «2610.05164v2».Fiber (n+1),
      2 * sqrt («2610.05164v2».SineJacobi.chain (n+1)).normalizedEnergy <
        q * ((«2610.05164v2».recurrenceEquiv I (n+1) (by omega)) J).val.normalizedGain I := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let ε := (L-«2610.05164v2».SineJacobi.energy/q^2)/2
  have hε : 0 < ε := by
    have h := (div_lt_iff₀ (sq_pos_of_pos hq)).mpr (by simpa only [mul_comm] using hE)
    dsimp [ε]
    linarith
  have hm : «2610.05164v2».SineJacobi.energy < q^2 * (L-ε) := by
    dsimp [ε]
    field_simp
    nlinarith [hE]
  filter_upwards [hL ε hε, sineEnergy_limit.eventually (gt_mem_nhds hm)] with n hn hs I J
  have henergy := hs.trans_le (mul_le_mul_of_nonneg_left (hn J) (sq_nonneg q))
  have hsq : sqrt (q^2 * J.val.normalizedEnergy) = q * sqrt J.val.normalizedEnergy := by
    rw [sqrt_mul (sq_nonneg q), sqrt_sq_eq_abs, abs_of_pos hq]
  have hroot := sqrt_lt_sqrt
    (le_trans (by norm_num : (0 : ℝ) ≤ 1)
      ((«2610.05164v2».SineJacobi.chain (n+1)).normalizedEnergy_ge_one (by omega)
        («2610.05164v2».SineJacobi.fiber (n+1) (by omega)).property)) henergy
  rw [hsq] at hroot
  have hg := mul_le_mul_of_nonneg_left (J.val.normalizedGain_lower I (by omega) J.property) hq.le
  change 2 * sqrt («2610.05164v2».SineJacobi.chain (n+1)).normalizedEnergy <
    q * (J.val.recurrence I (J.val.admissible I (by omega) J.property)).normalizedGain I
  linarith

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ n in atTop, ∀ J :
«2610.05164v2».Fiber (n+1), C.referenceBase - ε ≤ J.val.normalizedEnergy`.

Use: `«2610.05164v2».DualCertificate.one_det_uniform_of_value` uses this bound to establish the
bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem one_det_uniform_lower (C : «2610.05164v2».Calibration.Data) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ J : «2610.05164v2».Fiber (n+1),
      C.referenceBase - ε ≤ J.val.normalizedEnergy := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have h := uniform_lower_of_all_sections
    (v := fun n (J : «2610.05164v2».Fiber (n+1)) =>
      C.base («2610.05164v2».Calibration.Data.packedCoupling J.val (by omega) J.property)
        («2610.05164v2».Packing.packedLogDeterminant J.val (by omega) J.property
          (C.sigma * «2610.05164v2».Calibration.Data.packedCoupling J.val (by omega) J.property)))
    (fun n => ⟨«2610.05164v2».SineJacobi.fiber (n+1) (by omega)⟩) C.packedBase_tendsto hε
  filter_upwards [h] with n hn J
  exact (hn J).trans (C.packed_energy_ge_base J.val (by omega) J.property)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ n in atTop, ∀ I :
«2606.16671v2».SpectralInterval, ∀ J : «2610.05164v2».Fiber (n+1), 2 * sqrt
(«2610.05164v2».SineJacobi.chain (n+1)).normalizedEnergy < (oneDetGainFactor : ℝ) *
((«2610.05164v2».recurrenceEquiv I (n+1) (by omega)) J).val.normalizedGain I`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` uses this
bound to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.uniform_sine_of_finite_lower`,
`«2610.05164v2».DualCertificate.coarse_sine_upper`,
`«2610.05164v2».DualCertificate.one_det_factor_budget` with the arguments shown in the proof.
-/
theorem one_det_uniform_of_value (C : «2610.05164v2».Calibration.Data)
    (hv : (oneDetLower : ℝ) ≤ C.referenceBase) :
    ∀ᶠ n in atTop, ∀ I : «2606.16671v2».SpectralInterval, ∀ J : «2610.05164v2».Fiber (n+1),
      2 * sqrt («2610.05164v2».SineJacobi.chain (n+1)).normalizedEnergy <
        (oneDetGainFactor : ℝ) *
          ((«2610.05164v2».recurrenceEquiv I (n+1) (by omega)) J).val.normalizedGain I := by
  -- Use the identities/estimates
  -- `«2610.05164v2».DualCertificate.uniform_sine_of_finite_lower`,
  -- `«2610.05164v2».DualCertificate.coarse_sine_upper`,
  -- `«2610.05164v2».DualCertificate.one_det_factor_budget` with the arguments shown in the
  -- proof.
  apply uniform_sine_of_finite_lower (by norm_num [oneDetGainFactor])
    (coarse_sine_upper.trans (one_det_factor_budget.trans_le
      (mul_le_mul_of_nonneg_left hv (sq_nonneg (oneDetGainFactor : ℝ)))))
  exact fun _ hε => one_det_uniform_lower C hε

end
end «2610.05164v2».DualCertificate
