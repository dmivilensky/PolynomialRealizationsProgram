import chebyshev2.Calibration.Reciprocal
import chebyshev2.Filters.SpectralObservations

/-!
Article: chebyshev2, Lemma 10.
Regularity of the actual density of Definition 6.
Result: `chebyshev2.Calibration.Data.comparisonDensity_bounded` supplies the stated article
conclusion.
-/
namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.PrescribedSpeed chebyshev2.GroundState chebyshev2.Filters
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : chebyshev2.Calibration.Data) {κ : ℝ} (hκ : 0 < κ)

/--
Exact identity `C.comparisonDensity hκ x=(C.amplitude κ ((C.comparisonSpeed hκ).q x))^2`.

Use: `chebyshev2.Calibration.Data.comparisonDensity_bounded` rewrites with this identity to
establish constructs witnesses with the exact properties `∃ B : ℝ, 0 ≤ B ∧ ∀ x,
C.comparisonDensity hκ x ≤ B`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem comparisonDensity_formula (x : ℝ) :
    C.comparisonDensity hκ x=(C.amplitude κ ((C.comparisonSpeed hκ).q x))^2 := by
  -- Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  let S := C.comparisonSpeed hκ
  by_cases hx : x ∈ Ioo (S.X 0) (S.X 2)
  · exact C.comparisonDensity_amplitude hκ hx
  · change S.density κ x=(C.amplitude κ (S.q x))^2
    rw [S.density_zero_outside κ hx]
    rcases le_or_gt x (S.X 0) with hl | hl
    · rw [S.q_zero_left hl,C.amplitude_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    · have hr : S.X 2 ≤ x := not_lt.mp (fun hr => hx ⟨hl,hr⟩)
      rw [S.q_two_right hr,C.amplitude_two,zero_pow (by norm_num : (2:ℕ) ≠ 0)]

/--
Continuity of the displayed function: `Continuous (C.comparisonDensity hκ)`.

Use: `chebyshev2.Calibration.Data.comparisonCoordinate_c1` uses this continuity result to
establish smoothness to the stated order: `ContDiff ℝ 1 (C.comparisonSpeed hκ).q`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem comparisonDensity_continuous : Continuous (C.comparisonDensity hκ) := by
  have he : C.comparisonDensity hκ=fun x => (C.amplitude κ ((C.comparisonSpeed hκ).q x))^2 :=
    funext (C.comparisonDensity_formula hκ)
  rw [he]
  exact ((C.amplitude_continuousOn_fixed hκ).comp_continuous
    (C.comparisonSpeed hκ).q_continuous (C.comparisonSpeed hκ).q_mem).pow 2

/--
Constructs witnesses with the exact properties `∃ B : ℝ, 0 ≤ B ∧ ∀ x, C.comparisonDensity hκ x
≤ B`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 10.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_bounded`,
`chebyshev2.Calibration.Data.comparisonDensity_formula`,
`chebyshev2.Calibration.Data.amplitude_nonneg` with the arguments shown in the proof.
-/
theorem comparisonDensity_bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, C.comparisonDensity hκ x ≤ B := by
  obtain ⟨M,hM,hm⟩ := C.amplitude_bounded hκ
  refine ⟨M^2,sq_nonneg _,?_⟩
  intro x
  rw [C.comparisonDensity_formula hκ]
  exact pow_le_pow_left₀ (C.amplitude_nonneg hκ _) (hm _ ((C.comparisonSpeed hκ).q_mem x)) 2

/--
The actual derivative at the stated point: `HasDerivAt (C.comparisonSpeed hκ).q
(κ*C.comparisonDensity hκ x-chebyshev2.Calibration.Q ((C.comparisonSpeed hκ).q x)) x`.

Use: `chebyshev2.Calibration.Data.comparisonCoordinate_c1` uses this derivative formula to
establish smoothness to the stated order: `ContDiff ℝ 1 (C.comparisonSpeed hκ).q`.

Article: chebyshev2, Lemma 10.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem comparisonCoordinate_derivative (x : ℝ) :
    HasDerivAt (C.comparisonSpeed hκ).q
      (κ*C.comparisonDensity hκ x-chebyshev2.Calibration.Q ((C.comparisonSpeed hκ).q x)) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let S := C.comparisonSpeed hκ
  apply locallyAC_hasDerivAt_of_continuous (d := fun x =>
    κ*C.comparisonDensity hκ x-chebyshev2.Calibration.Q (S.q x)) S.q_locallyAC _ _ x
  · filter_upwards [S.q_derivative_ae] with x hx
    convert hx using 1
    have hi := S.density_identity hκ x
    change κ*S.density κ x=S.speed x+S.q x*(2-S.q x) at hi
    change κ*S.density κ x-S.q x*(2-S.q x)=S.speed x
    linarith
  · exact (continuous_const.mul (C.comparisonDensity_continuous hκ)).sub
      (S.q_continuous.mul (continuous_const.sub S.q_continuous))

/--
Smoothness to the stated order: `ContDiff ℝ 1 (C.comparisonSpeed hκ).q`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 10.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem comparisonCoordinate_c1 : ContDiff ℝ 1 (C.comparisonSpeed hκ).q := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (C.comparisonCoordinate_derivative hκ x).differentiableAt,?_⟩
  have he : deriv (C.comparisonSpeed hκ).q=fun x =>
      κ*C.comparisonDensity hκ x-chebyshev2.Calibration.Q ((C.comparisonSpeed hκ).q x) :=
    funext (fun x => (C.comparisonCoordinate_derivative hκ x).deriv)
  rw [he]
  exact (continuous_const.mul (C.comparisonDensity_continuous hκ)).sub
    ((C.comparisonSpeed hκ).q_continuous.mul
      (continuous_const.sub (C.comparisonSpeed hκ).q_continuous))

end
end chebyshev2.Calibration.Data
