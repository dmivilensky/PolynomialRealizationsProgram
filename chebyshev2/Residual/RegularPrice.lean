import chebyshev2.Residual.RegularPriceCost
import chebyshev2.Residual.IntervalPrice

/-!
Article: chebyshev2, Lemma 16.
The regular price of (26) is an admissible bounded piecewise continuous price for every bounded
piecewise continuous e.
Use: `chebyshev2.Calibration.Data.regularPriceData_cost` feeds
`chebyshev2.DualCertificate.Data.price_cost` (price cost).
Proof chain: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` — chebyshev2,
Theorem E.1; Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.Residual
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : chebyshev2.Calibration.Data) {κ : ℝ} (hκ : 0 < κ)
include hκ

/--
Integrability on the stated domain: `IntegrableOn (fun q => C.amplitude κ q*e.value q) (Ioo
(0:ℝ) 2)`.

Use: `chebyshev2.Calibration.Data.regularPriceData_cost` uses this integrability result to
establish the precise assertion is `priceCost κ τ (C.regularPriceData hκ τ e).value= (∫ q in
Ioo (0:ℝ) 2, C.amplitude κ q*e.value q)/κ+ τ*(1-∫ x, C.comparisonDensity hκ x)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem amplitude_mul_price_integrable (e : Price) :
    IntegrableOn (fun q => C.amplitude κ q*e.value q) (Ioo (0:ℝ) 2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  obtain ⟨M,_,hM⟩ := C.amplitude_bounded hκ
  apply (integrableOn_const (C := M*e.B) (s := Ioo (0:ℝ) 2)
    (by rw [volume_Ioo]; exact ENNReal.ofReal_ne_top)).mono'
  · exact (((C.amplitude_continuousOn_fixed hκ).mono Ioo_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioo).mul e.measurable.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    rw [norm_mul,Real.norm_of_nonneg (C.amplitude_nonneg hκ q)]
    exact mul_le_mul (hM _ ⟨hq.1.le,hq.2.le⟩) (e.bound q) (norm_nonneg _) (by linarith [C.amplitude_nonneg hκ q,hM _ ⟨hq.1.le,hq.2.le⟩])

/--
Continuity at the stated point: `ContinuousAt (C.regularPrice (κ := κ) τ e.value) q`.

Use: `chebyshev2.Calibration.Data.regularPriceData` uses this continuity result in the
displayed construction of `regularPriceData`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then
prove the asserted relation at an arbitrary point in that intersection.
-/
theorem regularPrice_continuousAt (τ : ℝ) (e : Price) {q : ℝ}
    (h0 : q ≠ 0) (h2 : q ≠ 2) (he : q ∉ e.exceptional) :
    ContinuousAt (C.regularPrice (κ := κ) τ e.value) q := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hq : q ∈ Ioo (0:ℝ) 2
  · have hν := (C.amplitude_continuousOn_fixed hκ).continuousAt (Icc_mem_nhds hq.1 hq.2)
    -- Establish continuity hQ before using the function at limits or in calculus arguments.
    have hQ : ContinuousAt chebyshev2.Calibration.Q q := by unfold chebyshev2.Calibration.Q; fun_prop
    -- Establish continuity hd before using the function at limits or in calculus arguments.
    have hd : ContinuousAt (C.speed κ) q := (continuousAt_const.mul (hν.pow 2)).sub hQ
    -- Establish continuity hc before using the function at limits or in calculus arguments.
    have hc : ContinuousAt (fun t => -τ*chebyshev2.Calibration.Q t/C.speed κ t+
        C.amplitude κ t*e.value t) q :=
      (((continuousAt_const.mul hQ).div hd (C.speed_positive hκ hq).ne').add
        (hν.mul (e.continuous q he)))
    apply hc.congr
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with t ht
    exact (indicator_of_mem ht (fun t => -τ*chebyshev2.Calibration.Q t/C.speed κ t+
      C.amplitude κ t*e.value t)).symm
  · have hqC : q ∉ Icc (0:ℝ) 2 := by
      intro hc
      exact hq ⟨lt_of_le_of_ne hc.1 (Ne.symm h0),lt_of_le_of_ne hc.2 h2⟩
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) q).congr
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hqC] with t ht
    exact (indicator_of_notMem (fun hi => ht ⟨hi.1.le,hi.2.le⟩)
      (fun t => -τ*chebyshev2.Calibration.Q t/C.speed κ t+C.amplitude κ t*e.value t)).symm

/--
The stated quantitative bound `‖C.regularPrice (κ := κ) τ e.value q‖ ≤ |τ|/2+M*e.B`.

Use: `chebyshev2.Calibration.Data.regularPriceData` uses this identity in the displayed
construction of `regularPriceData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem regularPrice_bound (τ : ℝ) (e : Price) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ q ∈ Icc (0:ℝ) 2, C.amplitude κ q ≤ M) (q : ℝ) :
    ‖C.regularPrice (κ := κ) τ e.value q‖ ≤ |τ|/2+M*e.B := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hq : q ∈ Ioo (0:ℝ) 2
  · rw [regularPrice,indicator_of_mem hq]
    have hQ := chebyshev2.Calibration.Q_positive hq
    have hd := C.speed_positive hκ hq
    have hν := C.amplitude_nonneg hκ q
    have hr : chebyshev2.Calibration.Q q/C.speed κ q ≤ 1/2 := by
      apply (div_le_iff₀ hd).2
      linarith [C.speed_gt_two_Q hκ hq]
    apply (norm_add_le _ _).trans
    have h1 : ‖-τ*chebyshev2.Calibration.Q q/C.speed κ q‖ ≤ |τ|/2 := by
      rw [norm_div,norm_mul,Real.norm_eq_abs,abs_neg,Real.norm_of_nonneg hQ.le,Real.norm_of_nonneg hd.le]
      have h := mul_le_mul_of_nonneg_left hr (abs_nonneg τ)
      convert h using 1 <;> ring
    have h2 : ‖C.amplitude κ q*e.value q‖ ≤ M*e.B := by
      rw [norm_mul,Real.norm_of_nonneg hν]
      exact mul_le_mul (hb q ⟨hq.1.le,hq.2.le⟩) (e.bound q) (norm_nonneg _) hM
    exact add_le_add h1 h2
  · rw [regularPrice,indicator_of_notMem hq,norm_zero]
    exact add_nonneg (by positivity) (mul_nonneg hM e.bound_nonneg)

/--
Constructs `regularPriceData` of type `Price` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.Calibration.Data.regularPriceData_cost` uses this definition to establish
the precise assertion is `priceCost κ τ (C.regularPriceData hκ τ e).value= (∫ q in Ioo (0:ℝ) 2,
C.amplitude κ q*e.value q)/κ+ τ*(1-∫ x, C.comparisonDensity hκ x)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def regularPriceData (τ : ℝ) (e : Price) : Price where
  value := C.regularPrice (κ := κ) τ e.value
  exceptional := insert 0 (insert 2 e.exceptional)
  continuous := fun q hq => C.regularPrice_continuousAt hκ τ e
    (fun he => hq (by simp [he])) (fun he => hq (by simp [he])) (fun he => hq (by simp [he]))
  B := |τ|/2+Classical.choose (C.amplitude_bounded hκ)*e.B
  bound_nonneg := add_nonneg (by positivity)
    (mul_nonneg (Classical.choose_spec (C.amplitude_bounded hκ)).1.le e.bound_nonneg)
  bound := C.regularPrice_bound hκ τ e
    (Classical.choose_spec (C.amplitude_bounded hκ)).1.le
    (Classical.choose_spec (C.amplitude_bounded hκ)).2

/--
The precise assertion is `priceCost κ τ (C.regularPriceData hκ τ e).value= (∫ q in Ioo (0:ℝ) 2,
C.amplitude κ q*e.value q)/κ+ τ*(1-∫ x, C.comparisonDensity hκ x)`.

Use: `chebyshev2.DualCertificate.Data.price_cost` rewrites with this identity to establish
the precise assertion is `priceCost κ (D.τ:ℝ) (D.price hκ).value= (∫ q in Ioo (0:ℝ)
2,D.calibration.amplitude κ q*D.cellPrice q)/κ+ (D.τ:ℝ)*(1-∫ x,D.calibration.comparisonDensity
hκ x)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.regularPrice_cost`,
`chebyshev2.Calibration.Data.amplitude_mul_price_integrable` with the arguments shown in
the proof.
-/
theorem regularPriceData_cost (τ : ℝ) (e : Price) :
    priceCost κ τ (C.regularPriceData hκ τ e).value=
      (∫ q in Ioo (0:ℝ) 2, C.amplitude κ q*e.value q)/κ+
        τ*(1-∫ x, C.comparisonDensity hκ x) :=
  C.regularPrice_cost hκ τ e.value (C.amplitude_mul_price_integrable hκ e)

end
end chebyshev2.Calibration.Data
