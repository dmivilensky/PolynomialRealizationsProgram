import chebyshev2.SineContinuum.SineCoordinate
import chebyshev2.SineContinuum.KernelIdentity

/-!
Article: chebyshev2, Proposition 2.
The full real-line change of variables is an equality of actual measures.
Use: `chebyshev2.SineContinuum.T_interval_measurePreserving` feeds
`chebyshev2.SineContinuum.sineRealHilbertBasis_ae` (sine Real Hilbert Basis ae).
Proof chain: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` — chebyshev2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real Filter MeasureTheory
open scoped ENNReal
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/--
Defines `interiorInterval` of type `Set LegendreInterval` by `{t | (t:ℝ) ∈ Ioo (0:ℝ) 1}`.

Use: `chebyshev2.SineContinuum.X_interval_measurable` uses this definition to establish
measurability of the displayed map: `Measurable (fun t : LegendreInterval => X t)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def interiorInterval : Set LegendreInterval := {t | (t:ℝ) ∈ Ioo (0:ℝ) 1}

/--
Measurability of the displayed map: `Measurable (fun t : LegendreInterval => X t)`.

Use: `chebyshev2.SineContinuum.T_interval_measurePreserving` rewrites with this
measurability result to establish `MeasurePreserving T_interval volume
realLineWeight.measure`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.X_continuousOn` with the
arguments shown in the proof.
-/
theorem X_interval_measurable : Measurable (fun t : LegendreInterval => X t) := by
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousOn (fun t : LegendreInterval => X t) interiorInterval :=
    X_continuousOn.comp continuous_subtype_val.continuousOn (fun _ ht => ht)
  apply hc.measurable_of_countable_compl
  apply (show ({(0:LegendreInterval),(1:LegendreInterval)} : Set LegendreInterval).Countable from
    ((finite_singleton _).insert _).countable).mono
  intro t ht
  have hh : ¬ (t:ℝ) ∈ Ioo (0:ℝ) 1 := ht
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with h | h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h
  · exact (hh h).elim

/--
The stated quantitative bound `0 ≤ SineJacobi.phi t`.

Use: `chebyshev2.SineContinuum.realLineWeight_density` rewrites with this bound to
establish exact identity `realLineWeight.density t=ENNReal.ofReal ((SineJacobi.phi t)⁻¹)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.phi_product`,
`chebyshev2.SineContinuum.l_zero`, `chebyshev2.SineContinuum.l_one` with the arguments
shown in the proof.
-/
theorem phi_interval_nonnegative (t : LegendreInterval) : 0 ≤ SineJacobi.phi t := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with h | h | h
  · rw [h,phi_product,l_zero]; simp
  · rw [h,phi_product,l_one]; simp
  · exact (SineJacobi.phi_pos h).le

/--
Constructs `realLineWeight` of type `Continuum.L2Weight (volume : Measure LegendreInterval)` by
the displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `chebyshev2.SineContinuum.T_interval_measurePreserving` uses this definition to
establish the precise assertion is `MeasurePreserving T_interval volume
realLineWeight.measure`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def realLineWeight : Continuum.L2Weight (volume : Measure LegendreInterval) where
  w t := (√(SineJacobi.phi t))⁻¹
  measurable := by
    have hc : Continuous (fun t : LegendreInterval => SineJacobi.phi t) :=
      phi_continuousOn.comp_continuous continuous_subtype_val (fun t => t.property)
    exact hc.measurable.sqrt.inv
  nonzero := by
    filter_upwards [interval_interior_ae] with t ht
    exact inv_ne_zero (sqrt_pos.mpr (SineJacobi.phi_pos ht)).ne'

/--
Exact identity `realLineWeight.density t=ENNReal.ofReal ((SineJacobi.phi t)⁻¹)`.

Use: `chebyshev2.SineContinuum.X_interval_measurePreserving` rewrites with this identity to
establish the stated quantitative bound `MeasurePreserving (fun t : LegendreInterval => X t)
realLineWeight.measure volume`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.phi_interval_nonnegative`
with the arguments shown in the proof.
-/
theorem realLineWeight_density (t : LegendreInterval) :
    realLineWeight.density t=ENNReal.ofReal ((SineJacobi.phi t)⁻¹) := by
  dsimp [Continuum.L2Weight.density,realLineWeight]
  rw [inv_pow,sq_sqrt (phi_interval_nonnegative t)]

/--
Exact identity `(∫⁻ x, g x)=∫⁻ t in Ioo (0:ℝ) 1, ENNReal.ofReal ((SineJacobi.phi t)⁻¹)*g (X
t)`.

Use: `chebyshev2.SineContinuum.X_interval_measurePreserving` rewrites with this identity to
establish the stated quantitative bound `MeasurePreserving (fun t : LegendreInterval => X t)
realLineWeight.measure volume`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem coordinate_lintegral (g : ℝ → ℝ≥0∞) :
    (∫⁻ x, g x)=∫⁻ t in Ioo (0:ℝ) 1, ENNReal.ofReal ((SineJacobi.phi t)⁻¹)*g (X t) := by
  have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioo
    (fun _ ht => (X_derivative ht).hasDerivWithinAt) X_strictMono.monotoneOn g
  rw [X_image_univ,Measure.restrict_univ] at h
  exact h

/--
The full real-line change of variables is an equality of actual measures.

The stated quantitative bound `MeasurePreserving (fun t : LegendreInterval => X t)
realLineWeight.measure volume`.

Use: `chebyshev2.SineContinuum.T_interval_measurePreserving` rewrites with this identity to
establish the precise assertion is `MeasurePreserving T_interval volume
realLineWeight.measure`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Separate `X (t:ℝ) ∈ s` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem X_interval_measurePreserving :
    MeasurePreserving (fun t : LegendreInterval => X t) realLineWeight.measure volume := by
  -- Separate `X (t:ℝ) ∈ s` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  constructor
  · exact X_interval_measurable
  · apply Measure.ext
    intro s hs
    rw [Measure.map_apply X_interval_measurable hs,Continuum.L2Weight.measure,
      withDensity_apply _ (X_interval_measurable hs)]
    have he : (∫⁻ t in (fun t : LegendreInterval => X t) ⁻¹' s, realLineWeight.density t)=
        ∫⁻ t : LegendreInterval, ENNReal.ofReal ((SineJacobi.phi t)⁻¹)*s.indicator (fun _ => 1) (X t) := by
      rw [← lintegral_indicator (X_interval_measurable hs)]
      apply lintegral_congr
      intro t
      by_cases ht : X (t:ℝ) ∈ s <;> simp [ht,realLineWeight_density]
    rw [he]
    change (∫⁻ t : LegendreInterval, ENNReal.ofReal ((SineJacobi.phi t)⁻¹)*s.indicator (fun _ => 1) (X t)
      ∂volume.comap ((↑) : LegendreInterval → ℝ))=_
    rw [lintegral_subtype_comap (s := Icc (0:ℝ) 1) measurableSet_Icc
      (fun t : ℝ => ENNReal.ofReal ((SineJacobi.phi t)⁻¹)*s.indicator (fun _ => 1) (X t))]
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm,← coordinate_lintegral]
    simp [hs]

/--
Defines `T_interval` of type `LegendreInterval` by `⟨T x,⟨(T_mem x).1.le,(T_mem x).2.le⟩⟩`.

Use: `chebyshev2.SineContinuum.T_interval_measurePreserving` uses this definition to
establish the precise assertion is `MeasurePreserving T_interval volume
realLineWeight.measure`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def T_interval (x : ℝ) : LegendreInterval := ⟨T x,⟨(T_mem x).1.le,(T_mem x).2.le⟩⟩

/--
Measurability of the displayed map: `Measurable T_interval`.

Use: `chebyshev2.SineContinuum.T_interval_measurePreserving` rewrites with this
measurability result to establish `MeasurePreserving T_interval volume
realLineWeight.measure`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.T_continuous` with the
arguments shown in the proof.
-/
theorem T_interval_measurable : Measurable T_interval :=
  T_continuous.measurable.subtype_mk

/--
The precise assertion is `MeasurePreserving T_interval volume realLineWeight.measure`.

Use: `chebyshev2.SineContinuum.realLinePullback` uses this assertion in the displayed
construction of `realLinePullback`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem T_interval_measurePreserving : MeasurePreserving T_interval volume realLineWeight.measure := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  constructor
  · exact T_interval_measurable
  · rw [← X_interval_measurePreserving.map_eq,Measure.map_map T_interval_measurable X_interval_measurable]
    have he : (T_interval ∘ (fun t : LegendreInterval => X t))=ᵐ[realLineWeight.measure] id := by
      apply realLineWeight.weight_ac.ae_eq
      filter_upwards [interval_interior_ae] with t ht
      exact Subtype.ext (T_X ht)
    rw [Measure.map_congr he,Measure.map_id]

end
end chebyshev2.SineContinuum
