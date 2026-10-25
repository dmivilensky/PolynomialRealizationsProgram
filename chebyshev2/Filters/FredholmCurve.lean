import chebyshev2.Continuum.RankOneFredholm
import chebyshev2.Continuum.TraceClassFeature
import chebyshev2.HalfLine.FeatureResolvent
import chebyshev2.Filters.Cumulative

/-!
Article: chebyshev2, Proposition 3.
Spatial truncation in the nuclear norm, rather than just operator norm.
Use: `chebyshev2.Filters.leftLogDeterminant_locallyAC` feeds
`chebyshev2.Filters.leftLogDeterminant_eq_log_truncatedTransmission` (The two spatial logarithms
have identical AE derivatives and the same normalization at the left endpoint).
Proof chain: `chebyshev2.Comparison.Profile.signed_determinant_comparison` — chebyshev2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.HalfLine
open scoped InnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false

/--
Spatial truncation in the nuclear norm, rather than just operator norm.

Use: `chebyshev2.Filters.leftLogDeterminant_distance` uses this definition to establish the
stated quantitative bound `|leftLogDeterminant hm hn s y-leftLogDeterminant hm hn s x| ≤
s/2*‖leftTraceClass m y-leftTraceClass m x‖`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.
-/
def leftTraceClass (m : ℝ → ℝ) (x : ℝ) : TraceClassOperator FeatureSpace :=
  ∫ t in Iic x, m t • traceClassFeature t

/--
Exact identity `leftTraceClass m x=traceClassDensityOperator (leftDensity m x)`.

Use: `chebyshev2.Filters.leftTraceClass_val` rewrites with this identity to establish exact
identity `(leftTraceClass m x).val=densityOperator (leftDensity m x)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral.
-/
theorem leftTraceClass_eq (m : ℝ → ℝ) (x : ℝ) :
    leftTraceClass m x=traceClassDensityOperator (leftDensity m x) := by
  rw [leftTraceClass,integral_Iic_eq_integral_Iio,traceClassDensityOperator,
    ← integral_indicator measurableSet_Iio]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    by_cases ht : t < x <;> simp [leftDensity,ht])

/--
Exact identity `(leftTraceClass m x).val=densityOperator (leftDensity m x)`.

Use: `chebyshev2.Filters.leftLogDeterminant_distance` rewrites with this identity to
establish the stated quantitative bound `|leftLogDeterminant hm hn s y-leftLogDeterminant hm hn
s x| ≤ s/2*‖leftTraceClass m y-leftTraceClass m x‖`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Filters.leftTraceClass_eq`,
`chebyshev2.Continuum.traceClassDensityOperator_val`,
`chebyshev2.HalfLine.leftDensity_integrable` with the arguments shown in the proof.
-/
theorem leftTraceClass_val {m : ℝ → ℝ} (hm : Integrable m) (x : ℝ) :
    (leftTraceClass m x).val=densityOperator (leftDensity m x) := by rw [leftTraceClass_eq m x,traceClassDensityOperator_val (leftDensity_integrable hm x)]

/--
Exact identity `leftTraceClass m y-leftTraceClass m x = ∫ t in x..y, m t • traceClassFeature
t`.

Use: `chebyshev2.Filters.leftTraceClass_derivative` rewrites with this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(leftTraceClass m) (m x • traceClassFeature x) x`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem leftTraceClass_sub {m : ℝ → ℝ} (hm : Integrable m) (x y : ℝ) :
    leftTraceClass m y-leftTraceClass m x = ∫ t in x..y, m t • traceClassFeature t :=
  (intervalIntegral.integral_Iic_sub_Iic (μ := volume) (a := x) (b := y)
    (f := fun t => m t • traceClassFeature t) (traceClassDensity_integrable hm).integrableOn
    (traceClassDensity_integrable hm).integrableOn)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(leftTraceClass m) (m x • traceClassFeature x) x`.

Use: `chebyshev2.Filters.leftLogDeterminant_eq_log_truncatedTransmission` uses this
assertion to establish the identity `leftLogDeterminant hm hn s x=log (truncatedTransmission
s m x)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem leftTraceClass_derivative {m : ℝ → ℝ} (hm : Integrable m) :
    ∀ᵐ x, HasDerivAt (leftTraceClass m) (m x • traceClassFeature x) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (traceClassDensity_integrable hm).locallyIntegrable]
    with x hx
  have he (y : ℝ) : leftTraceClass m y = leftTraceClass m 0+
      ∫ t in (0:ℝ)..y, m t • traceClassFeature t := by
    rw [← leftTraceClass_sub hm]
    abel
  simpa only [← he] using (hx 0).const_add (leftTraceClass m 0)

/--
The stated quantitative bound `‖leftTraceClass m y-leftTraceClass m x‖ ≤ |cumulative m
y-cumulative m x|`.

Use: `chebyshev2.Filters.leftLogDeterminant_locallyAC` uses this bound to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(leftLogDeterminant hm hn s) a b`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem leftTraceClass_norm_sub {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x y : ℝ) : ‖leftTraceClass m y-leftTraceClass m x‖ ≤ |cumulative m y-cumulative m x| := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  wlog hxy : x ≤ y generalizing x y
  · rw [norm_sub_rev,abs_sub_comm]
    exact this y x (le_of_not_ge hxy)
  rw [leftTraceClass_sub hm]
  have h := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := fun t => m t • traceClassFeature t) hxy
  have he : (fun t => ‖m t • traceClassFeature t‖)=m := by
    funext t
    rw [norm_smul,traceClassFeature_norm,mul_one,Real.norm_eq_abs,abs_of_nonneg (hn t)]
  rw [he] at h
  have hi : (∫ t in x..y, m t)=cumulative m y-cumulative m x :=
    (intervalIntegral.integral_Iic_sub_Iic (a := x) (b := y) hm.integrableOn hm.integrableOn).symm
  exact h.trans (by rw [hi]; exact le_abs_self _)

/--
Defines `leftLogDeterminant` of type `ℝ` by `logDeterminant (densitySpectralData
(leftDensity_integrable hm x) (leftDensity_nonneg hn x)).eigenvalue s`.

Use: `chebyshev2.Filters.leftLogDeterminant_distance` uses this definition to establish the
stated quantitative bound `|leftLogDeterminant hm hn s y-leftLogDeterminant hm hn s x| ≤
s/2*‖leftTraceClass m y-leftTraceClass m x‖`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.
-/
def leftLogDeterminant {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (s x : ℝ) : ℝ :=
  logDeterminant (densitySpectralData (leftDensity_integrable hm x) (leftDensity_nonneg hn x)).eigenvalue s

/--
The stated quantitative bound `|leftLogDeterminant hm hn s y-leftLogDeterminant hm hn s x| ≤
s/2*‖leftTraceClass m y-leftTraceClass m x‖`.

Use: `chebyshev2.Filters.leftLogDeterminant_locallyAC` uses this bound to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(leftLogDeterminant hm hn s) a b`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Continuum.IsTraceClass.traceBound`,
`chebyshev2.Continuum.logDeterminant_traceBound`,
`chebyshev2.Continuum.densityOperator_isCompact` with the arguments shown in the proof.
-/
theorem leftLogDeterminant_distance {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x y : ℝ) :
    |leftLogDeterminant hm hn s y-leftLogDeterminant hm hn s x| ≤
      s/2*‖leftTraceClass m y-leftTraceClass m x‖ := by
  -- Use the identities/estimates `chebyshev2.Continuum.IsTraceClass.traceBound`,
  -- `chebyshev2.Continuum.logDeterminant_traceBound`,
  -- `chebyshev2.Continuum.densityOperator_isCompact` with the arguments shown in the
  -- proof.
  have h := (leftTraceClass m y-leftTraceClass m x).property.traceBound
  change TraceBound (leftTraceClass m y-leftTraceClass m x).val
    ‖leftTraceClass m y-leftTraceClass m x‖ at h
  simp only [TraceClassOperator.val_sub,leftTraceClass_val hm] at h
  exact logDeterminant_traceBound
    (densityOperator_isCompact (leftDensity_integrable hm y))
    (densityOperator_isCompact (leftDensity_integrable hm x))
    (densityOperator_positive (leftDensity_integrable hm y) (leftDensity_nonneg hn y))
    (densityOperator_positive (leftDensity_integrable hm x) (leftDensity_nonneg hn x))
    (densitySpectralData (leftDensity_integrable hm y) (leftDensity_nonneg hn y))
    (densitySpectralData (leftDensity_integrable hm x) (leftDensity_nonneg hn x)) h hs

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval f a b`.

Use: `chebyshev2.Filters.leftLogDeterminant_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(leftLogDeterminant hm hn s) a b`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem locallyAC_of_dist_le {f g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) (h : ∀ x y, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  apply squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    (fun E => Finset.sum_le_sum (fun i _ => h (E.2 i).1 (E.2 i).2)) hg

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(leftLogDeterminant hm hn s) a b`.

Use: `chebyshev2.Filters.leftLogDeterminant_eq_log_truncatedTransmission` uses this
assertion to establish the identity `leftLogDeterminant hm hn s x=log (truncatedTransmission
s m x)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Filters.locallyAC_of_dist_le`,
`chebyshev2.Filters.cumulative_locallyAC`,
`chebyshev2.Filters.leftLogDeterminant_distance` with the arguments shown in the proof.
-/
theorem leftLogDeterminant_locallyAC {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (leftLogDeterminant hm hn s) a b := by
  apply locallyAC_of_dist_le ((cumulative_locallyAC hm a b).const_mul (s/2))
  intro x y
  rw [Real.dist_eq,Real.dist_eq,← mul_sub,abs_mul,abs_of_nonneg (show 0 ≤ s/2 by positivity)]
  exact (leftLogDeterminant_distance hm hn hs y x).trans
    (mul_le_mul_of_nonneg_left (leftTraceClass_norm_sub hm hn y x) (by positivity))

end
end chebyshev2.Filters
