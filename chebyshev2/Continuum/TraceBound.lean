import chebyshev2.Continuum.FeatureOperator
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
Article: chebyshev2, Theorem 2.3.
A dual characterization of an upper bound on the nuclear norm: all finite orthonormal-frame pairings
are bounded.
Use: `chebyshev2.Continuum.densityOperator_traceBound` feeds
`chebyshev2.Continuum.densityOperator_isTraceClass` (density Operator is Trace Class).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for trace-class
operators. The needed form is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open MeasureTheory Real
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
A dual characterization of an upper bound on the nuclear norm: all finite orthonormal-frame
pairings are bounded. This property refers to the actual map.

Use: `chebyshev2.Continuum.TraceBound.add` uses this definition to establish the precise
assertion is `TraceBound (S + T) (a + b)`.

Article: chebyshev2, Theorem 2.4 via `chebyshev2.Continuum.eigenvalue_l1_le_nuclearNorm`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def TraceBound (T : E →L[ℝ] E) (C : ℝ) : Prop :=
  ∀ n : ℕ, ∀ u v : Fin n → E, Orthonormal ℝ u → Orthonormal ℝ v →
    |∑ i, inner ℝ (u i) (T (v i))| ≤ C

/--
Defines `frameFunctional` of type `(E →L[ℝ] E) →L[ℝ] ℝ` by `∑ i, (innerSL ℝ (u i)).comp
(ContinuousLinearMap.apply ℝ E (v i))`.

Use: `chebyshev2.Continuum.frameFunctional_apply` rewrites with this definition to
establish exact identity `frameFunctional u v T = ∑ i, inner ℝ (u i) (T (v i))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def frameFunctional {n : ℕ} (u v : Fin n → E) : (E →L[ℝ] E) →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (u i)).comp (ContinuousLinearMap.apply ℝ E (v i))

/--
Exact identity `frameFunctional u v T = ∑ i, inner ℝ (u i) (T (v i))`.

Use: `chebyshev2.Continuum.traceBound_integral` rewrites with this identity to establish
the precise assertion is `TraceBound (∫ x, f x ∂μ) (∫ x, c x ∂μ)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem frameFunctional_apply {n : ℕ} (u v : Fin n → E) (T : E →L[ℝ] E) :
    frameFunctional u v T = ∑ i, inner ℝ (u i) (T (v i)) := by simp [frameFunctional]

/--
The precise assertion is `TraceBound (InnerProductSpace.rankOne ℝ a b) (‖a‖ * ‖b‖)`.

Use: `chebyshev2.Continuum.featureProjection_difference_traceBound` uses this assertion to
establish the precise assertion is `TraceBound (featureProjection x - featureProjection y) (2 *
‖feature x - feature y‖)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem traceBound_rankOne (a b : E) :
    TraceBound (InnerProductSpace.rankOne ℝ a b) (‖a‖ * ‖b‖) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  intro n u v hu hv
  have hau := hu.sum_inner_products_le a (s := Finset.univ)
  have hbv := hv.sum_inner_products_le b (s := Finset.univ)
  simp only [Real.norm_eq_abs, sq_abs] at hau hbv
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => inner ℝ (u i) a) (fun i => inner ℝ (v i) b)
  have hp := mul_le_mul hau hbv (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
  have he : (∑ i, inner ℝ (u i) ((InnerProductSpace.rankOne ℝ a b) (v i))) =
      ∑ i, inner ℝ (u i) a * inner ℝ (v i) b := by
    apply Finset.sum_congr rfl
    intro i _
    simp [InnerProductSpace.rankOne_apply, real_inner_smul_right, real_inner_comm, mul_comm]
  rw [he]
  have hn : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have ha : |∑ i, inner ℝ (u i) a * inner ℝ (v i) b| ^ 2 ≤ (‖a‖ * ‖b‖)^2 := by
    rw [sq_abs, mul_pow]
    exact hs.trans hp
  exact (sq_le_sq₀ (abs_nonneg _) hn).mp ha

/--
The precise assertion is `TraceBound (S + T) (a + b)`.

Use: `chebyshev2.Continuum.featureProjection_difference_traceBound` uses this assertion to
establish the precise assertion is `TraceBound (featureProjection x - featureProjection y) (2 *
‖feature x - feature y‖)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem TraceBound.add {S T : E →L[ℝ] E} {a b : ℝ}
    (hS : TraceBound S a) (hT : TraceBound T b) : TraceBound (S + T) (a + b) := by
  intro n u v hu hv
  simp only [add_apply, inner_add_right, Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans (add_le_add (hS n u v hu hv) (hT n u v hu hv))

/--
The precise assertion is `TraceBound T b`.

Use: `chebyshev2.Continuum.measureOperator_transport` uses this assertion to establish the
precise assertion is `TraceBound (measureOperator (μ.map Prod.fst) - measureOperator (μ.map
Prod.snd)) (2 * sqrt (2 * μ.real univ * ∫ z, |z.1-z.2| ∂μ))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem TraceBound.mono {T : E →L[ℝ] E} {a b : ℝ} (hT : TraceBound T a) (hab : a ≤ b) :
    TraceBound T b := fun n u v hu hv => (hT n u v hu hv).trans hab

/--
The precise assertion is `TraceBound (c • T) (|c| * a)`.

Use: `chebyshev2.Continuum.densityOperator_traceBound` uses this assertion to establish the
precise assertion is `TraceBound (densityOperator m) (∫ x, |m x|)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem TraceBound.smul {T : E →L[ℝ] E} {a : ℝ} (hT : TraceBound T a) (c : ℝ) :
    TraceBound (c • T) (|c| * a) := by
  intro n u v hu hv
  change |∑ i, inner ℝ (u i) (c • T (v i))| ≤ _
  simp only [real_inner_smul_right, ← Finset.mul_sum, abs_mul]
  exact mul_le_mul_of_nonneg_left (hT n u v hu hv) (abs_nonneg _)

variable [CompleteSpace E]

/--
The precise assertion is `TraceBound (∫ x, f x ∂μ) (∫ x, c x ∂μ)`.

Use: `chebyshev2.Continuum.densityOperator_traceBound` uses this assertion to establish the
precise assertion is `TraceBound (densityOperator m) (∫ x, |m x|)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem traceBound_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → E →L[ℝ] E} {c : α → ℝ} (hf : Integrable f μ) (hc : Integrable c μ)
    (hbound : ∀ᵐ x ∂μ, TraceBound (f x) (c x)) :
    TraceBound (∫ x, f x ∂μ) (∫ x, c x ∂μ) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  intro n u v hu hv
  rw [← frameFunctional_apply, ← (frameFunctional u v).integral_comp_comm hf]
  change ‖∫ x, frameFunctional u v (f x) ∂μ‖ ≤ _
  apply norm_integral_le_of_norm_le hc
  filter_upwards [hbound] with x hx
  rw [frameFunctional_apply, Real.norm_eq_abs]
  exact hx n u v hu hv

/--
The precise assertion is `TraceBound (featureProjection x) 1`.

Use: `chebyshev2.Continuum.densityOperator_traceBound` uses this assertion to establish the
precise assertion is `TraceBound (densityOperator m) (∫ x, |m x|)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_norm`,
`chebyshev2.Continuum.traceBound_rankOne` with the arguments shown in the proof.
-/
theorem featureProjection_traceBound (x : ℝ) : TraceBound (featureProjection x) 1 := by
  simpa only [featureProjection, feature_norm, mul_one] using traceBound_rankOne (feature x) (feature x)

/--
The precise assertion is `TraceBound (featureProjection x - featureProjection y) (2 * ‖feature
x - feature y‖)`.

Use: `chebyshev2.Continuum.measureOperator_transport_integral` uses this assertion to
establish the precise assertion is `TraceBound (measureOperator (μ.map Prod.fst) -
measureOperator (μ.map Prod.snd)) (∫ z, 2 * ‖feature z.1 - feature z.2‖ ∂μ)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_norm`,
`chebyshev2.Continuum.TraceBound.add`, `chebyshev2.Continuum.traceBound_rankOne` with
the arguments shown in the proof.
-/
theorem featureProjection_difference_traceBound (x y : ℝ) :
    TraceBound (featureProjection x - featureProjection y) (2 * ‖feature x - feature y‖) := by
  -- Use the identities/estimates `chebyshev2.Continuum.feature_norm`,
  -- `chebyshev2.Continuum.TraceBound.add`, `chebyshev2.Continuum.traceBound_rankOne`
  -- with the arguments shown in the proof.
  have he : featureProjection x - featureProjection y =
      InnerProductSpace.rankOne ℝ (feature x - feature y) (feature x) +
      InnerProductSpace.rankOne ℝ (feature y) (feature x - feature y) := by
    ext u
    simp [featureProjection]
  rw [he]
  simpa only [feature_norm, mul_one, one_mul, ← two_mul] using
    (traceBound_rankOne (feature x - feature y) (feature x)).add
      (traceBound_rankOne (feature y) (feature x - feature y))

/--
The precise assertion is `TraceBound (densityOperator m) (∫ x, |m x|)`.

Use: `chebyshev2.Continuum.densityOperator_isTraceClass` uses this assertion to establish
the trace-class property: `IsTraceClass (densityOperator m)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `chebyshev2.Continuum.traceBound_integral`,
`chebyshev2.Continuum.densityOperator_integrable`,
`chebyshev2.Continuum.TraceBound.smul` with the arguments shown in the proof.
-/
theorem densityOperator_traceBound {m : ℝ → ℝ} (hm : Integrable m) :
    TraceBound (densityOperator m) (∫ x, |m x|) := by
  apply traceBound_integral (densityOperator_integrable hm) hm.abs
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [mul_one] using (featureProjection_traceBound x).smul (m x))

end
end chebyshev2.Continuum
