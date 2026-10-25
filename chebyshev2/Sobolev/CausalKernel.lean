import chebyshev2.Continuum.Transport
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Article: chebyshev2, Theorem 3.1.
A continuous candidate representative, in the same actual Hilbert space as the existing feature
family.
Use: `chebyshev2.Sobolev.causalValue_sq_bound` feeds
`chebyshev2.Sobolev.causalValueLp_norm_le` (causal Value Lp norm le).
Proof chain: `chebyshev2.GroundState.GroundWitness.square_identity` — chebyshev2, Theorem 3.1;
Sharp ground-state variational principle, ODE, simplicity and intrinsic coordinate.
Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel. The needed form is proved here.
-/
namespace chebyshev2.Sobolev
noncomputable section
open chebyshev2.Continuum Set MeasureTheory Real
open scoped InnerProductSpace ENNReal

/--
The inverse kernel of d/dx+1 with the L2 boundary condition at -infinity.

Use: `chebyshev2.Sobolev.causalKernel_column_formula` rewrites with this definition to
establish exact identity `causalKernel x t = exp t*(Ici t).indicator (fun x => exp (-x)) x`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
def causalKernel (x : ℝ) : ℝ → ℝ := (Iic x).indicator (fun t => exp (t-x))

/--
The stated quantitative bound `0 ≤ causalKernel x t`.

Use: `chebyshev2.Sobolev.causalMeasure_integral` rewrites with this bound to establish
exact identity `(∫ t, f t ∂causalMeasure x) = ∫ t, causalKernel x t*f t`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem causalKernel_nonneg (x t : ℝ) : 0 ≤ causalKernel x t := by
  by_cases h : t ≤ x
  · rw [causalKernel, indicator_of_mem (show t ∈ Iic x from h)]
    exact (exp_pos _).le
  · simp [causalKernel, h]

/--
The stated quantitative bound `causalKernel x t ≤ 1`.

Use: `chebyshev2.Sobolev.causalMeasure_le_volume` uses this bound to establish the stated
quantitative bound `causalMeasure x ≤ volume`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem causalKernel_le_one (x t : ℝ) : causalKernel x t ≤ 1 := by
  by_cases h : t ≤ x
  · rw [causalKernel, indicator_of_mem (show t ∈ Iic x from h)]
    exact exp_le_one_iff.mpr (sub_nonpos.mpr h)
  · simp [causalKernel, h]

/--
Measurability of the displayed map: `Measurable (causalKernel x)`.

Use: `chebyshev2.Sobolev.causalMeasure_integral` rewrites with this measurability result to
establish exact identity `(∫ t, f t ∂causalMeasure x) = ∫ t, causalKernel x t*f t`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem causalKernel_measurable (x : ℝ) : Measurable (causalKernel x) :=
  (continuous_exp.comp (continuous_id.sub continuous_const)).measurable.indicator measurableSet_Iic

/--
Measurability of the displayed map: `Measurable (fun z : ℝ × ℝ => causalKernel z.1 z.2)`.

Use: `chebyshev2.Sobolev.causalSquare_integrable_prod` uses this measurability result to
establish integrability of the displayed function: `Integrable (fun z : ℝ × ℝ => causalKernel
z.1 z.2*g z.2^2) (volume.prod volume)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Separate `z.2 ≤ z.1` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem causalKernel_joint_measurable : Measurable (fun z : ℝ × ℝ => causalKernel z.1 z.2) := by
  have he : (fun z : ℝ × ℝ => causalKernel z.1 z.2) =
      {z : ℝ × ℝ | z.2 ≤ z.1}.indicator (fun z => exp (z.2-z.1)) := by
    funext z
    by_cases h : z.2 ≤ z.1 <;> simp [causalKernel, h]
  rw [he]
  exact (by fun_prop : Measurable (fun z : ℝ × ℝ => exp (z.2-z.1))).indicator
    (measurableSet_le measurable_snd measurable_fst)

/--
Exact identity `causalKernel x t = exp (-x)*(Iic x).indicator (fun t => exp t) t`.

Use: `chebyshev2.Sobolev.causalKernel_row_integrable` rewrites with this identity to
establish integrability of the displayed function: `Integrable (causalKernel x)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem causalKernel_row_formula (x t : ℝ) :
    causalKernel x t = exp (-x)*(Iic x).indicator (fun t => exp t) t := by by_cases h : t ≤ x <;> simp [causalKernel, h, exp_sub, exp_neg, div_eq_mul_inv, mul_comm]

/--
Integrability of the displayed function: `Integrable (causalKernel x)`.

Use: `chebyshev2.Sobolev.causalMeasure_univ` rewrites with this integrability result to
establish exact identity `causalMeasure x univ = 1`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalKernel_row_formula` with the
arguments shown in the proof.
-/
theorem causalKernel_row_integrable (x : ℝ) : Integrable (causalKernel x) := by
  change Integrable (fun t => causalKernel x t)
  simp_rw [causalKernel_row_formula]
  apply Integrable.const_mul
  have h := (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) x).integrable_indicator
    measurableSet_Iic
  simpa only [one_mul] using h

/--
Exact identity `(∫ t, causalKernel x t) = 1`.

Use: `chebyshev2.Sobolev.causalMeasure_univ` rewrites with this identity to establish exact
identity `causalMeasure x univ = 1`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalKernel_row_formula` with the
arguments shown in the proof.
-/
theorem causalKernel_row_mass (x : ℝ) : (∫ t, causalKernel x t) = 1 := by
  simp_rw [causalKernel_row_formula]
  rw [integral_const_mul, integral_indicator measurableSet_Iic]
  have h := integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) x
  simp only [one_mul, div_one] at h
  rw [h, exp_neg, inv_mul_cancel₀ (exp_ne_zero x)]

/--
Exact identity `causalKernel x t = exp t*(Ici t).indicator (fun x => exp (-x)) x`.

Use: `chebyshev2.Sobolev.causalKernel_column_integrable` rewrites with this identity to
establish integrability of the displayed function: `Integrable (fun x => causalKernel x t)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem causalKernel_column_formula (t x : ℝ) :
    causalKernel x t = exp t*(Ici t).indicator (fun x => exp (-x)) x := by by_cases h : t ≤ x <;> simp [causalKernel, h, exp_sub, exp_neg, div_eq_mul_inv]

/--
Integrability of the displayed function: `Integrable (fun x => causalKernel x t)`.

Use: `chebyshev2.Sobolev.causalSquare_integrable_prod` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun z : ℝ × ℝ => causalKernel
z.1 z.2*g z.2^2) (volume.prod volume)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalKernel_column_formula` with
the arguments shown in the proof.
-/
theorem causalKernel_column_integrable (t : ℝ) : Integrable (fun x => causalKernel x t) := by
  simp_rw [causalKernel_column_formula]
  apply Integrable.const_mul
  apply IntegrableOn.integrable_indicator _ measurableSet_Ici
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
  simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) t

/--
Exact identity `(∫ x, causalKernel x t) = 1`.

Use: `chebyshev2.Sobolev.causalSquare_integrable_prod` rewrites with this identity to
establish integrability of the displayed function: `Integrable (fun z : ℝ × ℝ => causalKernel
z.1 z.2*g z.2^2) (volume.prod volume)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalKernel_column_formula` with
the arguments shown in the proof.
-/
theorem causalKernel_column_mass (t : ℝ) : (∫ x, causalKernel x t) = 1 := by
  simp_rw [causalKernel_column_formula]
  rw [integral_const_mul, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have h := integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) t
  simp only [neg_one_mul, div_neg, div_one, neg_neg] at h
  rw [h, exp_neg, mul_inv_cancel₀ (exp_ne_zero t)]

/--
A continuous candidate representative, in the same actual Hilbert space as the existing feature
family. Its Sobolev interpretation is proved separately.

Use: `chebyshev2.Sobolev.causalValue_integral` rewrites with this definition to establish
exact identity `causalValue g x = ∫ t, causalKernel x t*g t`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.groundParameter_variational`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
def causalValue (g : FeatureSpace) (x : ℝ) : ℝ := (sqrt 2)⁻¹ * inner ℝ (feature x) g

/--
Continuity of the displayed function: `Continuous (causalValue g)`.

Use: `chebyshev2.Sobolev.H1.continuous_rep` uses this continuity result to establish
continuity of the displayed function: `Continuous (rep u)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_continuous` with the
arguments shown in the proof.
-/
theorem causalValue_continuous (g : FeatureSpace) : Continuous (causalValue g) :=
  (feature_continuous.inner continuous_const).const_mul _

/--
Exact identity `causalValue g x = ∫ t, causalKernel x t*g t`.

Use: `chebyshev2.Sobolev.causalValue_sq_bound` rewrites with this identity to establish the
stated quantitative bound `causalValue g x^2 ≤ ∫ t, causalKernel x t*g t^2`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Identify the summands/integrands
on their required domain before replacing the sum or integral.
-/
theorem causalValue_integral (g : FeatureSpace) (x : ℝ) :
    causalValue g x = ∫ t, causalKernel x t*g t := by
  -- Separate `t ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [causalValue, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [feature_coe x] with t ht
  rw [ht]
  change (sqrt 2)⁻¹ * (g t*rawFeature x t) = causalKernel x t*g t
  by_cases h : t ≤ x
  · rw [rawFeature, causalKernel, indicator_of_mem (show t ∈ Iic x from h),
      indicator_of_mem (show t ∈ Iic x from h)]
    field_simp
  · simp [rawFeature, causalKernel, h]

/--
Defines `causalMeasure` of type `Measure ℝ` by `volume.withDensity (fun t => ENNReal.ofReal
(causalKernel x t))`.

Use: `chebyshev2.Sobolev.causalMeasure_integral` rewrites with this definition to establish
exact identity `(∫ t, f t ∂causalMeasure x) = ∫ t, causalKernel x t*f t`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
def causalMeasure (x : ℝ) : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (causalKernel x t))

/--
Exact identity `causalMeasure x univ = 1`.

Use: `chebyshev2.Sobolev.causalValue_sq_bound` rewrites with this identity to establish the
stated quantitative bound `causalValue g x^2 ≤ ∫ t, causalKernel x t*g t^2`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalKernel_row_integrable`,
`chebyshev2.Sobolev.causalKernel_nonneg`, `chebyshev2.Sobolev.causalKernel_row_mass`
with the arguments shown in the proof.
-/
theorem causalMeasure_univ (x : ℝ) : causalMeasure x univ = 1 := by
  rw [causalMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (causalKernel_row_integrable x)
    (Filter.Eventually.of_forall (causalKernel_nonneg x)), causalKernel_row_mass]
  norm_num

/--
Supplies the typeclass structure specified by `IsProbabilityMeasure (causalMeasure x)`. This
lets subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
instance (x : ℝ) : IsProbabilityMeasure (causalMeasure x) := ⟨causalMeasure_univ x⟩

/--
The stated quantitative bound `causalMeasure x ≤ volume`.

Use: `chebyshev2.Sobolev.causalValue_sq_bound` uses this bound to establish the stated
quantitative bound `causalValue g x^2 ≤ ∫ t, causalKernel x t*g t^2`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalKernel_le_one` with the
arguments shown in the proof.
-/
theorem causalMeasure_le_volume (x : ℝ) : causalMeasure x ≤ volume := by
  rw [causalMeasure]
  calc
    _ ≤ volume.withDensity (fun _ => (1 : ℝ≥0∞)) := by
      apply withDensity_mono
      exact Filter.Eventually.of_forall (fun t => by
        simpa using ENNReal.ofReal_le_ofReal (causalKernel_le_one x t))
    _ = volume := withDensity_one

/--
Exact identity `(∫ t, f t ∂causalMeasure x) = ∫ t, causalKernel x t*f t`.

Use: `chebyshev2.Sobolev.causalValue_sq_bound` rewrites with this identity to establish the
stated quantitative bound `causalValue g x^2 ≤ ∫ t, causalKernel x t*g t^2`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalKernel_measurable`,
`chebyshev2.Sobolev.causalKernel_nonneg` with the arguments shown in the proof.
-/
theorem causalMeasure_integral (x : ℝ) (f : ℝ → ℝ) :
    (∫ t, f t ∂causalMeasure x) = ∫ t, causalKernel x t*f t := by
  rw [causalMeasure, integral_withDensity_eq_integral_toReal_smul
    (causalKernel_measurable x).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (causalKernel_nonneg _ _), smul_eq_mul]

/--
The stated quantitative bound `causalValue g x^2 ≤ ∫ t, causalKernel x t*g t^2`.

Use: `chebyshev2.Sobolev.causalValueLp_norm_le` uses this bound to establish the stated
quantitative bound `‖causalValueLp g‖ ≤ ‖g‖`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalMeasure_le_volume`,
`chebyshev2.Continuum.integral_sq_le_mass_mul`,
`chebyshev2.Sobolev.causalMeasure_integral` with the arguments shown in the proof.
-/
theorem causalValue_sq_bound (g : FeatureSpace) (x : ℝ) :
    causalValue g x^2 ≤ ∫ t, causalKernel x t*g t^2 := by
  have hg : MemLp g 2 (causalMeasure x) := (Lp.memLp g).mono_measure (causalMeasure_le_volume x)
  have h := integral_sq_le_mass_mul (causalMeasure x) hg
  rw [causalMeasure_integral, ← causalValue_integral, Measure.real,
    causalMeasure_univ, ENNReal.toReal_one, one_mul, causalMeasure_integral] at h
  exact h

end
end chebyshev2.Sobolev
