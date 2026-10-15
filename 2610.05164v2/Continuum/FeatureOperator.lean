import «2610.05164v2».Continuum.ExponentialFeature
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
Article: 2610.05164v2, Theorem 2.3.
Feature Operator.
Use: `«2610.05164v2».Continuum.densityOperator_positive` feeds
`«2610.05164v2».LocalObstruction.fullPencil_symmetric` (full Pencil symmetric).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Continuity of the displayed function: `Continuous featureProjection`.

Use: `«2610.05164v2».Continuum.densityOperator_integrable` uses this continuity result to
establish integrability of the displayed function: `Integrable (fun x => m x •
featureProjection x)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_continuous` with the
arguments shown in the proof.
-/
theorem featureProjection_continuous : Continuous featureProjection := by
  unfold featureProjection
  exact ((InnerProductSpace.rankOne ℝ (E := FeatureSpace) (F := FeatureSpace)).continuous.comp
    feature_continuous).clm_apply feature_continuous

/--
Exact identity `inner ℝ u (featureProjection x u) = inner ℝ (feature x) u ^ 2`.

Use: `«2610.05164v2».HalfLine.boundaryProjection_positive` rewrites with this identity to
establish the precise assertion is `(boundaryProjection x).IsPositive`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem featureProjection_quadratic (x : ℝ) (u : FeatureSpace) :
    inner ℝ u (featureProjection x u) = inner ℝ (feature x) u ^ 2 := by
  rw [featureProjection, InnerProductSpace.rankOne_apply, real_inner_smul_right, real_inner_comm]
  ring

/--
Exact identity `inner ℝ u (featureProjection x v) = inner ℝ (feature x) u * inner ℝ (feature x)
v`.

Use: `«2610.05164v2».Continuum.densityOperator_inner` rewrites with this identity to establish
exact identity `inner ℝ u (densityOperator m v) = ∫ x, m x * (inner ℝ (feature x) u * inner ℝ
(feature x) v)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem featureProjection_inner (x : ℝ) (u v : FeatureSpace) :
    inner ℝ u (featureProjection x v) = inner ℝ (feature x) u * inner ℝ (feature x) v := by simp [featureProjection, real_inner_smul_right, real_inner_comm, mul_comm]

/--
The stated quantitative bound `‖featureProjection x - featureProjection y‖ ≤ 2 * ‖feature x -
feature y‖`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 2.3.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_norm` with the arguments
shown in the proof.
-/
theorem featureProjection_distance (x y : ℝ) :
    ‖featureProjection x - featureProjection y‖ ≤ 2 * ‖feature x - feature y‖ := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.feature_norm` with the arguments
  -- shown in the proof.
  have he : featureProjection x - featureProjection y =
      InnerProductSpace.rankOne ℝ (feature x - feature y) (feature x) +
      InnerProductSpace.rankOne ℝ (feature y) (feature x - feature y) := by
    ext u
    simp [featureProjection]
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [InnerProductSpace.norm_rankOne, feature_norm, mul_one, one_mul, two_mul]
  exact le_rfl

/--
Defines `densityOperator` of type `FeatureSpace →L[ℝ] FeatureSpace` by `∫ x, m x •
featureProjection x`.

Use: `«2610.05164v2».Continuum.densityOperator_positive` uses this definition to establish the
precise assertion is `(densityOperator m).IsPositive`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.
-/
def densityOperator (m : ℝ → ℝ) : FeatureSpace →L[ℝ] FeatureSpace :=
  ∫ x, m x • featureProjection x

/--
Integrability of the displayed function: `Integrable (fun x => m x • featureProjection x)`.

Use: `«2610.05164v2».Continuum.densityOperator_inner` uses this integrability result to
establish exact identity `inner ℝ u (densityOperator m v) = ∫ x, m x * (inner ℝ (feature x) u *
inner ℝ (feature x) v)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.featureProjection_continuous`,
`«2610.05164v2».Continuum.featureProjection_norm` with the arguments shown in the proof.
-/
theorem densityOperator_integrable {m : ℝ → ℝ} (hm : Integrable m) :
    Integrable (fun x => m x • featureProjection x) := by
  apply hm.norm.mono'
  · exact hm.aestronglyMeasurable.smul featureProjection_continuous.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    simp [norm_smul, featureProjection_norm]

/--
The stated quantitative bound `‖densityOperator m‖ ≤ ∫ x, |m x|`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 2.3.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem densityOperator_norm (m : ℝ → ℝ) :
    ‖densityOperator m‖ ≤ ∫ x, |m x| := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp [norm_smul, featureProjection_norm])

/--
Exact identity `inner ℝ u (densityOperator m v) = ∫ x, m x * (inner ℝ (feature x) u * inner ℝ
(feature x) v)`.

Use: `«2610.05164v2».Continuum.densityOperator_positive` rewrites with this identity to
establish the precise assertion is `(densityOperator m).IsPositive`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem densityOperator_inner {m : ℝ → ℝ} (hm : Integrable m) (u v : FeatureSpace) :
    inner ℝ u (densityOperator m v) =
      ∫ x, m x * (inner ℝ (feature x) u * inner ℝ (feature x) v) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have h := densityOperator_integrable hm
  have he : densityOperator m v = ∫ x, (m x • featureProjection x) v :=
    ContinuousLinearMap.integral_apply h v
  rw [he, ← integral_inner (h.apply_continuousLinearMap v) u]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change inner ℝ u (m x • featureProjection x v) = _
    rw [real_inner_smul_right, featureProjection_inner])

/--
The precise assertion is `(densityOperator m).IsPositive`.

Use: `«2610.05164v2».Continuum.densitySpectralData` uses this assertion in the displayed
construction of `densitySpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem densityOperator_positive {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    (densityOperator m).IsPositive := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  constructor
  · intro u v
    change inner ℝ (densityOperator m u) v = inner ℝ u (densityOperator m v)
    calc
      _ = inner ℝ v (densityOperator m u) := real_inner_comm _ _
      _ = ∫ x, m x * (inner ℝ (feature x) v * inner ℝ (feature x) u) := densityOperator_inner hm v u
      _ = ∫ x, m x * (inner ℝ (feature x) u * inner ℝ (feature x) v) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ = _ := (densityOperator_inner hm u v).symm
  · intro u
    change 0 ≤ inner ℝ (densityOperator m u) u
    rw [real_inner_comm, densityOperator_inner hm]
    apply integral_nonneg
    intro x
    exact mul_nonneg (hn x) (mul_self_nonneg _)

end
end «2610.05164v2».Continuum
