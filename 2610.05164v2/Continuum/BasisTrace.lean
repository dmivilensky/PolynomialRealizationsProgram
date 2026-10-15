import «2610.05164v2».Continuum.NuclearNorm
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: 2610.05164v2, Theorem 3.1.
The trace formula, proved in every Hilbert basis of the actual feature space.
Use: `«2610.05164v2».Continuum.densityOperator_trace` feeds
`«2610.05164v2».Continuum.traceClassDensityOperator_trace` (trace Class Density Operator trace).
Proof chain: `«2610.05164v2».GroundState.groundParameter_variational` — 2610.05164v2, Theorem 3.1;
Sharp ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open MeasureTheory Real Set
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

/--
Supplies the typeclass structure specified by `SecondCountableTopology FeatureSpace`. This lets
subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Theorem 3.1.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
instance : SecondCountableTopology FeatureSpace := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

/--
The precise assertion is `Countable ι`.

Use: `«2610.05164v2».Continuum.densityOperator_hasSum_trace` uses this assertion to establish
the value of a convergent infinite sum: `HasSum (fun i => inner ℝ (b i) (densityOperator m (b
i))) (∫ x, m x)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem orthonormal_countable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SecondCountableTopology E] {ι : Type*} {u : ι → E} (hu : Orthonormal ℝ u) : Countable ι := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (u i) (1 / 2)) (Metric.ball (u j) (1 / 2))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hs := norm_sub_sq_real (u i) (u j)
    rw [hu.norm_eq_one i, hu.norm_eq_one j, hu.inner_eq_zero hij] at hs
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (u i-u j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => Metric.nonempty_ball.mpr (by norm_num))

/--
The value of a convergent infinite sum: `HasSum (fun i => inner ℝ (feature x) (b i)^2) 1`.

Use: `«2610.05164v2».Continuum.densityOperator_hasSum_trace` uses this infinite-sum formula to
establish the value of a convergent infinite sum: `HasSum (fun i => inner ℝ (b i)
(densityOperator m (b i))) (∫ x, m x)`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.groundParameter_variational`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_norm` with the arguments
shown in the proof.
-/
theorem feature_parseval {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace) (x : ℝ) :
    HasSum (fun i => inner ℝ (feature x) (b i)^2) 1 := by
  have h := b.hasSum_inner_mul_inner (feature x) (feature x)
  simpa only [real_inner_comm (b _) (feature x), ← pow_two, real_inner_self_eq_norm_sq,
    feature_norm, one_pow] using h

/--
The trace formula, proved in every Hilbert basis of the actual feature space.

The value of a convergent infinite sum: `HasSum (fun i => inner ℝ (b i) (densityOperator m (b
i))) (∫ x, m x)`.

Use: `«2610.05164v2».Continuum.densityOperator_trace` uses this infinite-sum formula to
establish exact identity `(∑' i, inner ℝ (b i) (densityOperator m (b i))) = ∫ x, m x`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.groundParameter_variational`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem densityOperator_hasSum_trace {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace)
    {m : ℝ → ℝ} (hm : Integrable m) :
    HasSum (fun i => inner ℝ (b i) (densityOperator m (b i))) (∫ x, m x) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let : Countable ι := orthonormal_countable b.orthonormal
  have hsum (x : ℝ) : HasSum (fun i => m x * inner ℝ (feature x) (b i)^2) (m x) := by
    simpa using (feature_parseval b x).mul_left (m x)
  have habs (x : ℝ) : HasSum (fun i => |m x| * inner ℝ (feature x) (b i)^2) |m x| := by
    simpa using (feature_parseval b x).mul_left |m x|
  have hi := hasSum_integral_of_dominated_convergence
    (F := fun i x => m x * inner ℝ (feature x) (b i)^2)
    (f := m) (μ := volume)
    (fun i x => |m x| * inner ℝ (feature x) (b i)^2)
    (fun i => hm.aestronglyMeasurable.mul
      ((feature_continuous.inner continuous_const).pow 2).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall (fun x => by
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
      exact le_rfl))
    (Filter.Eventually.of_forall (fun x => (habs x).summable))
    (by
      have he : (fun x => ∑' i, |m x| * inner ℝ (feature x) (b i)^2) = (fun x => |m x|) := by
        funext x
        exact (habs x).tsum_eq
      rw [he]
      exact hm.abs)
    (Filter.Eventually.of_forall hsum)
  have he (i : ι) : inner ℝ (b i) (densityOperator m (b i)) =
      ∫ x, m x * inner ℝ (feature x) (b i)^2 := by
    rw [densityOperator_inner hm]
    simp only [pow_two]
  convert hi using 1
  funext i
  exact he i

/--
Exact identity `(∑' i, inner ℝ (b i) (densityOperator m (b i))) = ∫ x, m x`.

Use: `«2610.05164v2».Continuum.traceClassDensityOperator_trace` uses this identity to establish
exact identity `TraceClassOperator.trace b (traceClassDensityOperator m) = ∫ x, m x`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.groundParameter_variational`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.densityOperator_hasSum_trace`
with the arguments shown in the proof.
-/
theorem densityOperator_trace {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace)
    {m : ℝ → ℝ} (hm : Integrable m) :
    (∑' i, inner ℝ (b i) (densityOperator m (b i))) = ∫ x, m x :=
  (densityOperator_hasSum_trace b hm).tsum_eq

end
end «2610.05164v2».Continuum
