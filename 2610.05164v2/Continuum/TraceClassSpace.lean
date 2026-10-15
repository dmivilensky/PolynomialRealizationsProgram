import «2610.05164v2».Continuum.NuclearAlgebra
import Mathlib.Topology.MetricSpace.Cauchy

/-!
Article: 2610.05164v2, Proposition 3.
Nuclear bounds are closed under operator-norm limits.
Use: `«2610.05164v2».Continuum.TraceBound.of_tendsto` feeds
`«2610.05164v2».Filters.leftTraceClass_derivative` (left Trace Class derivative).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for trace-class
operators. The needed form is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open scoped InnerProductSpace BigOperators
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Constructs `traceClassSubmodule` of type `Submodule ℝ (E →L[ℝ] E)` by the displayed record
fields. Data fields specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».Continuum.TraceClassOperator.addEquivSubmodule` uses this definition in
the displayed construction of `addEquivSubmodule`. Its inputs and component formulas are fixed
by that definition.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def traceClassSubmodule : Submodule ℝ (E →L[ℝ] E) where
  carrier := IsTraceClass
  zero_mem' := IsTraceClass.zero
  add_mem' := IsTraceClass.add
  smul_mem' := fun c _ h => h.smul c

/--
Trace-class operators with their own nuclear-norm topology. The type is separate from the
operator-norm subtype, so the two topologies cannot be silently interchanged.

Use: `«2610.05164v2».Continuum.TraceClassOperator.addEquivSubmodule` uses this record of data
and proof obligations in the displayed construction of `addEquivSubmodule`. Its inputs and
component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
structure TraceClassOperator where
  /-- The underlying continuous linear operator. -/
  val : E →L[ℝ] E
  /-- Proof that the underlying operator is trace class; required to construct an element of this operator space. -/
  property : IsTraceClass val

namespace TraceClassOperator

/--
Constructs `equivSubmodule` of type `TraceClassOperator E ≃ traceClassSubmodule E` by the
displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `«2610.05164v2».Continuum.TraceClassOperator.addEquivSubmodule` uses this definition in
the displayed construction of `addEquivSubmodule`. Its inputs and component formulas are fixed
by that definition.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def equivSubmodule : TraceClassOperator E ≃ traceClassSubmodule E where
  toFun T := ⟨T.val, T.property⟩
  invFun T := ⟨T.val, T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
Supplies the typeclass structure specified by `AddCommGroup (TraceClassOperator E)`. This lets
subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
instance : AddCommGroup (TraceClassOperator E) := (equivSubmodule E).addCommGroup

/--
Defines `addEquivSubmodule` of type `TraceClassOperator E ≃+ traceClassSubmodule E` by `{
equivSubmodule E with map_add' := fun _ _ => rfl }`.

Use: `«2610.05164v2».Continuum.TraceClassOperator.normCore` uses this definition to establish
the precise assertion is `NormedSpace.Core ℝ (TraceClassOperator E) where norm_nonneg _`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def addEquivSubmodule : TraceClassOperator E ≃+ traceClassSubmodule E :=
  { equivSubmodule E with map_add' := fun _ _ => rfl }

/--
Supplies the typeclass structure specified by `Module ℝ (TraceClassOperator E)`. This lets
subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
instance : Module ℝ (TraceClassOperator E) := (addEquivSubmodule E).module ℝ

/--
Supplies the typeclass structure specified by `Norm (TraceClassOperator E)`. This lets
subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
instance : Norm (TraceClassOperator E) := ⟨fun T => (nuclearNorm T.val).toReal⟩

/--
Exact identity `(0 : TraceClassOperator E).val = 0`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem val_zero : (0 : TraceClassOperator E).val = 0 := rfl
/--
Exact identity `(S+T).val = S.val+T.val`.

Use: `«2610.05164v2».Continuum.TraceClassOperator.toOperator` uses this identity in the
displayed construction of `toOperator`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem val_add (S T : TraceClassOperator E) : (S+T).val = S.val+T.val := rfl
/--
Exact identity `(-T).val = -T.val`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem val_neg (T : TraceClassOperator E) : (-T).val = -T.val := rfl
/--
Exact identity `(S-T).val = S.val-T.val`.

Use: `«2610.05164v2».Continuum.traceClassFeature_norm_sub` rewrites with this identity to
establish exact identity `‖traceClassFeature x-traceClassFeature y‖ = 2*sqrt (1-exp
(-2*|x-y|))`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem val_sub (S T : TraceClassOperator E) : (S-T).val = S.val-T.val := rfl
/--
Exact identity `(c • T).val = c • T.val`.

Use: `«2610.05164v2».Continuum.TraceClassOperator.toOperator` uses this identity in the
displayed construction of `toOperator`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem val_smul (c : ℝ) (T : TraceClassOperator E) : (c • T).val = c • T.val := rfl

/--
Exact identity `S = T`.

Use: `«2610.05164v2».Continuum.TraceClassOperator.normCore` uses this identity to establish the
precise assertion is `NormedSpace.Core ℝ (TraceClassOperator E) where norm_nonneg _`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
@[ext] theorem ext {S T : TraceClassOperator E} (h : S.val = T.val) : S = T := by
  cases S
  cases T
  cases h
  rfl

/--
The precise assertion is `NormedSpace.Core ℝ (TraceClassOperator E) where norm_nonneg _`.

Use: `«2610.05164v2».Continuum.TraceClassOperator.toOperator` uses this assertion in the
displayed construction of `toOperator`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.nuclearNorm_toReal_smul`,
`«2610.05164v2».Continuum.nuclearNorm_toReal_add_le`,
`«2610.05164v2».Continuum.nuclearNorm_toReal_eq_zero_iff` with the arguments shown in the
proof.
-/
theorem normCore : NormedSpace.Core ℝ (TraceClassOperator E) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c T := by
    -- Use the identities/estimates `«2610.05164v2».Continuum.nuclearNorm_toReal_smul`,
    -- `«2610.05164v2».Continuum.nuclearNorm_toReal_add_le`,
    -- `«2610.05164v2».Continuum.nuclearNorm_toReal_eq_zero_iff` with the arguments shown in
    -- the proof.
    change (nuclearNorm (c • T.val)).toReal = ‖c‖ * (nuclearNorm T.val).toReal
    rw [nuclearNorm_toReal_smul T.property, Real.norm_eq_abs]
  norm_triangle S T := nuclearNorm_toReal_add_le S.property T.property
  norm_eq_zero_iff T := by
    change (nuclearNorm T.val).toReal = 0 ↔ T = 0
    rw [nuclearNorm_toReal_eq_zero_iff T.property]
    exact ⟨fun h => ext E h, fun h => congrArg val h⟩

/--
Supplies the typeclass structure specified by `NormedAddCommGroup (TraceClassOperator E)`. This
lets subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
instance : NormedAddCommGroup (TraceClassOperator E) := NormedAddCommGroup.ofCore (normCore E)
/--
Supplies the typeclass structure specified by `NormedSpace ℝ (TraceClassOperator E)`. This lets
subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
instance : NormedSpace ℝ (TraceClassOperator E) := NormedSpace.ofCore (normCore E)

/--
Exact identity `‖T‖ = (nuclearNorm T.val).toReal`.

Use: `«2610.05164v2».Continuum.traceClassFeature_norm` rewrites with this identity to establish
exact identity `‖traceClassFeature x‖ = 1`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem norm_def (T : TraceClassOperator E) : ‖T‖ = (nuclearNorm T.val).toReal := rfl

/--
The inclusion is continuous from the nuclear norm to the operator norm.

Use: `«2610.05164v2».Continuum.TraceClassOperator.toOperator_apply` uses this definition to
establish exact identity `toOperator E T = T.val`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def toOperator : TraceClassOperator E →L[ℝ] (E →L[ℝ] E) :=
  LinearMap.mkContinuous
    { toFun := val
      map_add' := val_add E
      map_smul' := val_smul E }
    1 (fun T => by
      change ‖T.val‖ ≤ 1 * (nuclearNorm T.val).toReal
      simpa only [one_mul] using T.property.traceBound.opNorm_le)

/--
Exact identity `toOperator E T = T.val`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem toOperator_apply (T : TraceClassOperator E) : toOperator E T = T.val := rfl

end TraceClassOperator

variable {E}

/--
Nuclear bounds are closed under operator-norm limits. This is the finite-frame lower
semicontinuity used for completeness in the stronger norm.

The precise assertion is `TraceBound S C`.

Use: `«2610.05164v2».Continuum.traceClassDensityOperator_val` uses this assertion to establish
exact identity `(traceClassDensityOperator m).val = densityOperator m`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem TraceBound.of_tendsto {T : ℕ → E →L[ℝ] E} {S : E →L[ℝ] E} {C : ℝ}
    (hlim : Filter.Tendsto T Filter.atTop (nhds S))
    (hbound : ∀ᶠ n in Filter.atTop, TraceBound (T n) C) : TraceBound S C := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  intro k u v hu hv
  have h := ((frameFunctional u v).continuous.tendsto S).comp hlim
  have he : ∀ᶠ n in Filter.atTop, ‖frameFunctional u v (T n)‖ ≤ C := by
    filter_upwards [hbound] with n hn
    simpa only [frameFunctional_apply, Real.norm_eq_abs] using hn k u v hu hv
  simpa only [frameFunctional_apply, Real.norm_eq_abs] using le_of_tendsto h.norm he

namespace TraceClassOperator
variable [CompleteSpace E]

/--
Completeness for the nuclear norm, proved by an operator-norm limit and lower semicontinuity of
every finite-frame pairing.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
instance : CompleteSpace (TraceClassOperator E) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hc := (toOperator E).lipschitzWith.cauchySeq_comp hu
  obtain ⟨T, hT⟩ := cauchySeq_tendsto_of_complete hc
  change Filter.Tendsto (fun n => (u n).val) Filter.atTop (nhds T) at hT
  have hca := Metric.cauchySeq_iff.mp hu
  obtain ⟨N, hN⟩ := hca 1 (by norm_num)
  have hb : TraceBound (T-(u N).val) 1 := by
    apply TraceBound.of_tendsto (hT.sub tendsto_const_nhds)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    apply ((u n-u N).property.traceBound).mono
    change ‖u n-u N‖ ≤ 1
    have he : ‖u n-u N‖ < 1 := by simpa only [dist_eq_norm] using hN n hn N le_rfl
    exact he.le
  have hfinite : IsTraceClass T := by
    have h := hb.isTraceClass.add (u N).property
    simpa only [sub_add_cancel] using h
  let U : TraceClassOperator E := ⟨T, hfinite⟩
  refine ⟨U, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨M, hM⟩ := hca (ε/2) (by positivity)
  refine ⟨M, fun n hn => ?_⟩
  have hb : TraceBound ((u n).val-T) (ε/2) := by
    apply TraceBound.of_tendsto (tendsto_const_nhds.sub hT)
    filter_upwards [Filter.eventually_ge_atTop M] with m hm
    apply ((u n-u m).property.traceBound).mono
    change ‖u n-u m‖ ≤ ε/2
    have he : ‖u n-u m‖ < ε/2 := by simpa only [dist_eq_norm] using hM n hn m hm
    exact he.le
  change dist (u n) U < ε
  rw [dist_eq_norm]
  exact (nuclearNorm_toReal_le hb).trans_lt (by linarith)

end TraceClassOperator

end
end «2610.05164v2».Continuum
