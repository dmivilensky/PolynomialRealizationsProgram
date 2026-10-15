import «2610.05164v2».Continuum.BasisTrace
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
Article: 2610.05164v2, Theorem 2.3.
Compactness follows from the closed submodule of compact operators, rather than from an assumed
spectral expansion of the density operator.
Use: `«2610.05164v2».Continuum.densityOperator_isCompact` feeds
`«2610.05164v2».Packing.packed_spectral_distance` (Theorem 2.3, equation (7), for the full fiber
including zero edges).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

/--
Membership in the specified domain/enclosure: `(∫ x, f x ∂μ) ∈ S`.

Use: `«2610.05164v2».Continuum.densityOperator_isCompact` uses this assertion to establish
compactness of the displayed operator: `IsCompactOperator (densityOperator m)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem integral_mem_closedSubmodule {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E)) {f : α → E}
    (hf : Integrable f μ) (hm : ∀ᵐ x ∂μ, f x ∈ S) : (∫ x, f x ∂μ) ∈ S := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let : IsClosed (S : Set E) := hS
  have he : (fun x => S.mkQL (f x)) =ᵐ[μ] (fun _ => 0) := by
    filter_upwards [hm] with x hx
    exact Submodule.Quotient.mk_eq_zero S |>.mpr hx
  have h := S.mkQL.integral_comp_comm hf
  rw [integral_congr_ae he, integral_zero] at h
  exact (Submodule.Quotient.mk_eq_zero S).mp h.symm

/--
Compactness of the displayed operator: `IsCompactOperator (InnerProductSpace.rankOne ℝ a b)`.

Use: `«2610.05164v2».Continuum.featureProjection_isCompact` uses this assertion to establish
compactness of the displayed operator: `IsCompactOperator (featureProjection x)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem rankOne_isCompact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) : IsCompactOperator (InnerProductSpace.rankOne ℝ a b) := by
  have h := isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ b)
  simpa only [InnerProductSpace.rankOne_def', ContinuousLinearMap.coe_comp] using
    h.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ a)

/--
Compactness of the displayed operator: `IsCompactOperator (featureProjection x)`.

Use: `«2610.05164v2».Continuum.densityOperator_isCompact` uses this assertion to establish
compactness of the displayed operator: `IsCompactOperator (densityOperator m)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.rankOne_isCompact` with the
arguments shown in the proof.
-/
theorem featureProjection_isCompact (x : ℝ) : IsCompactOperator (featureProjection x) :=
  rankOne_isCompact _ _

/--
Compactness follows from the closed submodule of compact operators, rather than from an assumed
spectral expansion of the density operator.

Compactness of the displayed operator: `IsCompactOperator (densityOperator m)`.

Use: `«2610.05164v2».Continuum.densitySpectralData` uses this assertion in the displayed
construction of `densitySpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.integral_mem_closedSubmodule`,
`«2610.05164v2».Continuum.densityOperator_integrable`,
`«2610.05164v2».Continuum.featureProjection_isCompact` with the arguments shown in the proof.
-/
theorem densityOperator_isCompact {m : ℝ → ℝ} (hm : Integrable m) : IsCompactOperator (densityOperator m) := by
  let S := compactOperator (RingHom.id ℝ) FeatureSpace FeatureSpace
  apply integral_mem_closedSubmodule S isClosed_setOfPred_isCompactOperator (densityOperator_integrable hm)
  exact Filter.Eventually.of_forall (fun x => (featureProjection_isCompact x).smul (m x))

end
end «2610.05164v2».Continuum
