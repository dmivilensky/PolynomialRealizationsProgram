import «2610.05164v2».Sobolev.Hilbert
import «2610.05164v2».Continuum.TraceClassFeature
import «2610.05164v2».Continuum.TransportExtended
import «2610.05164v2».Continuum.GramSpectrum

/-!
Article: 2610.05164v2, Theorem 3.1.
Lemma 4(ii), on the proved Sobolev space: the actual signed trace-class Bochner integral, its
variation bound, and its basis-independent trace value.
Use: `«2610.05164v2».Sobolev.sobolevDensityOperator_quadratic` feeds
`«2610.05164v2».GroundState.groundParameter_bound` (ground Parameter bound).
Proof chain: `«2610.05164v2».GroundState.groundParameter_variational` — 2610.05164v2, Theorem 3.1;
Sharp ground-state variational principle, ODE, simplicity and intrinsic coordinate.
Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel. The needed form is proved here.
-/
namespace «2610.05164v2».Sobolev
noncomputable section
open «2610.05164v2».Continuum Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
The article's feature operators act on the exact H1 coordinates established in `Hilbert`; no
new copy of the operator or spectral proofs is required.

Use: `«2610.05164v2».Sobolev.sobolevMeasureOperator_form` uses this definition to establish
exact identity `inner ℝ u (sobolevMeasureOperator μ v)=2*∫ x, H1.rep u x*H1.rep v x ∂μ`.

Article: 2610.05164v2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
abbrev sobolevMeasureOperator := measureOperator
/--
Defines `sobolevSignedOperator` of type `` by `traceClassSignedOperator`.

Use: `«2610.05164v2».Sobolev.sobolevSignedOperator_spec` uses this definition to establish
exact identity `sobolevSignedOperator σ=(∫ᵛ x, traceClassFeature x ∂<•σ) ∧
‖sobolevSignedOperator σ‖ ≤ σ.totalVariation.real univ ∧ TraceClassOperator.trace b
(sobolevSignedOperator σ)=σ univ`.

Article: 2610.05164v2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
abbrev sobolevSignedOperator := traceClassSignedOperator
/--
Defines `sobolevDensityOperator` of type `` by `densityOperator`.

Use: `«2610.05164v2».Sobolev.sobolevDensityOperator_form` uses this definition to establish
exact identity `inner ℝ u (sobolevDensityOperator m v)=2*∫ x, m x*H1.rep u x*H1.rep v x`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.groundParameter_variational`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
abbrev sobolevDensityOperator := densityOperator

/--
Exact identity `inner ℝ u (sobolevMeasureOperator μ v)=2*∫ x, H1.rep u x*H1.rep v x ∂μ`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem sobolevMeasureOperator_form (μ : Measure ℝ) [IsFiniteMeasure μ] (u v : H1) :
    inner ℝ u (sobolevMeasureOperator μ v)=2*∫ x, H1.rep u x*H1.rep v x ∂μ := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [measureOperator_inner, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [H1.rep, causalValue]
    have hs : sqrt 2^2=2 := sq_sqrt (by norm_num)
    field_simp
    rw [hs])

/--
Exact identity `inner ℝ u (sobolevDensityOperator m v)=2*∫ x, m x*H1.rep u x*H1.rep v x`.

Use: `«2610.05164v2».Sobolev.sobolevDensityOperator_quadratic` rewrites with this identity to
establish exact identity `inner ℝ u (densityOperator m u)=2*∫ x, m x*H1.rep u x^2`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.groundParameter_variational`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem sobolevDensityOperator_form {m : ℝ → ℝ} (hm : Integrable m) (u v : H1) :
    inner ℝ u (sobolevDensityOperator m v)=2*∫ x, m x*H1.rep u x*H1.rep v x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [densityOperator_inner hm, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [H1.rep, causalValue]
    have hs : sqrt 2^2=2 := sq_sqrt (by norm_num)
    field_simp
    rw [hs])

/--
Exact identity `inner ℝ u (densityOperator m u)=2*∫ x, m x*H1.rep u x^2`.

Use: `«2610.05164v2».GroundState.groundParameter_attained` rewrites with this identity to
establish constructs witnesses with the exact properties `∃ u : H1, ‖u‖=1 ∧ (∫ x, m x*H1.rep u
x^2)=kernelEigenvalue hm hn 0/2`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.groundParameter_variational`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sobolevDensityOperator_quadratic {m : ℝ → ℝ} (hm : Integrable m) (u : H1) :
    inner ℝ u (densityOperator m u)=2*∫ x, m x*H1.rep u x^2 := by
  rw [sobolevDensityOperator_form hm]
  congr 1
  congr 1
  funext x
  ring

/--
The kernel-density adjoint is exactly multiplication by sqrt(2m) on the actual continuous
Sobolev representative, as in Lemma 4(iii).

The stated quantitative bound `evaluationOperator hm hn u =ᵐ[volume] (fun x => sqrt (2*m
x)*H1.rep u x)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem sobolevEvaluation_coe {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (u : H1) : evaluationOperator hm hn u =ᵐ[volume]
      (fun x => sqrt (2*m x)*H1.rep u x) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [evaluationOperator_coe hm hn u] with x hx
  rw [hx]
  simp only [rawEvaluation, H1.rep, causalValue, sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  field_simp

/--
The precise assertion is `nuclearNorm (featureProjection x-featureProjection y)= ENNReal.ofReal
(2*sqrt (1-exp (-2*|x-y|)))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.featureProjection_nuclearNorm_sub` with the arguments shown in the
proof.
-/
theorem sobolevFeature_projector_norm (x y : ℝ) :
    nuclearNorm (featureProjection x-featureProjection y)=
      ENNReal.ofReal (2*sqrt (1-exp (-2*|x-y|))) :=
  featureProjection_nuclearNorm_sub x y

/--
Lemma 4(ii), on the proved Sobolev space: the actual signed trace-class Bochner integral, its
variation bound, and its basis-independent trace value.

Exact identity `sobolevSignedOperator σ=(∫ᵛ x, traceClassFeature x ∂<•σ) ∧
‖sobolevSignedOperator σ‖ ≤ σ.totalVariation.real univ ∧ TraceClassOperator.trace b
(sobolevSignedOperator σ)=σ univ`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.traceClassSignedOperator_eq_integral`,
`«2610.05164v2».Continuum.traceClassSignedOperator_norm`,
`«2610.05164v2».Continuum.traceClassSignedOperator_trace` with the arguments shown in the
proof.
-/
theorem sobolevSignedOperator_spec {ι : Type*} (b : HilbertBasis ι ℝ H1)
    (σ : SignedMeasure ℝ) :
    sobolevSignedOperator σ=(∫ᵛ x, traceClassFeature x ∂<•σ) ∧
      ‖sobolevSignedOperator σ‖ ≤ σ.totalVariation.real univ ∧
      TraceClassOperator.trace b (sobolevSignedOperator σ)=σ univ :=
  ⟨traceClassSignedOperator_eq_integral σ, traceClassSignedOperator_norm σ,
    traceClassSignedOperator_trace b σ⟩

end
end «2610.05164v2».Sobolev
