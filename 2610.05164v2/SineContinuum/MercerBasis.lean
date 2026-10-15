import «2610.05164v2».SineContinuum.KernelConjugacy
import «2610.05164v2».Sobolev.Hilbert
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Article: 2610.05164v2, Lemma 5.
Complete feature-space eigenbasis, constructed from the actual synthesis operator.
Use: `«2610.05164v2».SineContinuum.mercerHilbertBasis_apply` feeds
`«2610.05164v2».SineContinuum.green_mercer_hasSum` (green mercer has Sum).
Proof chain: `«2610.05164v2».SineContinuum.green_mercer_uniform` — 2610.05164v2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion. The needed form is
proved here.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real MeasureTheory
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency true

/--
Defines `sineEvaluation` of type `Continuum.FeatureSpace →L[ℝ] Continuum.FeatureSpace` by
`Continuum.evaluationOperator m_integrable (fun x => (m_positive x).le)`.

Use: `«2610.05164v2».SineContinuum.mercerVector` uses this definition in the displayed
construction of `mercerVector`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.
-/
def sineEvaluation : Continuum.FeatureSpace →L[ℝ] Continuum.FeatureSpace :=
  Continuum.evaluationOperator m_integrable (fun x => (m_positive x).le)

/--
The precise assertion is `Function.Injective sineEvaluation`.

Use: `«2610.05164v2».SineContinuum.mercerVector_orthogonal_eq_bot` uses this assertion to
establish exact identity `(Submodule.span ℝ (range mercerVector))ᗮ=⊥`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sineEvaluation_injective : Function.Injective sineEvaluation := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro u hu
  change u=0
  have hz : sineEvaluation u=0 := hu
  have ha : Continuum.rawEvaluation m u=ᵐ[volume] (fun _ => 0) := by
    have h := Continuum.evaluationOperator_coe m_integrable (fun x => (m_positive x).le) u
    change sineEvaluation u=ᵐ[volume] Continuum.rawEvaluation m u at h
    rw [hz] at h
    exact h.symm.trans (Lp.coeFn_zero ℝ 2 volume)
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous (Continuum.rawEvaluation m u) :=
    m_continuous.sqrt.mul (Continuum.feature_continuous.inner continuous_const)
  have he := hc.ae_eq_iff_eq volume continuous_const |>.mp ha
  have hr : Sobolev.H1.rep u=Sobolev.H1.rep 0 := by
    funext x
    have h := congrFun he x
    rw [Continuum.rawEvaluation,sqrt_m] at h
    have hinner : inner ℝ (Continuum.feature x) u=0 :=
      (mul_eq_zero.mp h).resolve_left (n_positive x).ne'
    simp only [Sobolev.H1.rep,Sobolev.causalValue,hinner,inner_zero_right,mul_zero]
  exact Sobolev.H1.rep_injective hr

/--
Defines `mercerVector` of type `Continuum.FeatureSpace` by `(√(Continuum.referenceEigenvalue
j))⁻¹ • sineEvaluation.adjoint (sineRealHilbertBasis j)`.

Use: `«2610.05164v2».SineContinuum.mercerVector_orthogonal_eq_bot` rewrites with this
definition to establish the identity `(Submodule.span ℝ (range mercerVector))ᗮ=⊥`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.
-/
def mercerVector (j : ℕ) : Continuum.FeatureSpace :=
  (√(Continuum.referenceEigenvalue j))⁻¹ • sineEvaluation.adjoint (sineRealHilbertBasis j)

/--
Exact identity `sineEvaluation (mercerVector j)=√(Continuum.referenceEigenvalue j) •
sineRealHilbertBasis j`.

Use: `«2610.05164v2».SineContinuum.mercerVector_coefficient` uses this identity to establish
the precise assertion is `inner ℝ (mercerVector j) (sineFeature t)=
√(Continuum.referenceEigenvalue j)*upsilon j t`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.sineKernel_basis`,
`«2610.05164v2».Continuum.referenceEigenvalue_pos` with the arguments shown in the proof.
-/
theorem sineEvaluation_mercerVector (j : ℕ) :
    sineEvaluation (mercerVector j)=√(Continuum.referenceEigenvalue j) • sineRealHilbertBasis j := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.sineKernel_basis`,
  -- `«2610.05164v2».Continuum.referenceEigenvalue_pos` with the arguments shown in the proof.
  rw [mercerVector,map_smul]
  have he : sineEvaluation (sineEvaluation.adjoint (sineRealHilbertBasis j))=
      Continuum.referenceEigenvalue j • sineRealHilbertBasis j := sineKernel_basis j
  rw [he,smul_smul]
  congr 1
  have hp := Continuum.referenceEigenvalue_pos j
  apply (inv_mul_eq_iff_eq_mul₀ (sqrt_pos.mpr hp).ne').mpr
  simpa only [pow_two] using (sq_sqrt hp.le).symm

/--
The precise assertion is `Orthonormal ℝ mercerVector`.

Use: `«2610.05164v2».SineContinuum.mercerHilbertBasis` uses this assertion in the displayed
construction of `mercerHilbertBasis`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Separate `i=j` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem mercerVector_orthonormal : Orthonormal ℝ mercerVector := by
  -- Separate `i=j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [orthonormal_iff_ite]
  intro i j
  have h : inner ℝ (sineEvaluation.adjoint (sineRealHilbertBasis i))
      (sineEvaluation.adjoint (sineRealHilbertBasis j))=
      Continuum.referenceEigenvalue j*inner ℝ (sineRealHilbertBasis i) (sineRealHilbertBasis j) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [ContinuousLinearMap.adjoint_adjoint]
    change inner ℝ (sineRealHilbertBasis i) (sineKernel (sineRealHilbertBasis j))=_
    rw [sineKernel_basis,real_inner_smul_right]
  rw [mercerVector,mercerVector,real_inner_smul_left,real_inner_smul_right,h]
  by_cases hij : i=j
  · subst j
    rw [real_inner_self_eq_norm_sq,sineRealHilbertBasis.orthonormal.norm_eq_one]
    simp only [one_pow,mul_one,ite_true]
    have hp := Continuum.referenceEigenvalue_pos i
    have hsq := sq_sqrt hp.le
    field_simp [(sqrt_pos.mpr hp).ne']
    nlinarith
  · rw [sineRealHilbertBasis.orthonormal.inner_eq_zero hij]
    simp [hij]

/--
Exact identity `(Submodule.span ℝ (range mercerVector))ᗮ=⊥`.

Use: `«2610.05164v2».SineContinuum.mercerHilbertBasis` uses this identity in the displayed
construction of `mercerHilbertBasis`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.referenceEigenvalue_pos`,
`«2610.05164v2».SineContinuum.sineEvaluation_injective` with the arguments shown in the proof.
-/
theorem mercerVector_orthogonal_eq_bot :
    (Submodule.span ℝ (range mercerVector))ᗮ=⊥ := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.referenceEigenvalue_pos`,
  -- `«2610.05164v2».SineContinuum.sineEvaluation_injective` with the arguments shown in the
  -- proof.
  apply bot_unique
  intro u hu
  change u=0
  have he : sineEvaluation u=0 := by
    apply sineRealHilbertBasis.repr.injective
    ext j
    simp only [map_zero,lp.coeFn_zero,Pi.zero_apply,sineRealHilbertBasis.repr_apply_apply]
    have h := (Submodule.mem_orthogonal _ _).mp hu (mercerVector j)
      (Submodule.subset_span (mem_range_self j))
    rw [mercerVector,real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (sqrt_pos.mpr
      (Continuum.referenceEigenvalue_pos j)).ne')
  exact sineEvaluation_injective (he.trans (map_zero _).symm)

/--
Complete feature-space eigenbasis, constructed from the actual synthesis operator. Its
completeness uses injectivity of Sobolev evaluation.

Use: `«2610.05164v2».SineContinuum.mercerHilbertBasis_apply` uses this definition to establish
exact identity `mercerHilbertBasis j=mercerVector j`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.
-/
def mercerHilbertBasis : HilbertBasis ℕ ℝ Continuum.FeatureSpace :=
  HilbertBasis.mkOfOrthogonalEqBot mercerVector_orthonormal mercerVector_orthogonal_eq_bot

/--
Exact identity `mercerHilbertBasis j=mercerVector j`.

Use: `«2610.05164v2».SineContinuum.green_mercer_hasSum` rewrites with this identity to
establish the value of a convergent infinite sum: `HasSum (fun j => upsilon j t*upsilon j s/mu
j) (green t s)`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem mercerHilbertBasis_apply (j : ℕ) : mercerHilbertBasis j=mercerVector j :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) j

end
end «2610.05164v2».SineContinuum
