import «2610.05164v2».Continuum.NuclearSpectrum

/-!
Article: 2610.05164v2, Theorem 2.3.
The dual norm agrees with the sum of absolute eigenvalues of a compact symmetric trace-class
operator.
Use: `«2610.05164v2».Continuum.nuclearNorm_eigenbasis` feeds
`«2610.05164v2».Continuum.exists_positiveSpectralData` (exists positive Spectral Data).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus. The
needed form is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open MeasureTheory Real
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/--
The precise assertion is `TraceBound (∑' i, f i) (∑' i, c i)`.

Use: `«2610.05164v2».Continuum.eigenbasis_traceBound` uses this assertion to establish the
precise assertion is `TraceBound T (∑' i, |eig i|)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem traceBound_tsum {ι : Type*} {f : ι → E →L[ℝ] E} {c : ι → ℝ}
    (hf : Summable f) (hc : Summable c) (hb : ∀ i, TraceBound (f i) (c i)) :
    TraceBound (∑' i, f i) (∑' i, c i) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  intro n u v hu hv
  have hs := (frameFunctional u v).hasSum hf.hasSum
  rw [frameFunctional_apply] at hs
  have hfin (s : Finset ι) : ‖∑ i ∈ s, frameFunctional u v (f i)‖ ≤ ∑ i ∈ s, c i := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [frameFunctional_apply, Real.norm_eq_abs]
    exact hb i n u v hu hv
  exact le_of_tendsto_of_tendsto hs.norm hc.hasSum (Filter.Eventually.of_forall hfin)

/--
Absolute summability of eigenvalues gives convergence of the actual rank-one expansion in
operator norm.

The value of a convergent infinite sum: `HasSum (fun i => eig i • InnerProductSpace.rankOne ℝ
(b i) (b i)) T`.

Use: `«2610.05164v2».Continuum.eigenbasis_traceBound` uses this infinite-sum formula to
establish the precise assertion is `TraceBound T (∑' i, |eig i|)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem eigenbasis_operator_series {ι : Type*} (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] E)
    {eig : ι → ℝ} (he : ∀ i, T (b i) = eig i • b i) (hs : Summable (fun i => |eig i|)) :
    HasSum (fun i => eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) T := by
  -- Prove the summability hf needed for the later infinite-sum manipulations.
  have hf : Summable (fun i => eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) := by
    apply Summable.of_norm
    simpa only [norm_smul, InnerProductSpace.norm_rankOne, b.orthonormal.norm_eq_one,
      mul_one, Real.norm_eq_abs] using hs
  apply hf.hasSum_iff.mpr
  apply ContinuousLinearMap.ext
  intro u
  have h₁ := (ContinuousLinearMap.apply ℝ E u).hasSum hf.hasSum
  have h₂ := T.hasSum (b.hasSum_repr u)
  have he' (i : ι) : T (b.repr u i • b i) =
      (eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) u := by
    rw [map_smul, he, HilbertBasis.repr_apply_apply]
    change inner ℝ (b i) u • eig i • b i = eig i • (inner ℝ (b i) u • b i)
    rw [smul_comm]
  have h₂' : HasSum (fun i => (eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) u) (T u) := by
    simpa only [he'] using h₂
  exact h₁.unique h₂'

/--
The precise assertion is `TraceBound T (∑' i, |eig i|)`.

Use: `«2610.05164v2».Continuum.nuclearNorm_eigenbasis` uses this assertion to establish
summability of the displayed sequence: `Summable (fun i => |eig i|) ∧ nuclearNorm T =
ENNReal.ofReal (∑' i, |eig i|)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.eigenbasis_operator_series`,
`«2610.05164v2».Continuum.traceBound_tsum`, `«2610.05164v2».Continuum.TraceBound.smul` with the
arguments shown in the proof.
-/
theorem eigenbasis_traceBound {ι : Type*} (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] E)
    {eig : ι → ℝ} (he : ∀ i, T (b i) = eig i • b i) (hs : Summable (fun i => |eig i|)) :
    TraceBound T (∑' i, |eig i|) := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.eigenbasis_operator_series`,
  -- `«2610.05164v2».Continuum.traceBound_tsum`, `«2610.05164v2».Continuum.TraceBound.smul`
  -- with the arguments shown in the proof.
  have hf := eigenbasis_operator_series b T he hs
  rw [← hf.tsum_eq]
  apply traceBound_tsum hf.summable hs
  intro i
  simpa only [b.orthonormal.norm_eq_one, mul_one] using
    (traceBound_rankOne (b i) (b i)).smul (eig i)


/--
The dual norm agrees with the sum of absolute eigenvalues of a compact symmetric trace-class
operator.

Summability of the displayed sequence: `Summable (fun i => |eig i|) ∧ nuclearNorm T =
ENNReal.ofReal (∑' i, |eig i|)`.

Use: `«2610.05164v2».Continuum.exists_positiveSpectralData` uses this summability result to
establish the precise assertion is `Nonempty (PositiveSpectralData T)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceBound_of_nuclearNorm_le`,
`«2610.05164v2».Continuum.eigenbasis_abs_summable`,
`«2610.05164v2».Continuum.nuclearNorm_le_of_traceBound` with the arguments shown in the proof.
-/
theorem nuclearNorm_eigenbasis {ι : Type*} (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] E)
    {eig : ι → ℝ} (he : ∀ i, T (b i) = eig i • b i) (hT : IsTraceClass T) :
    Summable (fun i => |eig i|) ∧ nuclearNorm T = ENNReal.ofReal (∑' i, |eig i|) := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.traceBound_of_nuclearNorm_le`,
  -- `«2610.05164v2».Continuum.eigenbasis_abs_summable`,
  -- `«2610.05164v2».Continuum.nuclearNorm_le_of_traceBound` with the arguments shown in the
  -- proof.
  have hn : nuclearNorm T ≠ ⊤ := ne_of_lt hT
  have hbound : TraceBound T (nuclearNorm T).toReal := by
    apply traceBound_of_nuclearNorm_le ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_toReal hn]
  obtain ⟨hs,hle⟩ := eigenbasis_abs_summable b he hbound
  refine ⟨hs, le_antisymm (nuclearNorm_le_of_traceBound (eigenbasis_traceBound b T he hs)) ?_⟩
  rw [← ENNReal.ofReal_toReal hn]
  exact ENNReal.ofReal_le_ofReal hle

end
end «2610.05164v2».Continuum
