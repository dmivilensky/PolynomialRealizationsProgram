import «2610.05164v2».Continuum.CompactEigenbasis

/-!
Article: 2610.05164v2, Theorem 2.3.
Absolute summability follows from the operator's bound for a complete actual eigenbasis; it is not a
hypothesis attached to a model spectrum.
Use: `«2610.05164v2».Continuum.eigenbasis_abs_summable` feeds
`«2610.05164v2».Continuum.nuclearNorm_eigenbasis` (The dual norm agrees with the sum of absolute
eigenvalues of a compact symmetric trace-class operator).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus. The
needed form is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
A dual trace bound controls every finite sum of absolute eigenvalues.

The stated quantitative bound `(∑ i, |eig i|) ≤ C`.

Use: `«2610.05164v2».Continuum.eigenbasis_abs_summable` uses this bound to establish
summability of the displayed sequence: `Summable (fun i => |eig i|) ∧ (∑' i, |eig i|) ≤ C`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem eigenframe_abs_sum_le {n : ℕ} {T : E →L[ℝ] E} {C : ℝ} (hT : TraceBound T C)
    {u : Fin n → E} (hu : Orthonormal ℝ u) {eig : Fin n → ℝ}
    (he : ∀ i, T (u i) = eig i • u i) : (∑ i, |eig i|) ≤ C := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  classical
  let v : Fin n → E := fun i => if 0 ≤ eig i then u i else -u i
  have hv : Orthonormal ℝ v := hu.orthonormal_of_forall_eq_or_eq_neg (fun i => by
    dsimp [v]
    split_ifs <;> simp)
  have h := hT n u v hu hv
  have hi (i : Fin n) : inner ℝ (u i) (T (v i)) = |eig i| := by
    dsimp [v]
    split_ifs with h
    · rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq, hu.norm_eq_one]
      simp [abs_of_nonneg h]
    · rw [map_neg, he, inner_neg_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hu.norm_eq_one]
      simp [abs_of_neg (lt_of_not_ge h)]
  simp only [hi] at h
  have hn : 0 ≤ ∑ i : Fin n, |eig i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  rw [abs_of_nonneg hn] at h
  exact h

/--
Absolute summability follows from the operator's bound for a complete actual eigenbasis; it is
not a hypothesis attached to a model spectrum.

Summability of the displayed sequence: `Summable (fun i => |eig i|) ∧ (∑' i, |eig i|) ≤ C`.

Use: `«2610.05164v2».Continuum.compact_traceBound_has_summable_eigenbasis` uses this
summability result to construct witnesses satisfying `∃ (ι : Type u)
(b : HilbertBasis ι ℝ E) (eig : ι → ℝ), (∀ i, T (b i) = eig i • b i) ∧ Summable (fun i => |eig
i|) ∧ (∑' i, |eig i|) ≤ C`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.eigenframe_abs_sum_le` with the
arguments shown in the proof.
-/
theorem eigenbasis_abs_summable {ι : Type*} (b : HilbertBasis ι ℝ E) {T : E →L[ℝ] E}
    {eig : ι → ℝ} (he : ∀ i, T (b i) = eig i • b i) {C : ℝ} (hT : TraceBound T C) :
    Summable (fun i => |eig i|) ∧ (∑' i, |eig i|) ≤ C := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.eigenframe_abs_sum_le` with the
  -- arguments shown in the proof.
  classical
  have hb (s : Finset ι) : (∑ i ∈ s, |eig i|) ≤ C := by
    let e := s.equivFin
    let f : Fin s.card → ι := fun i => (e.symm i : ι)
    have hf : Function.Injective f := fun i j h => e.symm.injective (Subtype.ext h)
    have hu := b.orthonormal.comp f hf
    have h := eigenframe_abs_sum_le hT hu (fun i => he (f i))
    change (∑ i : Fin s.card, |eig (f i)|) ≤ C at h
    have hr : (∑ i : Fin s.card, |eig (f i)|) = ∑ i ∈ s, |eig i| := by
      rw [← e.sum_comp (fun i => |eig (f i)|)]
      simp only [f, e.symm_apply_apply]
      have hz : s.attach = (Finset.univ : Finset s) := by ext; simp
      simpa only [hz] using s.sum_attach (fun i => |eig i|)
    rwa [hr] at h
  exact ⟨summable_of_sum_le (fun _ => abs_nonneg _) hb,
    Real.tsum_le_of_sum_le (fun _ => abs_nonneg _) hb⟩

variable [CompleteSpace E]

/--
Constructs witnesses with the exact properties `∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (eig :
ι → ℝ), (∀ i, T (b i) = eig i • b i) ∧ Summable (fun i => |eig i|) ∧ (∑' i, |eig i|) ≤ C`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 2.3.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.exists_compact_eigenbasis`,
`«2610.05164v2».Continuum.eigenbasis_abs_summable` with the arguments shown in the proof.
-/
theorem compact_traceBound_has_summable_eigenbasis (T : E →L[ℝ] E)
    (hc : IsCompactOperator T) (hs : T.IsSymmetric) {C : ℝ} (hT : TraceBound T C) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (eig : ι → ℝ),
      (∀ i, T (b i) = eig i • b i) ∧ Summable (fun i => |eig i|) ∧ (∑' i, |eig i|) ≤ C := by
  obtain ⟨ι,b,eig,he⟩ := exists_compact_eigenbasis T hc hs
  exact ⟨ι,b,eig,he,eigenbasis_abs_summable b he hT⟩

end
end «2610.05164v2».Continuum
